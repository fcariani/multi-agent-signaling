; 1. variable declarations

extensions [table ls]

;  the original game has an elegant, if slightly non-modular way of keeping

globals [
  times-right ; how many signaling games were successful
  games-played ; how many signaling games were played
  success?  ; whether we have reached the goal
  all-signals
  all-states
  nearby   ; proximity for eavesdropping
  around-me  ; proximity for movement
  ma-sig-net ; for storing the levelspace model
]


turtles-own [
  my-sender-table ; probabilistic association between states and signals
  my-receiver-table ; probabilistic association between signals and states
  sender ; "on" / "off" variable to designate a sender
  receiver; "on" / "off" variable to designate a receiver
  my-state ; states are internal turtle features (e.g. "I need food")
]

to setup
  ca
  initialize-globals
  populate  ; create the turtles on the board
            ; outputs the initial average tables to the output box
  if print-probabilities? [print-probabilities]
  setup-levelspace
  reset-ticks
end

; 2. setup procedures

to initialize-globals
  set times-right 0
  set games-played 0
  set success? "No"
  set all-signals (range num-signals)
  set all-states (range num-states)
  ; nearby and around-me are similar but
  set nearby moore-offsets eavesdropping-radius  ;one is for eavesdropping
  set around-me moore-offsets movement-aim-radius ;and one is for movement
                                                  ; ma-sig-net is initialized in the levelspace initialization
end

to populate
  create-turtles num-agents [
    setxy random-xcor random-ycor
    set shape "person"
    set sender 0
    set receiver 0
    initialize-tables  ;initialize each turtle's sender and receiver tables
  ]
  reset-ticks
end

to initialize-tables
  ; the sender table assigns to each state the range of signals
  set my-sender-table table:make
  foreach all-states [x -> table:put my-sender-table x all-signals]
  ; the receiver table assigns to each signal the range of states
  set my-receiver-table table:make
  foreach all-signals [x -> table:put my-receiver-table x all-states]
end


; end of setup procedures  (except for "print-probabilities" and "setup-levelspace", below)

; 3. go procedure

to go
  ; stop condition for the model
  if success? != "No" [stop]
  ; non-signaling part of the model
  ask turtles[
    move
    ; at each tick, the state of a turtle changes, randomly for now
    set my-state random num-states
  ]
  ; signaling part of the model
  ;this is the procedure for playing signaling games
  setup-and-play-game
  ; output to the outputbox
  clear-output
  ; print to the output box if the switch is set to on
  if print-probabilities? [print-probabilities]
  check-success ; check whether we were successful
  go-levelspace; runs any updates in the levelspace model
  tick
end

; 4. movement procedures

to wiggle
  ;; turn right then left, so the average is straight ahead
  rt random 90
  lt random 90
end

;;
to move
  ifelse biased-movement?[
    let targets other turtles at-points around-me
    if any? targets [ face min-one-of targets [distance myself]  ]
    forward 1
  ]
  [wiggle
    forward 1]
end


; 5. signaling game procedures

;  first we characterize when games happen and who is involved

to setup-and-play-game
  ; games can only be played on patches with at least two turtles
  ask patches with [count turtles-on self > 1] [
    ask one-of turtles-here[
      set sender 1 ; we designate a turtle as a sender
      play-game ]
  ]
end

; next, we specify how we play the game

to play-game
  set games-played (games-played + 1) ;
  let partner-guess "dummy" ; initializing the partner guess
  let partner one-of other turtles-here   ; choose a partner
                                          ; choose a signal
  let my-signal (one-of (table:get my-sender-table my-state))
  ; have the partner guess
  ask partner [  ; we ask the partner to set their guess
    set receiver 1
    set partner-guess one-of (table:get my-receiver-table my-signal)
  ]
  ; now compare the guess and the initial state
  ; if we got it right...
  ifelse my-state = partner-guess
  [
    ; we add one more successful game to our count
    set times-right (times-right + 1)
    ; next, we each update **all** our tables
    ; first the sender's tables
    update-both-tables my-sender-table my-receiver-table my-state my-signal
    ; next the tables of any other turtles within earshot
    let target-turtles (other turtles-here) ; initialized as the turtles here
    ; but if there are eavesdroppers, it is reset as the turtles in radius
    if eavesdroppers? [set target-turtles (other turtles at-points nearby)]
    ; target turtles are asked to update both their sender and receiver tables
    ask target-turtles [
      update-both-tables my-sender-table my-receiver-table
      ; the "myself" here ought to refer to the sender, I hope it does.
      ([my-state] of myself) my-signal
    ]
  ]
  ; if we got it wrong...
  [ if failure-update? ; if the option to update on failures is on
                       ; we create restricted signal/state lists by removing my-signal
                       ; and my-state
    [
      let restricted-signals remove-item my-signal all-signals
      let restricted-states remove-item my-state all-states
      ; for each of the other signals we add one thing to the urn
      foreach restricted-signals [
        sig ->
        update-both-tables my-sender-table my-receiver-table my-state sig
        ask partner [update-both-tables my-sender-table my-receiver-table
          ([my-state] of myself) my-signal]
      ]
    ]
  ]
  set sender 0
  ask partner [set receiver 0]
end

; 6. some assorted helper procedures and reporters

; for updating tables

to update-both-tables [ s-table r-table state sig ]
  table:put s-table state (lput sig (table:get s-table state))
  table:put r-table sig (lput state (table:get r-table sig))
end

; for characterizing moore neighborhoods (plus the center patch)

to-report moore-offsets [n]
  report [list pxcor pycor] of patches with
  [abs pxcor <= n and abs pycor <= n]
end

; 7. Output reporters

; helper

to-report num-rep [sequence i]  ; this takes a sequence and a value
                                ; and ...
                                ; ... reports the number of occurrences of i in the sequence,
                                ; divided by the length of the sequence
  report (length filter [x ->  x = i] sequence) / (length sequence)
end

; 7.1 Average Reporters

; 7.1.1 Average Receiver Table

; main definition
; this exploits the helper below to compute an average receiver table
; for each signal
to-report average-receiver-table [sig]
  let target-table table:make
  ; that is, we look at each state and store the average degree of
  ; association between the input signal and the state
  foreach all-states [state -> table:put target-table state
    (average-rec-association sig state)]
  report target-table
end

; helper
to-report average-rec-association [sig state]
  ;  asks the receiver tables of the turtles for the frequencies
  ; of state/signal association, then reports averages across turtles
  report precision (mean map [s -> num-rep s state]
    ([table:get my-receiver-table sig] of turtles)) 3
end

; 7.1.2 Average Sender Table

; main definition
; same structure as above but for sender tables instead of receiver tables
; this means also inverting the relative roles of states and signals
to-report average-sender-table [state]
  let target-table table:make
  foreach all-signals [sig -> table:put target-table sig
    (average-send-association sig state)]
  report target-table
end

; helper for main
to-report average-send-association [sig state]
  ; it asks the sender tables of the turtles for the frequencies
  ; of state/signal association,
  ;then averages across turtles, approximating to 3 decimal digits
  report precision (mean map [s -> num-rep s sig]
    ([table:get my-sender-table state] of turtles)) 3
end

; 7.2 Standard Deviation Reporting Proceure

; 7.2.1. Standard Deviation of Receiver

; exploits the helper below to compute a sd receiver table for each signal
to-report sd-receiver-table [sig]
  let target-table table:make
  ; that is, we look at each state and find the sd of the rec association
  ;  between input signal and state
  foreach all-states [state -> table:put target-table state
    (sd-rec-association sig state)]
  report target-table
end

; helper  asks the receiver tables of the turtles for the frequencies
; of state/signal association,
to-report sd-rec-association [sig state]
  ; then computes the sd across turtles, approximating to 3 decimal digits
  report precision (standard-deviation map [s -> num-rep s state]
    ([table:get my-receiver-table sig] of turtles)) 3
end


; 7.2.2. Standard deviation of Sender

; main definition. as above it mirrors 7.2.1 but for sender tables,
; with roles of state and signals reversed
to-report sd-sender-table [state]
  let target-table table:make
  foreach all-signals [sig -> table:put target-table sig
    (sd-send-association sig state)]
  report target-table
end

; helper for main
to-report sd-send-association [sig state]
  report precision (standard-deviation map [s -> num-rep s sig]
    ([table:get my-sender-table state] of turtles)) 3
end

; 8. Expected Success Reporter

; we define an expectation function as in three steps. First

; say I get a signal and I have a target-state in mind...
to-report expected-success-rec [target-state signal]
  ; ... report how likely we are to get the target-state right ...
  ; ... given the average-receiver table.
  report (table:get average-receiver-table signal target-state)
end

; suppose we are in a state, how likely are we to succeed?
; this function computes this based on average-send-table.
to-report expected-success-send [state]
  report sum map [sig ->  ; we take the weighted average of ...
    (expected-success-rec state sig) *  ; ... the average probability
                                        ; ...of success in state sig.
    (table:get average-sender-table state sig) ; ... weighted by how likely
                                               ; we are to send sig in state
  ] all-signals
end

to-report expected-success ; mean of the expected success for each state
  report mean map [sta -> (expected-success-send sta)] all-states
end
; note we are assuming that the states are equiprobable

; 9. Scorekeeping procedures

; 9.1 Output procedures


to print-probabilities
  output-type "average receiver table (+ sd) \n \n"
  foreach n-values num-signals [i -> i] [sig ->
    let target-table (average-receiver-table sig)
    let sd-table (sd-receiver-table sig)
    output-type "signal: " output-print sig
    foreach table:keys target-table [state -> output-type state
      output-type "  " output-type table:get target-table state
      output-type " (" output-type table:get sd-table state output-type ")\n"
    ]
  ]
  output-type "\n*********\n"
  output-type "average sender table (+ sd) "
  output-type "\n\n"
  foreach n-values num-states [i -> i] [sta ->
    let target-table (average-sender-table sta)
    let sd-table (sd-sender-table sta)
    output-type "state: " output-print sta
    foreach table:keys target-table [sig -> output-type sig
      output-type "  " output-type table:get target-table sig
      output-type " (" output-type table:get sd-table sig output-type ")\n"    ]
  ]
end

; 9.2 other reporters and procedures to check the status of the game

to check-success
  if expected-success > (success-threshold / 100) and success? = "No"
  [
    set success? games-played
  ]
end

to-report times-wrong
  report games-played - times-right
end

; 10. dialect identification procedures

; this reporter takes an agent's sender table and coarsens it by
; taking for each state...
to-report coarsen-table [input-table] ; ... the mode of the signals
  let target-table table:make
  foreach (table:keys input-table)
  [x -> table:put target-table x modes (table:get input-table x)]
  report target-table
end

; a dialect is a coarsened table according to the prior procedure

; this reporter outputs a list of dialects and a matching list of how many agents speak them
to-report dialects
  let dialect-list []
  let weight-list []
  ask turtles [
    ifelse not member? (coarsen-table my-sender-table) dialect-list
    [
      set dialect-list lput (coarsen-table my-sender-table) dialect-list
      set weight-list lput 1 weight-list
    ]
    [
      let target-position position (coarsen-table my-sender-table) dialect-list
      let old-value item target-position weight-list
      set weight-list replace-item target-position weight-list (old-value + 1)
    ]
  ]
  let combined-list list dialect-list weight-list
  report combined-list
end

to-report count-dialects
  report length (item 0 dialects)
end

; return an agent dialect

to-report dialect-of [agent];arthur suggested mods but I haven't yet gotten this to work
  report coarsen-table my-sender-table
end

; return true if the two turtles have the same dialect
to-report same-dialect [agent1 agent2]
  report (dialect-of agent1)=(dialect-of agent2)
end



; levelspace procedures

to setup-levelspace
  ls:reset
  ls:create-interactive-models 1 "dialects-as-objects.nlogo"
  set ma-sig-net last ls:models
  ls:assign ls:models dialects-info (item 1 dialects)
  ls:assign ls:models master-tick ticks
  ls:ask ls:models [setup]
end

to go-levelspace
  ls:assign ls:models dialects-info (item 1 dialects)
  ls:assign ls:models master-tick ticks
  ls:ask ls:models [go]
end
@#$#@#$#@
GRAPHICS-WINDOW
410
10
691
292
-1
-1
13.0
1
10
1
1
1
0
1
1
1
-10
10
-10
10
0
0
1
ticks
30.0

BUTTON
60
175
145
208
NIL
setup\n
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
150
175
240
208
NIL
go
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
10
10
190
43
num-states
num-states
2
8
2.0
1
1
NIL
HORIZONTAL

SLIDER
10
50
190
83
num-agents
num-agents
2
300
80.0
1
1
NIL
HORIZONTAL

SLIDER
10
90
190
123
num-signals
num-signals
2
8
2.0
1
1
NIL
HORIZONTAL

MONITOR
10
220
99
265
times wrong
times-wrong
17
1
11

MONITOR
100
220
190
265
times right
times-right
17
1
11

MONITOR
290
220
385
265
success rate
word precision ((times-right / games-played) * 100) 2 \" %\"
2
1
11

OUTPUT
748
10
1076
449
12

MONITOR
10
310
190
355
NIL
expected-success
3
1
11

SWITCH
10
130
190
163
failure-update?
failure-update?
1
1
-1000

MONITOR
195
310
285
355
NIL
success?
17
1
11

SLIDER
10
270
190
303
success-threshold
success-threshold
0
100
80.0
1
1
NIL
HORIZONTAL

SWITCH
750
455
927
488
print-probabilities?
print-probabilities?
0
1
-1000

MONITOR
10
365
190
410
number of dialects
count-dialects
17
1
11

SLIDER
195
50
385
83
eavesdropping-radius
eavesdropping-radius
1
5
3.0
1
1
NIL
HORIZONTAL

SWITCH
195
8
385
41
eavesdroppers?
eavesdroppers?
1
1
-1000

SWITCH
195
90
385
123
biased-movement?
biased-movement?
0
1
-1000

SLIDER
195
130
385
163
movement-aim-radius
movement-aim-radius
1
5
3.0
1
1
NIL
HORIZONTAL

BUTTON
245
175
325
208
NIL
go\n
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

MONITOR
195
220
285
265
times played
games-played
17
1
11

@#$#@#$#@
## WHAT IS IT?

This is a multi-agent generalization of the signaling game model. Signaling games are meant to show that conventional associations between signals and states of the world may emerge as a result of repeated interaction without explicit agreement, and only on the basis of simple updates resulting from prior interactions. 

The present generalization extends the model from the case of two-player signaling games to a whole community of agents. 

## HOW IT WORKS

The agents in the model are people moving around a torus. The torus is generated by an array of 21x21 equal-sized patches. 

In thye default setting, agents move around the world  at random. 

When two or more agents share a patch, a signaling game can happen on that patch. In particular, in such circumstances one of the agents on the patch is designated as "sender" and the other agent is designated as receiver.  

In a signaling game, each agent observes a state. In the standard version of signaling games, states are features of the world (i.e. global variable). In the present version, states are "internal" properties of agents. (We may imagine for instance an agent trying to communicate "I need food" or "I need water".) Neither the difference in interpretation (external vs. internal) nor the difference in structural representation (global vs. owned variable) should make a difference to the relevant emergent patterns. 

## HOW TO USE IT

The model shares two parameters with the standard signaling game model:

- NUM-STATES (how many possible states could agents be in)
- NUM-SIGNALS (how many possible signals are available)

in addition, there are a few new parameters that are special to the present setting;

- NUM-AGENTS: total number of agents.
- SUCCESS-THRESHOLD: on any given run of the model, we can indicate a success-threshold. The model will output to a monitor the number of games it took to hit this threshold (note that the threshold is not a stop condition).on the same patch as a signaling game update on the results of the interaction vs. (ii) any agents nearby update on the results of the interaction.
- FAILURE-UPDATE?: this toggles an option between (i) standard signaling game in which the probabilities of signal association are only updated after a successful interaction vs. (ii) every interaction results in an update).  
- BIASED-MOVEMENT?: biased movement forces the agents to move in a non-random way. 



## THINGS TO NOTICE

Run the model in its default setting and check that signaling conventions tend to emerge in this setting just as they do in the standard signaling model. 

But note that the more agents you add, the slower it takes for a robust conventional association to develop. 

Note also that this can be sped up by allowing agents to eavesdrop on other agents' conversation. 

Also check out the Levelspace addition in which we flip perspective and visualize the dialects the agents speak as objects in their own right. Notice how, as ticks pass, the number of spoken dialects diminishes (see the code of this model for how dialects are identified).

## THINGS TO TRY

Try increasing the MOVEMENT-AIM-RADIUS: under the BIASED-MOVEMENT? option this allows agents to set a target turtle and move towards it. 



## EXTENDING THE MODEL

There is a large variety of alternate movement options we might consider. We would like BIASED-MOVEMENT? to become a chooser. 

Similarly, while the model currently forces one update dynamics, there are many others we might experiment with based on the literature. 

## NETLOGO FEATURES

Etensive use of the table extension to netlogo and initial use of the levelspace extension. 

## RELATED MODELS

The model extends and generalizes 

- Wilensky, U. (2016). NetLogo Signaling Game model. http://ccl.northwestern.edu/netlogo/models/SignalingGame. Center for Connected Learning and Computer-Based Modeling, Northwestern University, Evanston, IL.


## CREDITS AND REFERENCES

For the levelspace extension, see:

- Hjorth, A. Head, B. \& Wilensky, U. (2015). "LevelSpace NetLogo extension". http://ccl.northwestern.edu/levelspace/index.html. Evanston, IL: Center for Connected Learning and Computer Based Modeling, Northwestern University.

@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.0.3
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
<experiments>
  <experiment name="big exp 1" repetitions="200" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="1000000"/>
    <metric>success?</metric>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-signals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="90"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="2"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="exp 2" repetitions="20" runMetricsEveryStep="true">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="100000"/>
    <exitCondition>success? != "No"</exitCondition>
    <metric>success?</metric>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-signals">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="90"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="3"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="exp 3" repetitions="20" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="50000"/>
    <exitCondition>success? != "No"</exitCondition>
    <metric>success?</metric>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-signals">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="90"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="3"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="exp 4" repetitions="20" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="50000"/>
    <exitCondition>success? != "No"</exitCondition>
    <metric>success?</metric>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-signals">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="90"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="3"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="exp 5" repetitions="20" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="10000"/>
    <exitCondition>success? != "No"</exitCondition>
    <metric>success?</metric>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-signals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="90"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="2"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="exp 6" repetitions="20" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="10000"/>
    <exitCondition>success? != "No"</exitCondition>
    <metric>success?</metric>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-signals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="90"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="2"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="exp 7" repetitions="20" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="10000"/>
    <exitCondition>success? != "No"</exitCondition>
    <metric>success?</metric>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-signals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="2"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="exp 8" repetitions="20" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="10000"/>
    <exitCondition>success? != "No"</exitCondition>
    <metric>success?</metric>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="true"/>
    </enumeratedValueSet>
    <steppedValueSet variable="eavesdropping-radius" first="1" step="1" last="5"/>
    <enumeratedValueSet variable="num-signals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="2"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="exp 9" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="10000"/>
    <exitCondition>success? != "No"</exitCondition>
    <metric>success?</metric>
    <metric>length dialects</metric>
    <enumeratedValueSet variable="num-signals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="print-probabilities?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="eavesdropping-radius">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="2"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="new exp 1" repetitions="1000" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="20000"/>
    <metric>success?</metric>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-signals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="print-probabilities?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="eavesdropping-radius">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="movement-aim-radius">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="biased-movement?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="new exp 2" repetitions="20" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="20000"/>
    <metric>success?</metric>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-signals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="print-probabilities?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="eavesdropping-radius">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="movement-aim-radius">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="biased-movement?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="new exp 5" repetitions="20" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="10000"/>
    <metric>count-dialects</metric>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-signals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="print-probabilities?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="eavesdropping-radius">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="movement-aim-radius">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="biased-movement?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="new exp 2c" repetitions="3" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="10000"/>
    <metric>success?</metric>
    <metric>count-dialects</metric>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-signals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="print-probabilities?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="eavesdropping-radius">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="movement-aim-radius">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="biased-movement?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="new exp 4" repetitions="20" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <timeLimit steps="20000"/>
    <metric>success?</metric>
    <metric>count-dialects</metric>
    <enumeratedValueSet variable="eavesdroppers?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-signals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-agents">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="success-threshold">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="print-probabilities?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="failure-update?">
      <value value="false"/>
    </enumeratedValueSet>
    <steppedValueSet variable="eavesdropping-radius" first="1" step="2" last="5"/>
    <enumeratedValueSet variable="movement-aim-radius">
      <value value="3"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-states">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="biased-movement?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
</experiments>
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
1
@#$#@#$#@
