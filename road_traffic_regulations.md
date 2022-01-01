## Examples of what we want to prove:
* StVO 9(3):

  A person wishing to ***turn off*** must allow ***oncoming*** vehicles to pass; (...)

* StVO 9(4):

  A person wishing to ***turn left*** must first allow ***oncoming*** traffic intending to turn right to pass. (...)

* Give way sign (205):

  A person operating a vehicle must give way.

* Priority road sign (306):

  This sign indicates priority until the next sign 205 (Give way), 206 (Stop) or 307 (End Priority road). (...)

* StVO 8(1):

  At intersections and junctions vehicles coming from the right have the right of way.  This does not apply: 1. if the right of way is specially regulated by traffic signs (sign 205 (Give way), 206 (Stop), 301 (Right of way), 306 (Priority Road)); or (...)

* StVO 37(1):

  Light signals take precedence over priority rules and traffic signs regulating priority.

## Formalization (Draft)
* Model lanelets as directed edges, model connections between lanelets as nodes.
  ```haskell
  type Direction = Left | Straight | Right
  ```
  Might need to generalize s.t. there are different degrees of `Left`, i.e. 100, 101, 102, ... , 199 leftmost to rightmost left, but all still fall under the over-arching orientation `Left`.

  ```haskell
  type Node = nat
  type Edge = (nat, Direction, nat)
  ```

* Signals and signage.
  ```haskell
  type Signal = Authority | TrafficLight | Sign
  ```
  We also introduce an ordering: `Authority > TrafficLight > Sign`

  ```haskell
  type Light = Green | Amber | Red | RedAmber

  type Authority = (...)
  type TrafficLight = (Light, Direction)
  type Sign = Unsigned | GiveWay | Priority | (...)
  -- TODO: annotate `Priority` with `Direction` (abknickende Vorfahrtsstraße)

  type Signage = Node -> Signal set

  relevant_signal :: Signage -> Node -> Direction -> Signal
  ```
  The signage of a node is applicable for all incoming edges.
  The relevant signal is according to the precedence rules of the StVO which reflects the ordering introduced above.

* Oncoming traffic.
  ```haskell
  type Oncoming = Edge -> Edge -> bool
  ```
  Alternative: Insert more nodes, but leads to different problems.

* Right of.
  ```haskell
  type RightOf = Node -> Node -> bool
  ```
  Needed for `rechts-vor-links`.

```haskell
type RoadTopology = (Node set, Edge set, Oncoming, RightOf)
```

Traffic participants are located on/before a node, do they have the right of way for a given path?

* Participants/Paths and collision.
  ```haskell
  type Path = Edge list
  origin :: Path -> Node -- start a of the first edge (a,d,b) in the path
  direction :: Path -> Direction -- direction d of the first edge (a,d,b) in the path
  collide :: Path -> Path -> bool
  ```
  Two paths collide iff they each contain at least one common node or they contain two edges e1 e2 s.t. oncoming e1 e2 holds.

* Right of way.
  ```haskell
  type PriorityTable = Signal -> Direction -> nat
  has_right_of_way :: RoadTopology -> Signage -> Path -> Path -> bool
  ```
  Alternative:

  Should `has_right_of_way` only be well-defined for two paths which actually collide, i.e. if two paths don't collide in any way does one have the right of way over the other one?
  Or maybe change the return type of has_right_of_way s.t. if p1 and p2 don't collide they both have right of way.

Possible lemmas: (probably lots of well-formed assumptions missing in the following)

* Compatible road topology and signage.
  ```isabelle
  compatible r s iff
    forall p1 p2.
      collide p1 p2 -->
        has_right_of_way r s p1 p2 xor has_right_of_way r s p2 p1
  ```

We could then write a checker which given one fixed priority table checks if a given intersection is compatible by checking for all possible signages all colliding pairs of paths(dynamic signals such as traffic lights and authority signals allow for multiple signages).

This could probably also be used to define compatible r s inductively, i.e. the empty
signage (or no signs at all) should fulfill this statement due to the implicit assumptions about `RightOf`. Maybe one can then add signal under specific preconditions? (TODO)

In the following we assume `compatible r s`.

**Important**:

We can only try to prove the following for one ***specific*** instance of a road topology and signage...

* StVO 9(3), StVO 9(4):

  A person wishing to ***turn off*** must allow ***oncoming*** vehicles to pass; (...)

  A person wishing to ***turn left*** must first allow ***oncoming*** traffic intending to turn right to pass. (...)

  ```
  direction p1 != Straight ==>
    oncoming p2 p1 ==>                 // p2 is the oncoming traffic for p1
      not (has_right_of_way r s p1 p2)

  direction p1 = Left ==>
    oncoming p2 p1 ==>
      direction p2 = Right ==>
        not (has_right_of_way r s p1 p2)
  ```

* StVO 8(1):

  At intersections and junctions vehicles coming from the right have the right of way.  This does not apply: 1. if the right of way is specially regulated by traffic signs (sign 205, 206, 301, 306); or (...)

  ```
  collide p1 p2 ==>
    relevant_signal (origin p1) = Unsigned ==>
      relevant_signal (origin p1) = Unsigned ==>
        right_of (origin p1) (origin p2)  ==>             // p1 is right of p2
          has_right_of_way r s p1 p2
  ```
  Might need to exclude roundabout case here, see StVO 8(1a).

* Right of way sign (301):

  This sign indicates priority at the next intersection or junction.

  One probably also want to prove something along the lines of:

  ```
  collide p1 p2 ==>
    relevant_signal (origin p1) = Priority ==>
      relevant_signal (origin p2) = Yield ==>
        has_right_of_way r s p1 p2
  ```
  And similiar lemmas for other types of signal combinations.

* StVO 36(1), StVO 37(1):

  The signals and instructions given by police officers must be obeyed. They take precedence over all other orders and other rules but do not relieve road users of their obligation to take due care.

  Light signals take precedence over priority rules and traffic signs regulating priority.

  Holds by construction but one can probably prove something along the lines off:
  ```
  S = signage n ==>
    forall s' in S. s > s' ==>
      relevant_singal (signage[n := insert s S]) = s
  ```




## Relevant Rules for Formalization (Draft)

### Precedence
* StVO 36(1):

  The signals and instructions given by police officers must be obeyed. They take precedence over all other orders and other rules but do not relieve road users of their obligation to take due care.

* StVO 37(1):

  Light signals take precedence over priority rules and traffic signs regulating priority.

### Priority
* StVO 9(3):

  A person wishing to turn off must allow oncoming vehicles to pass; (...)

* StVO 9(4):

  A person wishing to turn left must first allow oncoming traffic intending to turn right to pass. Vehicles approaching from opposite directions and both wishing to turn left must do so in front of each other, unless the traffic situation or the design of the intersection requires the vehicles turning left to do so after they have passed each other.

* StVO 8(1):

  At intersections and junctions vehicles coming from the right have the right of way.  This does not apply: 1. if the right of way is specially regulated by traffic signs (sign 205, 206, 301, 306); or (...)

* StVO 8(1a):
  If, at the approach to a roundabout, sign 215 (roundabout) is placed below sign 205 (give way), traffic on the roundabout has the right of way. (...)

* Raik Werner in: Creifelds Rechtswörterbuch Kreisverkehr:
  A roundabout, (...), may be ordered by traffic signs. A right of way does not exist for the traffic circle unless specifically stipulated (StVO 8(1a)).

* LG Saarbrücken BeckRS 2014 06911; Walter in: beck-online. Grosskommentar, Hrsg: Spckhoff Rn. 87:

  Prima facie evidence speaks in favor of a violation of the right of way by the person entering the roundablut if there is a collision between him and the road user driving on the roundabout lane.  * Burmann et al. Straßenverkehrsrecht 37, recital 14: Yellow always means to wait for the next color signal at the stop line.

* StVO 37(2):

  The sequence of traffic light signals is green - amber - red - red and amber (simultaneously) - green. (...) 1. Colours at intersections mean: Green: "Traffic may proceed".  Traffic may turn off in accordance with the rules of section 9; (...) Green arrow: "Traffic may proceed only in the direction of the arrow". A green arrow on the left-hand side after an intersection indicates that oncoming traffic is signalled to stop by a red light and that vehicles wishing to turn left may enter or clear the intersection unhindered in the direction of the green arrow. Amber: "Wait in front of the intersection for the next signal". (...) Red: "Stop in front of the intersection". After stopping, traffic may turn right even if red is showing if a sign with a green arrow on a black background (green arrow) is affixed to the right of the red light. A person operating a vehicle may turn off only from the right-hand lane. When doing so, they must take care not to impede or endanger any other road users, especially pedestrians and vehicles that are allowed to proceed. A black arrow on a red light gives the order to stop, a black arrow on an amber light to wait for the next signal, in both cases only for the direction in which the arrow is pointing. A single-aspect signal with a green arrow allows traffic to turn right when the light for traffic going straight ahead shows red.

* OlG Hamburg VRS 29, 126; OLG Stuttgart NZV 1994, 440:
  The rule 'right before left' also applies to the situation where two traffic participants enter a priority road from the same side and in the same place.

* KG VM 1990, 100:
  If traffic participants from all four directions arrive at the intersection at the same time, the intersection must be crossed carefully and with mutual respect, each being primarily responsible for not endangering the person to whom he has the right of way.

* LG Paderborn NZV 2001, 307:
  If vehicles from three directions meet at the intersection, priority is given to the one which is not being approached from the right.

### Relevant Signs: StVO Annex 1

#### General warning signs
* Intersection or junction (102):

  Intersection of junction with traffic coming from the right having priority.

#### Regulatory signs (Markings: TODO)
* Give way (205):

  A person operating a vehicle must give way.

* Stop and give way (206): A person operating a vehicle must stop and give way.

* Give priority to vehicles from opposite direction (208):

  A person operating a vehicle must give way to oncoming vehicles.

* Roundabout (215):

  (...)

#### Informatory signs (Markings?)
* Right of way (301):

  This sign indicates priority at the next intersection or junction.

* Priority road (306):

  This sign indicates priority until the next sign 205, 206 or 307. (Supplementary signs which indicate the course of the priority route).

* End of priority road (307):

  (...)

* Priority over oncoming vehicles (308):

  A person operating a vehicle has priority over oncoming vehicles.

#### Traffic installations
* (...)

## References: Relevant Traffic Rules StVO
* Section 8 Right of way
* Section 9 Turning off, turing round (U-turns) and reversing
  (3) (4)
* Section 10 Entering the road and moving off
* Section 11 Special traffic situations
  (1) (3)
* Section 19 Level crossings
* Section 26 Pedestrian crossings
  (1)
* Section 36 Signals and instructions given by police officers
* Section 37 Traffic light signals, lane control signals and green arrow
* Section 38 Flashing blue lights and flashing amber lights
* Section 39 Traffic signs
* Section 40 Warning signs
* Section 41 Regulatory signs
* Section 42 Informatory signs
* Section 43 Traffic installations
* Section 46 Exemptions and permission
* Section 49 Administrative offences
* Annexes
  - Annex 1 General and special warning signs
    102, 125, 131, 151
  - Annex 2 Regulatory Signs
    201, 205, 206, 208, 250, 267
    Markings 293+
  - Annex 3 Informatory signs
    301, 306, 307, 308
  - Annex 4 Traffic installations

