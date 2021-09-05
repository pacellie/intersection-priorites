theory Intersection
  imports
    Main
begin

section\<open>Origin, Direction and Collision\<close>

type_alias Priority = nat

datatype Origin = North | East | South | West

datatype Direction = Left | Straight | Right

datatype Path = Path Origin Direction

fun origin :: "Path \<Rightarrow> Origin" where
  "origin (Path orig _) = orig"

fun direction :: "Path \<Rightarrow> Direction" where
  "direction (Path _ dir) = dir"

fun collide_south :: "Direction \<Rightarrow> Path \<Rightarrow> bool" where
  "collide_south Right (Path West Left) = False"
| "collide_south _ (Path West Right) = False"

| "collide_south Left (Path North Left) = False"
| "collide_south Straight (Path North Straight) = False"
| "collide_south Straight (Path North Right) = False"
| "collide_south Right (Path North Straight) = False"
| "collide_south Right (Path North Right) = False"

| "collide_south Left (Path East Right) = False"
| "collide_south Right (Path East _) = False"

| "collide_south _ _ = True"

fun rotate_origin_clockwise :: "Origin \<Rightarrow> nat \<Rightarrow> Origin" where
  "rotate_origin_clockwise orig 0 = orig"
| "rotate_origin_clockwise North n = rotate_origin_clockwise East (n-1)"
| "rotate_origin_clockwise East n = rotate_origin_clockwise South (n-1)"
| "rotate_origin_clockwise South n = rotate_origin_clockwise West (n-1)"
| "rotate_origin_clockwise West n = rotate_origin_clockwise North (n-1)"

fun rotate_path_clockwise :: "Path \<Rightarrow> nat \<Rightarrow> Path" where
  "rotate_path_clockwise (Path orig dir) n = Path (rotate_origin_clockwise orig n) dir"

(* TODO: Adjust definition to rotate both paths by the left paths counterclockwise distance to south? *)
fun collide :: "Path \<Rightarrow> Path \<Rightarrow> bool" where
  "collide (Path South d) p = collide_south d p"
| "collide (Path East d) p = collide_south d (rotate_path_clockwise p 1)"
| "collide (Path West d) p = collide_south d (rotate_path_clockwise p 3)"
| "collide (Path North d) p = collide_south d (rotate_path_clockwise p 2)"

lemma rotate_path_clockwise_dir[simp]:
  "direction (rotate_path_clockwise p n) = direction p"
  by (cases p) auto

lemma collide_south_south[simp]:
  "South = origin p \<Longrightarrow> collide_south d p"
  by (cases p) simp

lemma rotate_path_clockwise_east_1[simp]:
  "East = origin p \<Longrightarrow> South = origin (rotate_path_clockwise p 1)"
  by (cases p) simp

lemma rotate_path_clockwise_west_3[simp]:
  "West = origin p \<Longrightarrow> South = origin (rotate_path_clockwise p 3)"
  by (cases p) (auto simp: numeral_3_eq_3)

lemma rotate_path_clockwise_north_2[simp]:
  "North = origin p \<Longrightarrow> South = origin (rotate_path_clockwise p 2)"
  by (cases p) (auto simp: numeral_2_eq_2)

lemma collide_id_origin:
  "origin p1 = origin p2 \<Longrightarrow> collide p1 p2"
  using collide.elims(3) by fastforce

lemma collide_rotate:
  "collide p1 p2 = collide (rotate_path_clockwise p1 n) (rotate_path_clockwise p2 n)"
  sorry

lemma collide_com:
  "collide p1 p2 = collide p2 p1"
  sorry

lemma collide_nw_eq_collide_we:
  "collide (Path North d1) (Path South d2) = collide (Path West d1) (Path East d2)"
  sorry

section\<open>Traffic Signs, Rules and Intersections\<close>

datatype TrafficSign =
  PriorityLeft10 \<comment>\<open>1002-10\<close>
| PriorityLeft12 \<comment>\<open>1002-12\<close>
| PriorityLeft13 \<comment>\<open>1002-13\<close>
| PriorityRight20 \<comment>\<open>1002-20\<close>
| PriorityRight22 \<comment>\<open>1002-22\<close>
| PriorityRight23 \<comment>\<open>1002-23\<close>
| PriorityNoTurn11 \<comment>\<open>1002-11\<close>
| PriorityNoTurn14 \<comment>\<open>1002-14\<close>
| PriorityNoTurn21 \<comment>\<open>1002-21\<close>
| PriorityNoTurn24 \<comment>\<open>1002-24\<close>
| Priority \<comment>\<open>306\<close>
| RightOfWay \<comment>\<open>301\<close>
| Yield \<comment>\<open>205\<close>
| Stop \<comment>\<open>206\<close>
| RightBeforeLeft \<comment>\<open>102\<close>
| GreenArrow \<comment>\<open>720\<close>

(* Q: Is there another way to alias a function type *)
datatype Intersection = Intersection "Origin \<Rightarrow> TrafficSign set"
datatype Rules = Rules "Direction \<Rightarrow> TrafficSign \<Rightarrow> Priority"

fun priority :: "Intersection \<Rightarrow> Rules \<Rightarrow> Path \<Rightarrow> Priority" where
  "priority (Intersection i) (Rules r) (Path orig dir) = (
    let signs = i orig in
    let prios = (r dir) ` signs \<union> {0} in
    Max prios
  )"

text\<open>
  Do I even need the notion of a highest priority here?

  If there are three cars/paths A,B,C with priorities 1,1,2 and paths A and B collide,
  then C is allowed to drive first, leaving cars A and B. We only need the notion of a
  highest priority if the priorities of A and B are allowed to change now.

  In other words:
  Does the priority of a car/path depend on another car/path?

  The table does not consider this, but what about right before left?
\<close>
definition wf_intersection_rules :: "Intersection \<Rightarrow> Rules \<Rightarrow> bool" where
  "wf_intersection_rules i r = (\<forall>p q. origin p \<noteq> origin q \<and> priority i r p = priority i r q \<longrightarrow> \<not>collide p q)"

definition wf_intersection_rules_alt :: "Intersection \<Rightarrow> Rules \<Rightarrow> bool" where
  "wf_intersection_rules_alt i r = (\<forall>p q. origin p \<noteq> origin q \<and> collide p q \<longrightarrow> priority i r p \<noteq> priority i r q)"

lemma wf_intersection_rules_alt_eq:
  "wf_intersection_rules i = wf_intersection_rules_alt i"
  using wf_intersection_rules_def wf_intersection_rules_alt_def by blast

section\<open>Examples\<close>

(* TODO: Finish rules; adjust return type to `Priority option` *)
fun rules :: "Direction \<Rightarrow> TrafficSign \<Rightarrow> Priority" where
  "rules Left Priority = 4"
| "rules Straight Priority = 5"
| "rules Right Priority = 4"
| "rules _ Yield = 2"
| "rules _ _ = undefined"

fun intersection :: "Origin \<Rightarrow> TrafficSign set" where
  "intersection North = { Yield }"
| "intersection East = {}"
| "intersection South = { Yield }"
| "intersection West = {}"

lemma counterexample:
  "\<not> wf_intersection_rules (Intersection intersection) (Rules rules)"
proof -
  define p1 where "p1 = Path North Straight"
  define p2 where "p2 = Path South Left"

  have 0: "origin p1 \<noteq> origin p2"
    unfolding p1_def p2_def by simp

  have 1: "collide p1 p2"
    by (simp add: p1_def p2_def)

  have 2: "priority (Intersection intersection) (Rules rules) p1 = 
    priority (Intersection intersection) (Rules rules) p2"
    unfolding p1_def p2_def by simp

  show ?thesis
    using 0 1 2 wf_intersection_rules_def by blast
qed


