theory Intersection
  imports
    Main
begin

section\<open>Origin, Direction and Collision\<close>

type_synonym Priority = nat

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

definition rotate_path_clockwise :: "Path \<Rightarrow> nat \<Rightarrow> Path" where
  "rotate_path_clockwise path n = 
    (case path of (Path orig dir) \<Rightarrow> Path (rotate_origin_clockwise orig n) dir)"

lemma rotate_path_clockwise_simps:
  "rotate_path_clockwise (Path orig path) 0 = Path orig path"
  "rotate_path_clockwise (Path North path) (Suc 0) = Path East path"
  "rotate_path_clockwise (Path East path) (Suc 0) = Path South path"
  "rotate_path_clockwise (Path South path) (Suc 0) = Path West path"
  "rotate_path_clockwise (Path West path) (Suc 0) = Path North path"
  "rotate_path_clockwise (Path North path) 2 = Path South path"
  "rotate_path_clockwise (Path East path) 2 = Path West path"
  "rotate_path_clockwise (Path South path) 2 = Path North path"
  "rotate_path_clockwise (Path West path) 2 = Path East path"
  "rotate_path_clockwise (Path North path) 3 = Path West path"
  "rotate_path_clockwise (Path East path) 3 = Path North path"
  "rotate_path_clockwise (Path South path) 3 = Path East path"
  "rotate_path_clockwise (Path West path) 3 = Path South path"
  unfolding rotate_path_clockwise_def by (auto simp: numeral_2_eq_2 numeral_3_eq_3)

fun turns :: "Origin \<Rightarrow> nat" where
  "turns South = 0"
| "turns East = 1"
| "turns North = 2"
| "turns West = 3"

fun collide :: "Path \<Rightarrow> Path \<Rightarrow> bool" where
  "collide (Path orig dir) p = collide_south dir (rotate_path_clockwise p (turns orig))"

lemma rotate_origin_clockwise_add:
  "rotate_origin_clockwise (rotate_origin_clockwise orig m) n = rotate_origin_clockwise orig (m + n)"
  by (induction orig m rule: rotate_origin_clockwise.induct) auto

lemma rotate_path_clockwise_add:
  "rotate_path_clockwise (rotate_path_clockwise p m) n = rotate_path_clockwise p (m + n)"
  using rotate_origin_clockwise_add unfolding rotate_path_clockwise_def by (cases p) simp

lemma rotate_origin_clockwise_mod:
  "rotate_origin_clockwise orig n = rotate_origin_clockwise orig (n mod 4)"
  apply (induction n arbitrary: orig)
   apply (auto simp: mod_Suc)
  subgoal premises prems for _ x
    using prems by (cases x) (auto simp: numeral_3_eq_3) 
  subgoal premises prems for _ x
    using prems by (cases x) auto
  done

lemma rotate_path_clockwise_mod:
  "rotate_path_clockwise p n = rotate_path_clockwise p (n mod 4)"
  using rotate_origin_clockwise_mod rotate_path_clockwise_def by (cases p) simp

lemma collide_id_origin:
  "origin p1 = origin p2 \<Longrightarrow> collide p1 p2"
  apply (cases p1; cases p2)
  apply (auto)
  subgoal premises prems for _ x _
    using prems rotate_path_clockwise_def by (cases x) (auto simp: numeral_2_eq_2 numeral_3_eq_3)
  done

lemma collide_rotate0:
  "collide p1 p2 = collide (rotate_path_clockwise p1 0) (rotate_path_clockwise p2 0)"
  using rotate_path_clockwise_def by (cases p1; cases p2) simp

lemma collide_rotate1:
  "collide p1 p2 = collide (rotate_path_clockwise p1 1) (rotate_path_clockwise p2 1)"
  apply (cases p1; cases p2)
  apply (auto simp: rotate_origin_clockwise_add)
  subgoal premises prems for a b c d
    using prems rotate_path_clockwise_def
    apply (cases a; cases b; cases c; cases d)
                        apply (auto simp: numeral_2_eq_2 numeral_3_eq_3)
    done
  subgoal premises prems for a b c d
    using prems rotate_path_clockwise_def
    apply (cases a; cases b; cases c; cases d)
                        apply (auto simp: numeral_2_eq_2 numeral_3_eq_3)
    done
  done

lemma collide_rotate2:
  "collide p1 p2 = collide (rotate_path_clockwise p1 2) (rotate_path_clockwise p2 2)"
  apply (cases p1; cases p2)
  apply (auto simp: rotate_origin_clockwise_add)
  subgoal premises prems for a b c d
    using prems rotate_path_clockwise_def
    apply (cases a; cases b; cases c; cases d)
                        apply (auto simp: numeral_2_eq_2 numeral_3_eq_3)
    done
  subgoal premises prems for a b c d
    using prems rotate_path_clockwise_def
    apply (cases a; cases b; cases c; cases d)
                        apply (auto simp: numeral_2_eq_2 numeral_3_eq_3)
    done
  done

lemma collide_rotate3:
  "collide p1 p2 = collide (rotate_path_clockwise p1 3) (rotate_path_clockwise p2 3)"
  apply (cases p1; cases p2)
  apply (auto simp: rotate_origin_clockwise_add)
  subgoal premises prems for a b c d
    using prems rotate_path_clockwise_def
    apply (cases a; cases b; cases c; cases d)
                        apply (auto simp: numeral_2_eq_2 numeral_3_eq_3)
    done
  subgoal premises prems for a b c d
    using prems rotate_path_clockwise_def
    apply (cases a; cases b; cases c; cases d)
                        apply (auto simp: numeral_2_eq_2 numeral_3_eq_3)
    done
  done

lemmas collide_rotate0123 = collide_rotate0 collide_rotate1 collide_rotate2 collide_rotate3

lemma collide_rotate_mod4:
  "collide p1 p2 = collide (rotate_path_clockwise p1 (n mod 4)) (rotate_path_clockwise p2 (n mod 4))"
proof -
  have "\<And>m::nat. m < 4 \<Longrightarrow> collide p1 p2 = collide (rotate_path_clockwise p1 m) (rotate_path_clockwise p2 m)"
  proof -
    fix m :: nat
    assume "m < 4"
    then consider (A) "m = 0" | (B) "m = 1" | (C) "m = 2" | (D) "m = 3"
      by force
    thus "collide p1 p2 = collide (rotate_path_clockwise p1 m) (rotate_path_clockwise p2 m)"
      using collide_rotate0123 by auto
  qed
  thus ?thesis
    by simp
qed

lemma collide_rotate:
  "collide p1 p2 = collide (rotate_path_clockwise p1 n) (rotate_path_clockwise p2 n)"
  using collide_rotate_mod4 rotate_path_clockwise_mod by auto

lemma collide_com:
  "collide p1 p2 = collide p2 p1"
  apply (cases p1; cases p2)
  apply (auto)
  subgoal premises prems for a b c d
    using prems rotate_path_clockwise_def
    apply (cases a; cases b;  cases c; cases d)
                        apply (auto simp: numeral_2_eq_2 numeral_3_eq_3)
    done
  subgoal premises prems for a b c d
    using prems rotate_path_clockwise_def
    apply (cases a; cases b;  cases c; cases d)
                        apply (auto simp: numeral_2_eq_2 numeral_3_eq_3)
    done
  done

lemma collide_nw_eq_collide_we:
  "collide (Path North d1) (Path South d2) = collide (Path West d1) (Path East d2)"
  using rotate_path_clockwise_def by (cases d1; cases d2) (auto simp: numeral_2_eq_2 numeral_3_eq_3)

(* TODO: Flipping S-W S-E Symmetry *)

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

type_synonym Intersection = "Origin \<Rightarrow> TrafficSign set"
type_synonym Rules = "Direction \<Rightarrow> TrafficSign \<Rightarrow> Priority"

fun priority :: "Intersection \<Rightarrow> Rules \<Rightarrow> Path \<Rightarrow> Priority" where
  "priority intersection rules (Path orig dir) = (
    let signs = intersection orig in
    let prios = (rules dir) ` signs \<union> {0} in
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

section\<open>Examples\<close>

fun intersection :: "Origin \<Rightarrow> TrafficSign set" where
  "intersection North = { Priority }"
| "intersection East = { Yield }"
| "intersection South = { Priority }"
| "intersection West = { Yield }"

(* TODO: Finish rules; adjust return type to `Priority option` *)
fun current_rules :: "Direction \<Rightarrow> TrafficSign \<Rightarrow> Priority" where
  "current_rules Left Priority = 4"
| "current_rules Straight Priority = 5"
| "current_rules Right Priority = 4"
| "current_rules Left Yield = 2"
| "current_rules Straight Yield = 2"
| "current_rules Right Yield = 2"
| "current_rules _ _ = undefined"

lemma counterexample:
  "\<not> wf_intersection_rules intersection current_rules"
proof -
  define p1 where "p1 = Path East Straight"
  define p2 where "p2 = Path West Left"

  have 0: "origin p1 \<noteq> origin p2"
    unfolding p1_def p2_def by simp

  have 1: "collide p1 p2"
    using rotate_path_clockwise_def by (simp add: p1_def p2_def)

  have 2: "priority intersection current_rules p1 = 
    priority intersection current_rules p2"
    unfolding p1_def p2_def by simp

  show ?thesis
    using 0 1 2 wf_intersection_rules_def by blast
qed

fun adjusted_rules :: "Direction \<Rightarrow> TrafficSign \<Rightarrow> Priority" where
  "adjusted_rules Left Priority = 4"
| "adjusted_rules Straight Priority = 5"
| "adjusted_rules Right Priority = 5"
| "adjusted_rules Left Yield = 1"
| "adjusted_rules Straight Yield = 2"
| "adjusted_rules Right Yield = 2"
| "adjusted_rules _ _ = undefined"

lemma wf_adjusted_intersection_rules:
  "wf_intersection_rules intersection adjusted_rules"
  unfolding wf_intersection_rules_def
proof (standard; standard; standard)
  fix p q
  assume asm: "origin p \<noteq> origin q \<and> priority intersection adjusted_rules p = priority intersection adjusted_rules q"

  obtain origin_p path_p where p_def: "p = Path origin_p path_p"
    using Path.exhaust by blast
  obtain origin_q path_q where q_def: "q = Path origin_q path_q"
    using Path.exhaust by blast

  show "\<not> collide p q"
    unfolding p_def q_def
    apply (cases origin_p; cases origin_q; cases path_p; cases path_q)
    using asm p_def q_def
                        apply (auto simp: rotate_path_clockwise_simps)
    done
qed



