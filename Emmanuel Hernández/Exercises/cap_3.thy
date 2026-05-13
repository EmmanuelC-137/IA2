theory cap_3
imports Main
begin

section "Capitulo 3"

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = N int | V vname | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus e1 e2) = 
  (case (asimp_const e1, asimp_const e2) of 
    (N x, N y) \<Rightarrow> N (x+y)
  | (e1, e2) \<Rightarrow> Plus e1 e2)"

text \<open>Exercise 3.1. To show that asimp_const really folds all subexpressions of
the form Plus (N i) (N j), define a function optimal :: aexp \<Rightarrow> bool that
checks that its argument does not contain a subexpression of the form Plus
(N i) (N j). Then prove optimal (asimp_const a).\<close>

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n) = True" |
"optimal (V x) = True" |
"optimal (Plus (N i) (N j)) = False" |
"optimal (Plus e1 e2) = (optimal e1 \<and> optimal e2)"

theorem optimal_asimp_const: "optimal (asimp_const a)"
apply(induction a)
apply(auto split: aexp.split)
done



text \<open>Exercise 3.2. In this exercise we verify constant folding for aexp where we
sumupall constants, even if they are not next to each other. For example, Plus
(N 1) (Plus (V x) (N 2))becomesPlus (V x) (N 3).Thisgoesbeyondasimp.
Define a function full_asimp :: aexp \<Rightarrow> aexp that sums up all constants and
prove its correctness: aval (full_asimp a) s = aval a s.\<close>

fun sum_consts :: "aexp \<Rightarrow> int" where
"sum_consts (N n) = n" |
"sum_consts (V x) = 0" |
"sum_consts (Plus a1 a2) = sum_consts a1 + sum_consts a2"

fun sum_vars :: "aexp \<Rightarrow> aexp option" where
"sum_vars (N n) = None" |
"sum_vars (V x) = Some (V x)" |
"sum_vars (Plus a1 a2) = 
  (case (sum_vars a1, sum_vars a2) of
    (None, None) \<Rightarrow> None
  | (Some e1, None) \<Rightarrow> Some e1
  | (None, Some e2) \<Rightarrow> Some e2
  | (Some e1, Some e2) \<Rightarrow> Some (Plus e1 e2))"

lemma aval_sum_vars: 
  "aval a s = sum_consts a + (case sum_vars a of None \<Rightarrow> 0 | Some a' \<Rightarrow> aval a' s)"
apply(induction a)
apply (auto split: option.split)
done

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp a = 
  (case sum_vars a of
    None \<Rightarrow> N (sum_consts a)
  | Some a' \<Rightarrow> if sum_consts a = 0 then a' else Plus a' (N (sum_consts a)))"

theorem aval_full_asimp: "aval (full_asimp a) s = aval a s"
apply(cases "sum_vars a")
apply(insert aval_sum_vars[of a s])
apply auto
done


text \<open>Exercise 3.3. Substitution is the process of replacing a variable by an ex
pression in an expression. Define a substitution function subst :: vname \<Rightarrow>
aexp \<Rightarrow> aexp \<Rightarrow> aexp such that subst x a e is the result of replacing every
occurrence of variable x by a in e. For example:

3 Case Study: IMP Expressions

subst x (N 3) (Plus (V x ) (V y )) = Plus (N 3) (V y )
Prove the so-called substitution lemma that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
aval (subst x a e) s = aval e (s(x := aval a s)). As a consequence prove
aval a1 s = aval a2 s =\<Rightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s.\<close>

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N n) = N n" |
"subst x a (V y) = (if x = y then a else V y)" |
"subst x a (Plus a1 a2) = Plus (subst x a a1) (subst x a a2)"

lemma subst_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
apply(induction e)
apply auto
done

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
apply(simp add: subst_lemma)
done



text \<open>Exercise 3.4. Take a copy of theory AExp and modify it as follows. Extend
type aexp with a binary constructor Times that represents multiplication.
Modify the definition of the functions aval and asimp accordingly. You can
remove asimp_const. Function asimp should eliminate 0 and 1 from multi
plications as well as evaluate constant subterms. Update all proofs concerned\<close>

datatype aexp_t = N_t int | V_t vname | Plus_t aexp_t aexp_t | Times_t aexp_t aexp_t

fun aval_t :: "aexp_t \<Rightarrow> state \<Rightarrow> val" where
"aval_t (N_t n) s = n" |
"aval_t (V_t x) s = s x" |
"aval_t (Plus_t a1 a2) s = aval_t a1 s + aval_t a2 s" |
"aval_t (Times_t a1 a2) s = aval_t a1 s * aval_t a2 s"

fun plus_t :: "aexp_t \<Rightarrow> aexp_t \<Rightarrow> aexp_t" where
"plus_t (N_t i) (N_t j) = N_t (i+j)" |
"plus_t (N_t i) a = (if i=0 then a else Plus_t (N_t i) a)" |
"plus_t a (N_t i) = (if i=0 then a else Plus_t a (N_t i))" |
"plus_t a1 a2 = Plus_t a1 a2"

fun times_t :: "aexp_t \<Rightarrow> aexp_t \<Rightarrow> aexp_t" where
"times_t (N_t i) (N_t j) = N_t (i*j)" |
"times_t (N_t i) a = (if i=0 then N_t 0 else if i=1 then a else Times_t (N_t i) a)" |
"times_t a (N_t i) = (if i=0 then N_t 0 else if i=1 then a else Times_t a (N_t i))" |
"times_t a1 a2 = Times_t a1 a2"

fun asimp_t :: "aexp_t \<Rightarrow> aexp_t" where
"asimp_t (N_t n) = N_t n" |
"asimp_t (V_t x) = V_t x" |
"asimp_t (Plus_t a1 a2) = plus_t (asimp_t a1) (asimp_t a2)" |
"asimp_t (Times_t a1 a2) = times_t (asimp_t a1) (asimp_t a2)"

lemma aval_plus_t: "aval_t (plus_t a1 a2) s = aval_t a1 s + aval_t a2 s"
apply(induction a1 a2 rule: plus_t.induct)
apply auto
done

lemma aval_times_t: "aval_t (times_t a1 a2) s = aval_t a1 s * aval_t a2 s"
apply(induction a1 a2 rule: times_t.induct)
apply auto
done

lemma aval_asimp_t: "aval_t (asimp_t a) s = aval_t a s"
apply(induction a)
apply (simp_all add: aval_plus_t aval_times_t)
done


text \<open>Exercise 3.5. Define a datatype aexp2 of extended arithmetic expressions
that has, in addition to the constructors of aexp, a constructor for modelling
a C-like post-increment operation x++, where x must be a variable. Define an
evaluation function aval2 :: aexp2 \<Rightarrow> state \<Rightarrow> val \<times> state that returns both
the value of the expression and the new state. The latter is required because
post-increment changes the state.
Extend aexp2 and aval2 with a division operation. Model partiality of
division by changing the return type of aval2 to (val \<times> state) option. In
case of division by 0 let aval2 return None. Division on int is the infix div.\<close>

datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | PostInc vname | Div aexp2 aexp2

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
"aval2 (N2 n) s = Some (n, s)" |
"aval2 (V2 x) s = Some (s x, s)" |
"aval2 (Plus2 a1 a2) s = 
  (case aval2 a1 s of
    None \<Rightarrow> None
  | Some (v1, s') \<Rightarrow> 
      (case aval2 a2 s' of
        None \<Rightarrow> None
      | Some (v2, s'') \<Rightarrow> Some (v1 + v2, s'')))" |
"aval2 (PostInc x) s = Some (s x, s(x := s x + 1))" |
"aval2 (Div a1 a2) s =
  (case aval2 a1 s of
    None \<Rightarrow> None
  | Some (v1, s') \<Rightarrow>
      (case aval2 a2 s' of
        None \<Rightarrow> None
      | Some (v2, s'') \<Rightarrow> if v2 = 0 then None else Some (v1 div v2, s'')))"



text \<open>Exercise 3.6. The following type adds a LET construct to arithmetic ex
pressions:
datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp
The LET constructor introduces a local variable: the value of LET x e1 e2
is the value of e2 in the state where x is bound to the value of e1 in the
original state. Define a function lval :: lexp \<Rightarrow> state \<Rightarrow> int that evaluates
lexp expressions. Remember s(x := i).
Define a conversion inline :: lexp \<Rightarrow> aexp. The expression LET x e1 e2
is inlined by substituting the converted form of e1 for x in the converted form
of e2. See Exercise 3.3 for more on substitution. Prove that inline is correct
w.r.t. evaluation.\<close>

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl n) s = n" |
"lval (Vl x) s = s x" |
"lval (Plusl e1 e2) s = lval e1 s + lval e2 s" |
"lval (LET x e1 e2) s = lval e2 (s(x := lval e1 s))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl n) = N n" |
"inline (Vl x) = V x" |
"inline (Plusl e1 e2) = Plus (inline e1) (inline e2)" |
"inline (LET x e1 e2) = subst x (inline e1) (inline e2)"

lemma inline_correct: "aval (inline e) s = lval e s"
apply(induction e arbitrary: s)
apply (auto simp add: subst_lemma)
done



text \<open>Exercise 3.7. Define functions Eq, Le :: aexp \<Rightarrow> aexp \<Rightarrow> bexp and prove
bval (Eq a1 a2) s = (aval a1 s = aval a2 s) and bval (Le a1 a2) s =
(aval a1 s aval a2 s).\<close>

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)" |
"bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a1 a2 = And (Not (Less a1 a2)) (Not (Less a2 a1))"

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a1 a2 = Not (Less a2 a1)"

lemma bval_Eq: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
apply auto
done

lemma bval_Le: "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
apply auto
done


text \<open>Exercise 3.8. Consider an alternative type of boolean expressions featuring
a conditional:
datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp
First define an evaluation function ifval :: ifexp \<Rightarrow> state \<Rightarrow> bool analogously
to bval. Then define two functions b2ifexp :: bexp \<Rightarrow> ifexp and if2bexp ::
ifexp \<Rightarrow> bexp and prove their correctness, i.e., that they preserve the value
of an expression.\<close>

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 v) s = v" |
"ifval (If b1 b2 b3) s = (if ifval b1 s then ifval b2 s else ifval b3 s)" |
"ifval (Less2 a1 a2) s = (aval a1 s < aval a2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc v) = Bc2 v" |
"b2ifexp (Not b) = If (b2ifexp b) (Bc2 False) (Bc2 True)" |
"b2ifexp (And b1 b2) = If (b2ifexp b1) (b2ifexp b2) (Bc2 False)" |
"b2ifexp (Less a1 a2) = Less2 a1 a2"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 v) = Bc v" |
"if2bexp (If b1 b2 b3) = 
  Not (And (Not (And (if2bexp b1) (if2bexp b2))) 
           (Not (And (Not (if2bexp b1)) (if2bexp b3))))" |
"if2bexp (Less2 a1 a2) = Less a1 a2"

lemma bval_if2bexp: "bval (if2bexp b) s = ifval b s"
apply(induction b)
apply auto
done

lemma ifval_b2ifexp: "ifval (b2ifexp b) s = bval b s"
apply(induction b)
apply auto
done


text \<open>Exercise 3.9. Define a new type of purely boolean expressions
datatype pbexp =
VAR vname | NEG pbexp | AND pbexp pbexp | OR pbexp pbexp
where variables range over values of type bool:
fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x" |
"pbval (NEG b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"
Define a function is_nnf :: pbexp \<Rightarrow> bool that checks whether a boolean
expression is in NNF (negation normal form), i.e., if NEG is only applied
directly to VARs. Also define a function nnf :: pbexp \<Rightarrow> pbexp that converts
a pbexp into NNF by pushing NEG inwards as much as possible. Prove that
nnf preserves the value (pbval (nnf b) s = pbval b s) and returns an NNF
(is_nnf (nnf b)).
An expression is in DNF (disjunctive normal form) if it is in NNF and if
no OR occurs below an AND. Define a corresponding test is_dnf :: pbexp \<Rightarrow>
bool. An NNF can be converted into a DNF in a bottom-up manner. The crit
ical case is the conversion of AND b1 b2. Having converted b1 and b2, apply
distributivity of AND over OR. Define a conversion function dnf_of_nnf ::
pbexp \<Rightarrow> pbexp from NNF to DNF. Prove that your function preserves the
value (pbval (dnf_of_nnf b) s = pbval b s) and converts an NNF into a
DNF (is_nnf b =\<Rightarrow> is_dnf (dnf_of_nnf b)).\<close>

datatype pbexp = VAR vname | NEG pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x" |
"pbval (NEG b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
"is_nnf (NEG (VAR x)) = True" |
"is_nnf (NEG b) = False" |
"is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
"is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2)"

fun push_neg :: "pbexp \<Rightarrow> pbexp"
and nnf :: "pbexp \<Rightarrow> pbexp" where
"push_neg (VAR x) = NEG (VAR x)" |
"push_neg (NEG b) = nnf b" |
"push_neg (AND b1 b2) = OR (push_neg b1) (push_neg b2)" |
"push_neg (OR b1 b2) = AND (push_neg b1) (push_neg b2)" |
"nnf (VAR x) = VAR x" |
"nnf (NEG b) = push_neg b" |
"nnf (AND b1 b2) = AND (nnf b1) (nnf b2)" |
"nnf (OR b1 b2) = OR (nnf b1) (nnf b2)"

lemma pbval_push_neg_nnf:
  "pbval (push_neg b) s = (\<not> pbval b s)"
  "pbval (nnf b) s = pbval b s"
apply(induction b and b rule: push_neg_nnf.induct)
apply auto
done

lemma is_nnf_push_neg_nnf:
  "is_nnf (push_neg b)"
  "is_nnf (nnf b)"
apply(induction b and b rule: push_neg_nnf.induct)
apply auto
done

fun no_or :: "pbexp \<Rightarrow> bool" where
"no_or (VAR x) = True" |
"no_or (NEG (VAR x)) = True" |
"no_or (NEG b) = False" |
"no_or (AND b1 b2) = (no_or b1 \<and> no_or b2)" |
"no_or (OR b1 b2) = False"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf (VAR x) = True" |
"is_dnf (NEG (VAR x)) = True" |
"is_dnf (NEG b) = False" |
"is_dnf (OR b1 b2) = (is_dnf b1 \<and> is_dnf b2)" |
"is_dnf (AND b1 b2) = (no_or b1 \<and> no_or b2)"

fun dist_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"dist_AND (OR b1 b2) b3 = OR (dist_AND b1 b3) (dist_AND b2 b3)" |
"dist_AND b1 (OR b2 b3) = OR (dist_AND b1 b2) (dist_AND b1 b3)" |
"dist_AND b1 b2 = AND b1 b2"

lemma pbval_dist_AND: "pbval (dist_AND b1 b2) s = pbval (AND b1 b2) s"
apply(induction b1 b2 rule: dist_AND.induct)
apply auto
done

lemma no_or_dist_AND: "no_or b1 \<Longrightarrow> no_or b2 \<Longrightarrow> no_or (dist_AND b1 b2)"
apply(induction b1 b2 rule: dist_AND.induct)
apply auto
done

lemma is_dnf_dist_AND: "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (dist_AND b1 b2)"
  apply(induction b1 b2 rule: dist_AND.induct)
  apply (simp_all add: no_or_dist_AND)
  (*sledgehammer*)
  apply (smt (verit) is_dnf.simps(3,4,5,7) no_or.elims(1) pbexp.distinct(9))
done

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR x) = VAR x" |
"dnf_of_nnf (NEG b) = NEG b" |
"dnf_of_nnf (OR b1 b2) = OR (dnf_of_nnf b1) (dnf_of_nnf b2)" |
"dnf_of_nnf (AND b1 b2) = dist_AND (dnf_of_nnf b1) (dnf_of_nnf b2)"

lemma pbval_dnf_of_nnf: "pbval (dnf_of_nnf b) s = pbval b s"
apply(induction b)
apply (simp_all add: pbval_dist_AND)
done

lemma is_nnf_dnf_of_nnf: "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
  apply(induction b)
  apply (simp_all add: is_dnf_dist_AND)
done


text \<open>Exercise 3.10. A stack underflow occurs when executing an ADD instruc
tion on a stack of size less than 2. In our semantics a term exec1 ADD s stk
where length stk < 2 is simply some unspecified value, not an error or ex
ception — HOL does not have those concepts. Modify theory ASM such that
stack underflow is modelled by None and normal execution by Some, i.e.,
the execution functions have return type stack option. Modify all theorems
and proofs accordingly.\<close>

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk = Some (n # stk)" |
"exec1 (LOAD x) s stk = Some (s x # stk)" |
"exec1 ADD _ (j # i # stk) = Some ((i + j) # stk)" |
"exec1 ADD _ _ = None"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some stk" |
"exec (i#is) s stk = (case exec1 i s stk of None \<Rightarrow> None | Some stk' \<Rightarrow> exec is s stk')"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma exec_append[simp]:
  "exec (is1 @ is2) s stk = (case exec is1 s stk of None \<Rightarrow> None | Some stk' \<Rightarrow> exec is2 s stk')"
apply(induction is1 arbitrary: stk)
apply (auto split: option.split)
done

lemma exec_comp: "exec (comp a) s stk = Some (aval a s # stk)"
apply(induction a arbitrary: stk)
apply auto
done


text \<open>Exercise 3.11. This exercise is about a register machine and compiler for
aexp. The machine instructions are
datatype instr = LDI int reg | LD vname reg | ADD reg reg
where type reg is a synonym for nat. Instruction LDI i r loads i into register
r, LD x r loads the value of x into register r, and ADD r1 r2 adds register
r2 to register r1.
Define the execution of an instruction given a state and a register state
(= function from registers to integers); the result is the new register state:
fun exec1 :: instr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int
Define the execution exec of a list of instructions as for the stack machine.
The compiler takes an arithmetic expression a and a register r and pro
duces a list of instructions whose execution places the value of a into r. The
registers > r should be used in a stack-like fashion for intermediate results,
the ones < r should be left alone. Define the compiler and prove it correct:
exec (comp a r) s rs r = aval a s.\<close>

type_synonym reg = nat
datatype instr11 = LDI11 int reg | LD11 vname reg | ADD11 reg reg

fun exec1_11 :: "instr11 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec1_11 (LDI11 i r) s rs = rs(r := i)" |
"exec1_11 (LD11 x r) s rs = rs(r := s x)" |
"exec1_11 (ADD11 r1 r2) s rs = rs(r1 := rs r1 + rs r2)"

fun exec11 :: "instr11 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec11 [] s rs = rs" |
"exec11 (i#is) s rs = exec11 is s (exec1_11 i s rs)"

fun comp11 :: "aexp \<Rightarrow> reg \<Rightarrow> instr11 list" where
"comp11 (N n) r = [LDI11 n r]" |
"comp11 (V x) r = [LD11 x r]" |
"comp11 (Plus e1 e2) r = comp11 e1 r @ comp11 e2 (r+1) @ [ADD11 r (r+1)]"

lemma exec11_append[simp]:
  "exec11 (is1 @ is2) s rs = exec11 is2 s (exec11 is1 s rs)"
apply(induction is1 arbitrary: rs)
apply auto
done

lemma exec11_comp11_less[simp]: "r' < r \<Longrightarrow> exec11 (comp11 a r) s rs r' = rs r'"
apply(induction a arbitrary: r rs)
apply auto
done

lemma exec11_comp11_eq[simp]: "exec11 (comp11 a r) s rs r = aval a s"
apply(induction a arbitrary: r rs)
apply auto
done


text \<open>Exercise 3.12. This is a variation on the previous exercise. Let the instruc
tion set be
datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg
All instructions refer implicitly to register 0 as the source (MV0) or target
(all others). Define a compiler pretty much as explained above except that
the compiled code leaves the value of the expression in register 0. Prove that
exec (comp a r) s rs 0 = aval a s.\<close>

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

fun exec1_0 :: "instr0 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec1_0 (LDI0 i) s rs = rs(0 := i)" |
"exec1_0 (LD0 x) s rs = rs(0 := s x)" |
"exec1_0 (MV0 r) s rs = rs(r := rs 0)" |
"exec1_0 (ADD0 r) s rs = rs(0 := rs 0 + rs r)"

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec0 [] s rs = rs" |
"exec0 (i#is) s rs = exec0 is s (exec1_0 i s rs)"

fun comp0 :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"comp0 (N n) r = [LDI0 n]" |
"comp0 (V x) r = [LD0 x]" |
"comp0 (Plus e1 e2) r = comp0 e1 r @ [MV0 r] @ comp0 e2 (r+1) @ [ADD0 r]"

lemma exec0_append[simp]:
  "exec0 (is1 @ is2) s rs = exec0 is2 s (exec0 is1 s rs)"
apply(induction is1 arbitrary: rs)
apply auto
done

lemma exec0_comp0_less[simp]: "0 < r' \<Longrightarrow> r' < r \<Longrightarrow> exec0 (comp0 a r) s rs r' = rs r'"
apply(induction a arbitrary: r rs)
apply auto
done

lemma exec0_comp0_eq[simp]: "0 < r \<Longrightarrow> exec0 (comp0 a r) s rs 0 = aval a s"
apply(induction a arbitrary: r rs)
apply auto
done

end