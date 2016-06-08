theory BasicAlgebra
imports Main
begin

(* this is just me messing around reminding myself of basic Isabelle syntax *)

locale group =
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 50)
  and id :: "'a"
  and inv :: "'a \<Rightarrow> 'a" 
  assumes lmultinv [simp] : "(inv x) \<cdot> x = id"
  and rmultinv [simp] : "x \<cdot> (inv x) = id"
  and lmultid [simp] : "id \<cdot> x = x"
  and rmultid [simp] : "x \<cdot> id = x"
  and assoc : "(x \<cdot> (y \<cdot> z)) = ((x \<cdot> y) \<cdot> z)"
  
lemma (in group) unique_id: 
  fixes id' :: "'a"
  assumes "\<And> x. id' \<cdot> x = x" (* why do we have to quantify the x here? *)
  and "\<And> x. x \<cdot> id' = x" 
  shows "id = id'"
  proof -
  have "id' \<cdot> id = id" using assms by blast
  moreover have "id' \<cdot> id = id'" by simp
  ultimately show ?thesis by simp
  qed
  
  
thm group_def

datatype Nat = Zero | Succ Nat

fun addy :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" (infixl "\<oplus>" 50) where
"addy Zero n = n"|
"addy (Succ n) m = Succ (addy n m)"

fun subby :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
"subby Zero i = Zero" |
"subby i Zero = i" |
"subby (Succ i) (Succ j) = subby i j"

fun gt :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
"gt (Succ i) Zero = True" |
"gt Zero i = False" |
"gt (Succ i) (Succ j) = gt i j"

fun lt :: "Nat \<Rightarrow> Nat \<Rightarrow> bool" where
"lt i Zero = False" |
"lt Zero (Succ i) = True" |
"lt (Succ i) (Succ j) = lt i j"

theorem addy_assoc : "n \<oplus> (m \<oplus> l) = ((n \<oplus> m) \<oplus> l)"
proof (induction n)
case Zero
 show ?case by simp
case (Succ n)
 thus ?case by simp
qed

lemma [simp]: "n \<oplus> (Succ m) = Succ (n \<oplus> m)"
proof (induction n arbitrary: m)
case Zero
  show ?case by simp
case (Succ n)
  thus ?case by simp
qed

datatype Integer = IZ | IPos Nat | INeg Nat

fun iaddy :: "Integer \<Rightarrow> Integer \<Rightarrow> Integer" (infixl "\<bullet>" 50) where
"iaddy IZ i = i" |
"iaddy i IZ = i" |
"iaddy (IPos i) (IPos j) = IPos (Succ (i \<oplus> j))"|
"iaddy (INeg i) (INeg j) = INeg (Succ (i \<oplus> j))"|
"iaddy (IPos i) (INeg j) = (if (gt i j) 
  then (IPos (subby i (Succ j))) else 
    (if (lt i j) then (INeg (subby j (Succ i))) else IZ))"|
"iaddy (INeg i) (IPos j) = (if (gt i j) 
  then (INeg (subby i (Succ j))) else 
    (if (lt i j) then (IPos (subby j (Succ i))) else IZ))"

lemma iassoc : "(m \<bullet> (n \<bullet> l)) = ((m \<bullet> n) \<bullet> l)"
proof (induction m)
case IZ
  show ?case by simp
case (IPos m)
  show ?case apply -
             apply (cases n)
             apply simp
             apply (cases l)
             apply simp
             apply (simp add: addy_assoc)
             apply simp (* in progress *)