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
  assumes "\<And> x. id' \<cdot> x = x"
  and "\<And> x. x \<cdot> id' = x"
  shows "id = id'"
  proof -
  have "id' \<cdot> id = id" using assms by blast
  moreover have "id' \<cdot> id = id'" by simp
  ultimately show ?thesis by simp
  qed
  
  
thm group_def

datatype Nat = Zero | Succ Nat

fun addy :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat" where
"addy Zero n = n"|
"addy (Succ n) m = Succ (addy n m)"

