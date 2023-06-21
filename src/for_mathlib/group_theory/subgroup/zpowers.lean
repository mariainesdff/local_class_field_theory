import group_theory.subgroup.zpowers

namespace add_subgroup

lemma closure_singleton_eq_zmultiples {A : Type*} [add_group A] (a : A) :
  closure {a} = zmultiples a :=
by ext n; rw [mem_closure_singleton, mem_zmultiples_iff]

end add_subgroup