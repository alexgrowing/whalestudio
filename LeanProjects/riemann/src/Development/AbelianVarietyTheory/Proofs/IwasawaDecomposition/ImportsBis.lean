import Mathlib

namespace GlobalTheory.IsolatedTheoremTwo

theorem main : ∀ {s : Multiset ℂ}, (∀ x ∈ s, ‖x‖ = (1 : ℝ)) → ‖Multiset.prod s‖ = (1 : ℝ) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro h
    rw [Multiset.prod_cons, norm_mul, h a (Multiset.mem_cons_self a s),
      ih (fun x hx => h x (Multiset.mem_cons_of_mem hx)), one_mul]

end GlobalTheory.IsolatedTheoremTwo
