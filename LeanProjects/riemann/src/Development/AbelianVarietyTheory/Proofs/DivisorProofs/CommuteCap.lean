import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CoreFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable

noncomputable section
namespace GlobalTheory.CommutingCapOperators
open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ}

theorem commute_Eop {T : Module.End ℂ (Sm E a)} (h : ∀ X : Lie E a, Commute T (lie E a X))
    (τ : E →+* ℂ) (i j : Fin a) : Commute T (Eop τ i j) := by
  have h1 : ∀ c : Cinf E, Commute T (lieS E a i j c) := fun c => h _
  unfold Eop
  exact ((h1 _).sub_right ((h1 _).smul_right _)).smul_right _

theorem commute_cap {T : Module.End ℂ (Sm E a)} (h : ∀ X : Lie E a, Commute T (lie E a X))
    (τ : E →+* ℂ) (u : ℂ) : Commute T (cap τ u) := by
  have h1 := commute_Eop h τ
  unfold cap Formalism.REAL.qdet
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine (Int.commute_cast _ _).mul_right (Commute.list_prod_right _ _ fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  unfold Formalism.REAL.Tm
  refine Commute.add_right ?_ (h1 _ _)
  split_ifs
  · exact (Algebra.commutes _ T).symm
  · exact Commute.zero_right _

theorem main {T : Module.End ℂ (Sm E a)} (h : ∀ X : Lie E a, Commute T (lie E a X))
    {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) : Commute T z := by
  unfold Zalg at hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨τ, u, rfl⟩ := hx; exact commute_cap h τ u
  | algebraMap r => exact (Algebra.commutes r T).symm
  | add x y _ _ hx hy => exact hx.add_right hy
  | mul x y _ _ hx hy => exact hx.mul_right hy

end GlobalTheory.CommutingCapOperators
end
