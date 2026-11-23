import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import Formalism.RealPlaceAnalysis.StatementKT
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.CompactRelationsApplyComm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.ParthasarathyTensorMatrix

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem parthasarathy_tensor_matrix (ε : Fin n → Bool) {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F)
    {Λ : Fin n → ℝ} {V : Submodule ℂ M} (hV : IsKIrrHW ε F Λ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Fin n → Fin n → Matrix ι ι ℂ} (hG : Formalism.REAL.KRel ε G)
    (hGu : ∀ a b, ε a = ε b → G b a = (G a b)ᴴ)
    {ν : Fin n → ℝ} {f : ι → ℂ} (hf0 : f ≠ 0) (hfw : ∀ a, G a a *ᵥ f = ((ν a : ℝ) : ℂ) • f)
    (hfl : ∀ a b, b < a → ε a = ε b → G a b *ᵥ f = 0)
    (hdom : ∀ a b, a < b → ε a = ε b → (Λ + ν) b ≤ (Λ + ν) a) :
    ∃ x : ι → M, (∀ i, x i ∈ V) ∧ x ≠ 0 ∧
      (∀ a i, F a a (x i) + ∑ j, G a a i j • x j = (((Λ + ν) a : ℝ) : ℂ) • x i) ∧
      ∀ a b, a < b → ε a = ε b → ∀ i, F a b (x i) + ∑ j, G a b i j • x j = 0 :=
  parthasarathy_tensor_matrix_alt ε hF hV hG hGu hf0 hfw hfl hdom

theorem kIrrHW_int (ε : Fin n → Bool) {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F) {Λ : Fin n → ℝ} {V : Submodule ℂ M}
    (hV : IsKIrrHW ε F Λ V) : ∀ a b, a < b → ε a = ε b → ∃ m : ℕ, Λ a - Λ b = m :=
  kIrrHW_int' ε hF hV

end ReciprocityTheory.ChartRestriction.DS.HW
