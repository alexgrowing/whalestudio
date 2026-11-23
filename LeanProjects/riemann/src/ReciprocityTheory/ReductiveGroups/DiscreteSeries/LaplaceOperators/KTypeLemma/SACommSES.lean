import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TensorActionApplyDual
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.LowestWeightLiftLemmas

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] {MM : Type*} [AddCommGroup MM] [Module ℂ MM]

theorem sA_isKRel (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) : IsKRel ε (sA ε E V hV) := by
  intros; apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sA_isKRel <;> assumption

theorem sA_comm_sES (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (a b : Fin n) (hab : ε a = ε b) : Commute (sA ε E V hV a b) (sES V) := by
  intros; apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sA_comm_sES <;> assumption

theorem sθ_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (EM : Fin n → Fin n → Module.End ℂ MM) (hEM : IsGlRep EM) (φ : MM)
    (ν Λ : Fin n → ℝ) (hφ : ∀ a, EM a a φ = ((ν a : ℝ) : ℂ) • φ) (ℓ : V →ₗ[ℂ] ℂ)
    (hℓ : ∀ (a : Fin n) (v w : V), (w : M) = E a a v → ℓ w = ((Λ a : ℝ) : ℂ) * ℓ v) (a : Fin n)
    (x : KS (n := n) V) :
    sθ V EM φ ℓ (sA ε E V hV a a x) =
      tensV EM a a (sθ V EM φ ℓ x) + ((Λ a - ν a : ℝ) : ℂ) • sθ V EM φ ℓ x := by
  intros; apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sθ_sA <;> assumption

theorem sT_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) (a b : Fin n) (hab : ε a = ε b) (x : KS (n := n) V) :
    sT E V (sA ε E V hV a b x) = tensV E a b (sT E V x) := by
  intros; apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sT_sA <;> assumption

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
