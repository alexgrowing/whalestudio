import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsType

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem capParam_of_isHCTypeW : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (U : ℕ → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHCTypeW k r z u π → (∀ i : Fin k, U (i.val + 1) = u i) → Q.CapParam k r z π U := by
  intro k r z u U Wp _ _ _ π hz hT hπ hU
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨u', hu'⟩ := GlobalTheory.CapelliOfHC.exists_isType k r Wp z π u hz hT hπ'
  intro Bs hB w v
  rw [hu'.2.2.2.2.2 Bs hB w v]
  congr 1
  have key : ∀ f : ℕ → ℝ, ∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (f i : ℂ)) =
      ∏ s : Fin k, (w - (k : ℂ) / 2 + 1 / 2 + (f (s.val + 1) : ℂ)) := by
    intro f
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
      ← Fin.prod_univ_eq_prod_range (fun i => w - (k : ℂ) / 2 + 1 / 2 + (f (1 + i) : ℂ))]
    exact Finset.prod_congr rfl fun s _ => by rw [add_comm 1 s.val]
  rw [key, key, ← GlobalTheory.SupNonzero.prod_eq hu' hπ']
  simp only [hU]

end GlobalTheory.ThA
