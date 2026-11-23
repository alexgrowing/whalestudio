import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxLevelUnitaryCongrModIdeal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maxLevel_unitary_congr_mod_ideal : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (N : ℕ)
    (g : Matrix (Fin N) (Fin N) (𝓞 D.host.E)), IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det →
      ∃ k : GA D N, k ∈ intG D N ∧ ∀ i j : Fin N,
        ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D ((g i j : 𝓞 D.host.E) : D.host.E) ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.MaxLevelLift.exists_intG_cong | exact GlobalTheory.MaxLevelLift.exists_intG_cong | (intros; apply GlobalTheory.MaxLevelLift.exists_intG_cong <;> assumption)
