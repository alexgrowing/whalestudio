import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatInt
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int : ∃ e : FiniteAdeleRing (𝓞 ℚ) ℚ ≃ₐ[ℚ] FiniteAdeleRing ℤ ℚ, Continuous e := by
  first | (exact @GlobalTheory.AdeleZ.exists_continuous_adele_equiv) | (exact GlobalTheory.AdeleZ.exists_continuous_adele_equiv) | (intros; apply GlobalTheory.AdeleZ.exists_continuous_adele_equiv <;> assumption)
