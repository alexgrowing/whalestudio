import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExactExponentsSmulMemLocalizedCoeffLattice
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Divisibility.RowLat
open NumberField IsDedekindDomain Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_exactExponents_smul_mem_localizedCoeffLattice : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (w : HeightOneSpectrum (𝓞 K)), ∀ x ∈ nabAtr emb lam L, (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delAtr emb lam L) := by
  first | exact @GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr | exact GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr | (intros; apply GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr <;> assumption)
