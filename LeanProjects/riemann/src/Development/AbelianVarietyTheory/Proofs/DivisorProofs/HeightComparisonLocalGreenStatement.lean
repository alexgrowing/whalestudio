import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightComparisonLocalGreen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open NumberField IsDedekindDomain GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_comparison_local_green : ∀ {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} (A : Adl C Y)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (x : Y.X) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (b : HeightOneSpectrum (𝓞 F) → ℝ) (K : ℝ), 0 ≤ K →
    (∀ v ∉ S, ∀ e y, A.lg v e y = g v e y) → (∀ v e y, |A.lg v e y - g v e y| ≤ b v) →
    ∑ v ∈ S, b v ≤ ((A.n : ℕ) : ℝ) * (Module.finrank ℚ F : ℝ) * K →
    |A.ht x - ({ A with lg := g } : Adl C Y).ht x| ≤ K := by
  first | exact @GlobalTheory.TrueGeo.Adl.abs_ht_sub_ht_with_lg_le | exact GlobalTheory.TrueGeo.Adl.abs_ht_sub_ht_with_lg_le | (intros; apply GlobalTheory.TrueGeo.Adl.abs_ht_sub_ht_with_lg_le <;> assumption)
