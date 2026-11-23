import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_projective_stalk_factorial : ∀ (n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (X : Scheme.{0}) (p : X ⟶ S), IsProjOver s → Smooth s → Smooth p → QuasiCompact p → IsLocallyNoetherian X ∧ CompactSpace X ∧ ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  first | exact @GlobalTheory.CycAwayReg.smooth_over_projective_factorial | exact GlobalTheory.CycAwayReg.smooth_over_projective_factorial | (intros; apply GlobalTheory.CycAwayReg.smooth_over_projective_factorial <;> assumption)
