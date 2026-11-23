import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormRingActionSymmetric
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_form_ring_action_symmetric : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X.A)),
    IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ → ∀ (b : 𝓞 F) (x y : HdR X.A),
      ψ (act (dp0 R) (𝟙 _) X.rm b x) y = ψ x (act (dp0 R) (𝟙 _) X.rm b y) := by
  first | exact @GlobalTheory.RealMultAdjoint.polForm_adjoint_rm | exact GlobalTheory.RealMultAdjoint.polForm_adjoint_rm | (intros; apply GlobalTheory.RealMultAdjoint.polForm_adjoint_rm <;> assumption)
