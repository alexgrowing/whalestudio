import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetMorphismIsBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_morphism_is_base_change : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
    m.IsBC := by
  first | exact @GlobalTheory.LatJet.grpMor_isBC | exact GlobalTheory.LatJet.grpMor_isBC | (intros; apply GlobalTheory.LatJet.grpMor_isBC <;> assumption)
