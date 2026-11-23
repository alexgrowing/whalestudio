import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFiltrationSpannedCorrespondence
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_filtration_spanned_correspondence : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap σ) φ →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) φ),
    Submodule.span R' {x' | ∃ x, m.Corr x x'} = ⊤ ∧
      Fil X'.A ≤ Submodule.span R' {x' | ∃ x ∈ Fil X.A, m.Corr x x'} ∧
      ∀ x x', x ∈ Fil X.A → m.Corr x x' → x' ∈ Fil X'.A := by
  first | exact @GlobalTheory.DeRham.span_corr_baseChange | exact GlobalTheory.DeRham.span_corr_baseChange | (intros; apply GlobalTheory.DeRham.span_corr_baseChange <;> assumption)
