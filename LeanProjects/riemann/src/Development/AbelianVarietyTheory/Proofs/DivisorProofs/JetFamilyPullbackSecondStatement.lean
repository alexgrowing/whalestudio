import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFamilyPullbackSecond
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_family_pullback_second : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (J' : JetRing R' I n) {X₀ : Obj F 𝔠 (Sp R)} {δ₀ : X₀.DetGen}
    {N : I → Module.End R (HdR X₀.A)} (Y : Family J X₀ δ₀ N) {X₁ : Obj F 𝔠 (Sp R')}
    {N₁ : I → Module.End R' (HdR X₁.A)} {p : X₁.A.left ⟶ X₀.A.left}, X₁.IsPullBy X₀ (spMap σ) p →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 R') (𝟙 _) X₁.A σ (spMap σ) p),
    (∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (N₁ i x)) → ∀ (τ : J.B →+* J'.B),
    (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) → IsDPMorphism J.κ J'.κ τ →
    ∀ {Z' : Obj F 𝔠 (Sp J'.B)} {q : Z'.A.left ⟶ Y.X'.A.left}, Z'.IsPullBy Y.X' (spMap τ) q →
    ∀ {i' : X₁.A.left ⟶ Z'.A.left} (hi' : X₁.IsPullBy Z' (spMap J'.π) i'), i' ≫ q = p ≫ Y.i →
    ∀ (mor' : GrpMor (dp0 R') (𝟙 _) X₁.A J'.κ (spMap J'.π) X₁.A (algebraMap R' J'.B) (𝟙 _) (Over.Hom.left (𝟙 X₁.A))),
    ∀ (δ₁ : X₁.DetGen), Obj.DetCorr σ p δ₀.1 δ₁.1 → ∀ (δ' : Z'.DetGen), Obj.DetCorr τ q Y.δ'.1 δ'.1 →
    ∀ (x : Fin (Module.finrank ℚ F) → HdR X₁.A) (d : Fin (Module.finrank ℚ F) → Crys J'.κ (spMap J'.π) X₁.A)
      (v : Fin (Module.finrank ℚ F) → X₁.Lie) (v' : Fin (Module.finrank ℚ F) → Z'.Lie),
      (∀ j, IsJetElt J' X₁ N₁ mor' (x j) (d j) ∧ IsLieImage (x j) (v j).hom ∧
        IsLieImage (crysToDR J'.κ hi'.grp (d j)) (v' j).hom) →
      δ'.1 v' = algebraMap R' J'.B (δ₁.1 v) := by
  first | exact @GlobalTheory.JetBCGen.detGen_baseChange | exact GlobalTheory.JetBCGen.detGen_baseChange | (intros; apply GlobalTheory.JetBCGen.detGen_baseChange <;> assumption)
