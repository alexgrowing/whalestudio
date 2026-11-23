import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.LocalHodgeTateComplexTower
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HodgeTateSpectral.HTSpecGood

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalV GlobalTheory.HTLink GlobalTheory.HodgeCoh GlobalTheory.EtC GlobalTheory.Pst

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8

variable {l : ℕ} [Fact l.Prime]

def GoodModel {K : FinExt l} {X : Scheme.{0}} (q : X ⟶ Sp ↥K.1) (M : CrystallineSemistableComparison.Model l K.1) : Prop :=
  M.Sm ∧ (∃ d, SmoothOfRelativeDimension d M.p) ∧ ∃ e : M.gen ≅ X, e.hom ≫ q = M.q

def HasGoodCovers {K : FinExt l} (H : HTower ↥K.1) {J : Type} (ι : J → H.Γ) : Prop :=
  ∃ (MZ : CrystallineSemistableComparison.Model l K.1) (eZ : MZ.gen ≅ H.Z), GoodModel H.q MZ ∧ eZ.hom ≫ H.q = MZ.q ∧ ∀ j, ∃ (W : Scheme.{0})
    (c : W ⟶ H.Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (I : Type) (_ : Fintype I) (σ : I → (W ⟶ H.Y (ι j))),
    IsGalois c G a ∧ Splits (H.s (ι j)) c σ ∧ ∃ (MW : CrystallineSemistableComparison.Model l K.1) (eW : MW.gen ≅ W), GoodModel (c ≫ H.q) MW ∧
      (∃ (uc : MW.X ⟶ MZ.X) (hu : uc ≫ MZ.p = MW.p), CrystallineSemistableComparison.Model.genMap uc hu ≫ eZ.hom = eW.hom ≫ c) ∧
      ∀ i, ∃ (ui : MW.X ⟶ MZ.X) (hu : ui ≫ MZ.p = MW.p), CrystallineSemistableComparison.Model.genMap ui hu ≫ eZ.hom = eW.hom ≫ σ i ≫ H.t (ι j)

def CoverOf : Prop :=
  CrystallineSemistableComparison.HTSpecB.HTSpecGood → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (H : HTower ↥K.1) {J : Type} (ι : J → H.Γ),
    HasGoodCovers H ι → ∀ n, HTCover H ι n

end PositivityTheory.AutomorphicGaloisHodgeTate.G8
