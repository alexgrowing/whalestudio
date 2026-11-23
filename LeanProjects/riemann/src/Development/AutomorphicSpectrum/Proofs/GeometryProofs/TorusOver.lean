import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch

def TorusOver {L L' : Type} [Field L] [Field L'] (e : L →+* L') {G : Over (Sp L)} {G' : Over (Sp L')} [GrpObj G]
    [GrpObj G'] (τ : TorusExtension G) (τ' : TorusExtension G') (φ : G'.left ⟶ G.left) : Prop :=
  letI := τ.addCommGroup
  letI := τ'.addCommGroup
  ∃ κ : τ.X ≃+ τ'.X, ∀ (A : Type) [CommRing A] (a : Sp A ⟶ Sp L') (t' : Over.mk a ⟶ splitTorus (Sp L') τ'.X)
    (t : Over.mk (a ≫ spMap e) ⟶ splitTorus (Sp L) τ.X), (∀ χ, charVal t χ = charVal t' (κ χ)) →
      (t' ≫ τ'.i).left ≫ φ = (t ≫ τ.i).left

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch
