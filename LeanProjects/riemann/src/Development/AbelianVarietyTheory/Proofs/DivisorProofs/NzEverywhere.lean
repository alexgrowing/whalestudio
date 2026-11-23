import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem nz_everywhere {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] (L : LB G.left) {R : Type} [CommRing R]
    [IsLocalRing R] (χ : Sp R ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))) (h : NZ G L χ σ) :
    ∀ y : (Over.mk χ).left, ∃ g, (fst (Over.mk χ) G).left g = y ∧ g ∈ nonzeroLocus σ := by
  obtain ⟨x, hc, hx⟩ := h
  haveI : Smooth (fst (Over.mk χ) G).left := by
    change Smooth (pullback.fst χ G.hom)
    infer_instance
  have ho : IsOpen ((fst (Over.mk χ) G).left '' (nonzeroLocus σ : Set _)) :=
    (fst (Over.mk χ) G).left.isOpenMap _ (nonzeroLocus σ).isOpen
  intro y
  obtain ⟨g, hg, e⟩ := (IsLocalRing.specializes_closedPoint (R := R) y).mem_open ho ⟨x, hx, hc⟩
  exact ⟨g, e, hg⟩

theorem nz_pull : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G →
    ∀ (R V : Type) [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] (χ : Sp R ⟶ S) (σ : SecAt G L χ)
      (φ : R →+* V), NZ G L χ σ → NZ G L (spMap φ ≫ χ) (SecAt.pull G L σ φ) := by
  intro S G _ L hL hG R V _ _ _ _ χ σ φ h
  haveI : Smooth G.hom := hG.smooth
  exact nz_pullS G hL σ (nz_everywhere G L χ σ h) (spMap φ ≫ χ) _

end GlobalTheory.UMin
