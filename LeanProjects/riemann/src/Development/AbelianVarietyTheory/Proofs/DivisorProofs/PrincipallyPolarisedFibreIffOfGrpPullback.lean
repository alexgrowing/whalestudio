import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.FibMove

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso (L.pull (g ≫ f)) ((L.pull f).pull g) :=
  LBIso.chartPull (RigidBundleGlue.chartPullComp L f g _ rfl) (chartPullId _)
    ⟨idIso _, idIso_isGen (pull_isLB (pull_isLB hL f) g)⟩

theorem polFib_move : ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (A : Over S') [GrpObj A] (L' : LB A.left) (f : S' ⟶ S) (φ : A.left ⟶ G.left), L.IsLB → L'.IsLB → IsGrpPullback A G f φ → LBIso L' (L.pull φ) → ∀ (g : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S'), (PolFib A L' g x ↔ PolFib G L g (x ≫ f)) ∧ ∀ (R' : Type) [CommRing R'] (i : R →+* R'), PolFib A L' g x → PolFib A L' g (spMap i ≫ x) := by
  intro S S' G _ L A _ L' f φ hL hL' hφ hLL' g R _ x
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨P, α, hg, hα, hPL⟩
    refine ⟨P, α ≫ φ, hg, hα.comp hφ, ?_⟩
    exact LBIso.trans P.isLB (pull_isLB hL' α) (pull_isLB hL _) hPL
      (LBIso.trans (pull_isLB hL' α) (pull_isLB (pull_isLB hL φ) α) (pull_isLB hL _)
        (RigidBundleGlue.LBIso.pull hLL' α) (lbIso_pull_comp hL φ α).symm)
  · rintro ⟨P, β, hg, hβ, hPL⟩
    have w : β ≫ G.hom = P.A.hom ≫ (x ≫ f) := hβ.1.w
    let α : P.A.left ⟶ A.left := hφ.1.lift β (P.A.hom ≫ x) (by rw [w, Category.assoc])
    have e₁ : α ≫ φ = β := hφ.1.lift_fst _ _ _
    have e₂ : α ≫ A.hom = P.A.hom ≫ x := hφ.1.lift_snd _ _ _
    refine ⟨P, α, hg, IsGrpPullback.cancel hφ (hβ.congr rfl e₁.symm) e₂, ?_⟩
    have h1 : LBIso P.L (L.pull (α ≫ φ)) := by rw [e₁]; exact hPL
    exact LBIso.trans P.isLB (pull_isLB hL _) (pull_isLB hL' α) h1
      (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL φ) α) (pull_isLB hL' α)
        (lbIso_pull_comp hL φ α) (RigidBundleGlue.LBIso.pull hLL'.symm α))
  · rintro R' _ i ⟨P, α, hg, hα, hPL⟩
    obtain ⟨P', ψ, hg', hψ, hPL'⟩ := exists_isPolFibre polBaseChange_holds i P
    refine ⟨P', ψ ≫ α, hg'.trans hg, hψ.comp hα, ?_⟩
    exact LBIso.trans P'.isLB (pull_isLB P.isLB ψ) (pull_isLB hL' _) hPL'.symm
      (LBIso.trans (pull_isLB P.isLB ψ) (pull_isLB (pull_isLB hL' α) ψ) (pull_isLB hL' _)
        (RigidBundleGlue.LBIso.pull hPL ψ) (lbIso_pull_comp hL' α ψ).symm)

end GlobalTheory.UMin.FibMove
