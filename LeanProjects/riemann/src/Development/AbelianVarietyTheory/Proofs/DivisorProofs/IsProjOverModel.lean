import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsFiniteOverProjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ProjOverBase

theorem isProjOver_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (κ : C.o →+* X.o₁), X.uΩ ≫ C.i ≫ C.z = spMap ((algebraMap X.o₁ X.Ω₁).comp κ) → IsProjOver X.M.s := by
  intro E _ _ _ H Dw l Xo cf C X κ h
  have hs : X.M.s ≫ spMap κ = X.π ≫ C.z := by
    refine ext_of_isDominant X.M.pt ?_
    rw [← Category.assoc, X.M.pt_s, ← Category.assoc, X.comp]
    simp only [USetup.uΩ, UCompact.i, Category.assoc] at h ⊢
    rw [h]
    exact (Spec.map_comp (CommRingCat.ofHom κ) (CommRingCat.ofHom (algebraMap X.o₁ X.Ω₁))).symm
  haveI := C.ded
  exact GlobalTheory.FiniteOverProj.isProjOver_of_isFinite_over C.o X.o₁ κ X.M.Z C.Z C.z X.π X.M.s C.proj X.fin inferInstance hs

end GlobalTheory.UPoinc.ProjOverBase

end
