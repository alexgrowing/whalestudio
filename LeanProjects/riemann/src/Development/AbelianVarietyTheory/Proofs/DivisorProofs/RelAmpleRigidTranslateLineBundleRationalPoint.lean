import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigidTranslate

open GlobalTheory.CoordToExt GlobalTheory.PolTranslate

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem transl_transl_inv (t : 𝟙_ (Over S) ⟶ A) : transl t ≫ transl t⁻¹ = 𝟙 A := by
  rw [GlobalTheory.PolTranslate.comp_transl, transl, _root_.mul_assoc, ← MonObj.comp_mul, _root_.mul_inv_cancel,
    MonObj.comp_one, _root_.mul_one]

theorem transl_inv_transl (t : 𝟙_ (Over S) ⟶ A) : transl t⁻¹ ≫ transl t = 𝟙 A := by
  rw [GlobalTheory.PolTranslate.comp_transl, transl, _root_.mul_assoc, ← MonObj.comp_mul, _root_.inv_mul_cancel,
    MonObj.comp_one, _root_.mul_one]

instance isIso_transl_left (t : 𝟙_ (Over S) ⟶ A) : IsIso (transl t).left :=
  ⟨⟨(transl t⁻¹).left, congrArg (fun q => q.left) (transl_transl_inv t),
    congrArg (fun q => q.left) (transl_inv_transl t)⟩⟩

theorem relAmple_rigTransl_of_section [IsAffine S] [IsProper A.hom] {L : LB A.left} (t : 𝟙_ (Over S) ⟶ A)
    (hL : L.IsLB) (h : Out.RelAmple A L) : Out.RelAmple A (rigTransl L t) := by
  have hL' : (rigTransl L t).IsLB := DVR.linComb_isLB _ hL _ _
  refine AmpleLocal.relAmple_of_locally S A _ hL' inferInstance inferInstance fun s => ?_
  let t₀ : S ⟶ A.left := t.left
  obtain ⟨i, hi⟩ := exists_chart hL (t₀ s)
  let U : S.Opens := t₀ ⁻¹ᵁ L.U i
  refine ⟨U, hi, ?_⟩
  have hp : IsPullback (transl t).left A.hom A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w _).trans (Category.comp_id _).symm⟩
  have H := (isPullback_morphismRestrict A.hom U).flip.paste_horiz hp
  have k : (toUnit A ≫ t).left = A.hom ≫ t₀ := rfl
  obtain ⟨w, hw⟩ := lbIso_diff_pull hL (transl t).left (toUnit A ≫ t).left (A.hom ⁻¹ᵁ U).ι i fun z => by
    rw [k]; exact z.2
  exact relAmple_pull (A' := Over.mk (A.hom ∣_ U)) H hL (pull_isLB hL' _) ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) h

theorem relAmple_rigTransl_point : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B →
    ∀ (L : LB B.left), L.IsLB → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, Out.RelAmple B L →
      Out.RelAmple B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  intro K _ B _ hB L hL a h
  have := hB.proper
  exact relAmple_rigTransl_of_section a hL h

end GlobalTheory.RigidTranslate
