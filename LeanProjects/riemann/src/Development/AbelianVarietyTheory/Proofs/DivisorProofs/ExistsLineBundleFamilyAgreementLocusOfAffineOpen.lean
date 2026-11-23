import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameRigidifiedFamilyAbelianSchemeOfLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedImmersionRepresentsOfAffineOpensStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.GlueKernel

theorem same_comp {S : Scheme.{0}} {A U T Y Y' : Over S} {M : LB (A ⊗ U).left} {N : LB (A ⊗ T).left}
    (hM : M.IsLB) (hN : N.IsLB) (f : Y' ⟶ Y) (u : Y ⟶ U) (t : Y ⟶ T) (h : Same A M N u t) :
    Same A M N (f ≫ u) (f ≫ t) := by
  rw [same_iff hM hN] at h ⊢
  have e := congrArg (GlobalTheory.CechPic.pull (A ◁ f).left) h
  rw [pull_evc, pull_evc] at e
  simpa only [whiskerLeft_fst, whiskerLeft_snd_assoc] using e

theorem exists_kernel_of_affine : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U T : Over (Sp R)) (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) (hM : M.IsLB) (hN : N.IsLB), (∀ (Y : Over (Sp R)) (u : Y ⟶ U), evc hM (1 : Y ⟶ A) u = 0) → (∀ (Y : Over (Sp R)) (t : Y ⟶ T), evc hN (1 : Y ⟶ A) t = 0) → (∀ V : T.left.affineOpens, ∃ (H : Over (Sp R)) (h : H ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Flat (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)), Same A M N u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t) → ∃ (H : Over (Sp R)) (h : H ⟶ U ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U T).left ∧ Flat (h ≫ snd U T).left ∧ Surjective (h ≫ snd U T).left ∧ ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ T), Same A M N u t ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by
  intro R _ _ A _ hA U T M N hM hN h0M h0N hV
  exact GlobalTheory.T.exists_closedImmersion_represents_of_affineOpens_alt (Sp R) U T (fun Y u t => Same A M N u t)
    (fun Y Y' f u t h => same_comp hM hN f u t h)
    (fun Y u t h => GlobalTheory.T.sameRigidifiedFamily_abelianScheme_of_local R A hA U T M N hM hN h0M h0N Y u t h) hV

end GlobalTheory.DualCon.GlueKernel
