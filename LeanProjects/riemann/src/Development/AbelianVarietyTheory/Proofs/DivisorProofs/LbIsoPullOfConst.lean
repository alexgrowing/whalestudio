import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfSymmetric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvCompOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ConstDefSym

open GlobalTheory.CechPic

theorem lbIso_pull_of_const : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : Type) [Field k] [CharZero k] (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → LBIso (Q.P.L.pull π₁) (Q.P.L.pull π₂) := by
  intro R _ _ Q k _ _ ρ B' _ π₁ π₂ h₁ h₂ hfib

  let ρ₀ : R →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ
  let A₀ : Over (Sp k) := (Over.pullback (spMap ρ₀)).obj Q.P.A
  letI : GrpObj A₀ := Functor.grpObjObj
  have hj : IsGrpPullback A₀ Q.P.A (spMap ρ₀) (pullback.fst Q.P.A.hom (spMap ρ₀)) := isGrpPullback_pullback Q.P.A (spMap ρ₀)
  have ec : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫ spMap ρ₀ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have h₂' : IsGrpPullback B' Q.P.A (spMap (algebraMap k (DualNumber k)) ≫ spMap ρ₀) π₂ := h₂.congr ec rfl
  let q : B'.left ⟶ A₀.left := hj.1.lift π₂ (B'.hom ≫ spMap (algebraMap k (DualNumber k)))
    (by rw [h₂'.1.w, Category.assoc])
  have hq₁ : q ≫ pullback.fst Q.P.A.hom (spMap ρ₀) = π₂ := hj.1.lift_fst _ _ _
  have hq₂ : q ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) := hj.1.lift_snd _ _ _
  have hq : IsGrpPullback B' A₀ (spMap (algebraMap k (DualNumber k))) q :=
    IsGrpPullback.cancel hj (h₂'.congr rfl hq₁.symm) hq₂
  have eid : GlobalTheory.DeRham.epsRed k ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [GlobalTheory.DeRham.epsRed, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of k)
    ext x
    simp
  let i : A₀.left ⟶ B'.left := hq.1.lift (𝟙 _) (A₀.hom ≫ GlobalTheory.DeRham.epsRed k)
    (by rw [Category.id_comp, Category.assoc, eid, Category.comp_id])
  have e : i ≫ q = 𝟙 _ := hq.1.lift_fst _ _ _
  have hi₂ : i ≫ B'.hom = A₀.hom ≫ GlobalTheory.DeRham.epsRed k := hq.1.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl A₀).hom := inferInstanceAs (IsMonHom (𝟙 A₀))
  have hi : IsGrpPullback A₀ B' (GlobalTheory.DeRham.epsRed k) i :=
    IsGrpPullback.cancel hq ((isGrpPullback_of_iso (Iso.refl A₀)).congr eid.symm (by rw [e]; rfl)) hi₂
  have hA₀ : IsAbelianScheme A₀ := PolPull.isAbelianScheme_of_isGrpPullback Q.P.isAb hj

  have hL := Q.P.isLB
  have hsymA : pull (GrpObj.inv : Q.P.A ⟶ Q.P.A).left (cls Q.P.L hL) = cls Q.P.L hL := by
    have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨Q.sym, Q.sym_gen⟩
    rw [cls_linComb hL] at h0
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul,
      pull_id] at h0
    exact sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h0)
  have key : ∀ {f : Sp (DualNumber k) ⟶ Sp R} (π : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A f π →
      LBIso ((Q.P.L.pull π).pull (GrpObj.inv : B' ⟶ B').left) (Q.P.L.pull π) := by
    intro f π hπ
    rw [← cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _)]
    show pull _ (pull π (cls Q.P.L hL)) = pull π (cls Q.P.L hL)
    rw [← pull_comp, GlobalTheory.SymSpread.inv_comp_of_isGrpPullback hπ, pull_comp, hsymA]
  have hfib' : i ≫ π₁ = i ≫ π₂ := hfib A₀.left i A₀.hom hi₂
  have hclosed : LBIso ((Q.P.L.pull π₁).pull i) ((Q.P.L.pull π₂).pull i) := by
    rw [← cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)]
    show pull i (pull π₁ (cls Q.P.L hL)) = pull i (pull π₂ (cls Q.P.L hL))
    rw [← pull_comp, ← pull_comp, hfib']
  exact GlobalTheory.SymFirstOrder.lbIso_of_symmetric k A₀ B' i q hA₀ hi hq e _ _ (pull_isLB hL _) (pull_isLB hL _)
    (key π₁ h₁) (key π₂ h₂) hclosed

end GlobalTheory.ConstDefSym
