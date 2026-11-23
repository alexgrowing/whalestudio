import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualApprox

variable (R : Type) [CommRing R]

abbrev spO (C : Type) [CommRing C] [Algebra R C] : Over (Sp R) := Over.mk (spMap (algebraMap R C))

variable {R}

def spOMap {C C' : Type} [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C'] (f : C →ₐ[R] C') :
    spO R C' ⟶ spO R C :=
  Over.homMk (spMap f.toRingHom) (Spread.spMap_algHom_comp f)

@[simp]
theorem spOMap_left {C C' : Type} [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C'] (f : C →ₐ[R] C') :
    (spOMap f).left = spMap f.toRingHom := rfl

theorem spOMap_comp {C C' C'' : Type} [CommRing C] [CommRing C'] [CommRing C''] [Algebra R C] [Algebra R C']
    [Algebra R C''] (f : C →ₐ[R] C') (g : C' →ₐ[R] C'') : spOMap g ≫ spOMap f = spOMap (g.comp f) := by
  ext1
  simp only [Over.comp_left, spOMap_left]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

variable (R) (C : Type) [CommRing C] [Algebra R C]

abbrev stage (s : Finset C) : Over (Sp R) := spO R (Algebra.adjoin R (s : Set C))

def toStage (s : Finset C) : spO R C ⟶ stage R C s := spOMap (Algebra.adjoin R (s : Set C)).val

variable {R C}

def stageMap {s t : Finset C} (h : s ⊆ t) : stage R C t ⟶ stage R C s :=
  spOMap (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h)))

@[reassoc]
theorem toStage_stageMap {s t : Finset C} (h : s ⊆ t) : toStage R C t ≫ stageMap h = toStage R C s := by
  rw [toStage, stageMap, spOMap_comp, toStage]
  rfl

theorem whiskerLeft_toStage_left (X : Over (Sp R)) (s : Finset C) :
    (X ◁ toStage R C s).left = Spread.bcMap X.hom (Algebra.adjoin R (s : Set C)).val :=
  Spread.eq_bcMap X.hom _ (Over.whiskerLeft_left_fst _) (Over.whiskerLeft_left_snd _)

theorem whiskerLeft_stageMap_left (X : Over (Sp R)) {s t : Finset C} (h : s ⊆ t) :
    (X ◁ stageMap h).left = Spread.bcMap X.hom (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h))) :=
  Spread.eq_bcMap X.hom _ (Over.whiskerLeft_left_fst _) (Over.whiskerLeft_left_snd _)

instance (s : Finset C) : IsAffine (stage R C s).left := by
  dsimp; infer_instance

theorem locallyOfFiniteType_stage (s : Finset C) : LocallyOfFiniteType (stage R C s).hom := by
  dsimp
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  show RingHom.FiniteType (algebraMap R (Algebra.adjoin R (s : Set C)))
  rw [RingHom.finiteType_algebraMap, ← Subalgebra.fg_iff_finiteType]
  exact Subalgebra.fg_adjoin_finset s

open GlobalTheory.CechPic in

theorem exists_lb_stage (X : Over (Sp R)) [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (N : LB (X ⊗ spO R C).left) (hN : N.IsLB) :
    ∃ (s : Finset C) (M : LB (X ⊗ stage R C s).left), M.IsLB ∧ LBIso N (M.pull (X ◁ toStage R C s).left) := by
  classical
  let ρ : ∀ s : (Finset C)ᵒᵖ, (X ⊗ spO R C).left ⟶ (Spread.bcDiagram X.hom C).obj s := fun s =>
    (Spread.bcCone X.hom C).π.app s
  have w : ∀ {s t} (g : s ⟶ t), ρ s ≫ (Spread.bcDiagram X.hom C).map g = ρ t := fun g =>
    ((Spread.bcCone X.hom C).w g)
  have hc : IsLimit (schemeConeOfFamily _ ρ w) := Spread.isLimitBcCone X.hom C
  obtain ⟨s, M, hM, hiso, -⟩ := LBLimit.exists_lb_of_isLimit _ ρ w hc N hN
  refine ⟨s.unop, M, hM, ?_⟩
  rw [whiskerLeft_toStage_left]
  exact hiso

open GlobalTheory.CechPic in

theorem exists_stage_pull_eq (X : Over (Sp R)) [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (s : Finset C) (c c' : Pic (X ⊗ stage R C s).left)
    (h : CechPic.pull (X ◁ toStage R C s).left c = CechPic.pull (X ◁ toStage R C s).left c') :
    ∃ (t : Finset C) (hst : s ⊆ t),
      CechPic.pull (X ◁ stageMap hst).left c = CechPic.pull (X ◁ stageMap hst).left c' := by
  classical
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨L', hL', rfl⟩ := cls_surj c'
  let ρ : ∀ s : (Finset C)ᵒᵖ, (X ⊗ spO R C).left ⟶ (Spread.bcDiagram X.hom C).obj s := fun s =>
    (Spread.bcCone X.hom C).π.app s
  have w : ∀ {s t} (g : s ⟶ t), ρ s ≫ (Spread.bcDiagram X.hom C).map g = ρ t := fun g =>
    ((Spread.bcCone X.hom C).w g)
  have hc : IsLimit (schemeConeOfFamily _ ρ w) := Spread.isLimitBcCone X.hom C
  have h' : LBIso (L.pull (X ◁ toStage R C s).left) (L'.pull (X ◁ toStage R C s).left) :=
    (cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).1 h
  rw [whiskerLeft_toStage_left] at h'
  have e : LBIso (L.pull (ρ (.op s))) (L'.pull (ρ (.op s))) := h'
  obtain ⟨j, f, hf⟩ := exists_lbIso_of_isLimit _ ρ w hc (i := .op s) L L' hL hL' e
  refine ⟨j.unop, f.unop.le, ?_⟩
  rw [whiskerLeft_stageMap_left]
  exact (cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).2 hf

end GlobalTheory.DualApprox

namespace GlobalTheory.DualApprox

open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon

variable {R : Type} [CommRing R] {C : Type} [CommRing C] [Algebra R C]

theorem whiskerLeft_eq_lift' {X Y Z : Over (Sp R)} (g : Y ⟶ Z) : X ◁ g = lift (fst X Y) (snd X Y ≫ g) := by
  ext1 <;> simp

theorem exists_fam_stage (A : Over (Sp R)) [GrpObj A] [QuasiCompact A.hom] [QuasiSeparated A.hom]
    (N : LB (A ⊗ spO R C).left) (hF : Fam A N) :
    ∃ (t : Finset C) (N₀ : LB (A ⊗ stage R C t).left), Fam A N₀ ∧ Same A N N₀ (𝟙 _) (toStage R C t) := by
  classical
  have hN := hF.isLB
  obtain ⟨s, M, hM, hiso⟩ := exists_lb_stage A N hN
  have H1 : ∀ (Y : Over (Sp R)) (x : Y ⟶ A) (y : Y ⟶ spO R C), evc hN x y = evc hM x (y ≫ toStage R C s) := by
    intro Y x y
    have e : cls N hN = cls _ (pull_isLB hM (A ◁ toStage R C s).left) := (cls_eq_iff hN (pull_isLB hM _)).2 hiso
    have e2 : cls _ (pull_isLB hM (A ◁ toStage R C s).left) = evc hM (fst A _) (snd A _ ≫ toStage R C s) := by
      rw [whiskerLeft_eq_lift']; rfl
    rw [evc, e, e2, pull_evc, lift_fst, lift_snd_assoc]
  have : QuasiCompact (A ⊗ A).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have : QuasiSeparated (A ⊗ A).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  let D : ∀ U : Over (Sp R), (M : LB (A ⊗ U).left) → M.IsLB → Pic ((A ⊗ A) ⊗ U).left := fun U M hM =>
    evc hM (fst (A ⊗ A) U ≫ fst A A * fst (A ⊗ A) U ≫ snd A A) (snd (A ⊗ A) U) -
      evc hM (fst (A ⊗ A) U ≫ fst A A) (snd (A ⊗ A) U) - evc hM (fst (A ⊗ A) U ≫ snd A A) (snd (A ⊗ A) U)
  have hD : CechPic.pull ((A ⊗ A) ◁ toStage R C s).left (D _ M hM) = CechPic.pull ((A ⊗ A) ◁ toStage R C s).left 0 := by
    rw [map_zero]
    simp only [D, map_sub, pull_evc, MonObj.comp_mul, ← Category.assoc, whiskerLeft_fst, whiskerLeft_snd]
    rw [← H1, ← H1, ← H1, (isAdditive_iff hN).1 hF.add]
    abel
  obtain ⟨t, hst, ht⟩ := exists_stage_pull_eq (A ⊗ A) s _ _ hD
  rw [map_zero] at ht
  let N₀ : LB (A ⊗ stage R C t).left := ev M (fst A _) (snd A _ ≫ stageMap hst)
  have hN₀ : N₀.IsLB := pull_isLB hM _
  have H2 : ∀ (Y : Over (Sp R)) (x : Y ⟶ A) (y : Y ⟶ stage R C t), evc hN₀ x y = evc hM x (y ≫ stageMap hst) := by
    intro Y x y
    rw [evc_ev hM, lift_fst, lift_snd_assoc]
  refine ⟨t, N₀, ⟨hN₀, (isAdditive_iff hN₀).2 fun Y a a' y => ?_⟩, ?_⟩
  · rw [H2, H2, H2]
    have e := congrArg (CechPic.pull (lift (lift a a') y).left) ht
    simp only [D, map_sub, map_zero, pull_evc, MonObj.comp_mul, ← Category.assoc, whiskerLeft_fst,
      whiskerLeft_snd] at e
    simp only [Category.assoc, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd, whiskerLeft_fst_assoc,
      whiskerLeft_snd_assoc] at e
    rw [sub_sub, sub_eq_zero] at e
    exact e
  · rw [same_iff hN hN₀, H2, Category.assoc, toStage_stageMap, ← H1, Category.comp_id]

end GlobalTheory.DualApprox

namespace GlobalTheory.DualApprox

open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon

theorem exists_fam_finiteType : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (T : Over (Sp R)) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ∃ (T₀ : Over (Sp R)) (h : T ⟶ T₀) (N₀ : LB (A ⊗ T₀).left), IsAffine T₀.left ∧ LocallyOfFiniteType T₀.hom ∧ Fam A N₀ ∧ Same A N N₀ (𝟙 T) h := by
  intro R _ _ A _ hA T _ N hF
  have : IsProper A.hom := hA.proper
  letI : Algebra R Γ(T.left, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop).hom.toAlgebra
  let e : T ≅ spO R Γ(T.left, ⊤) := Over.isoMk T.left.isoSpec (by
    show T.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop).hom) = T.hom
    rw [CommRingCat.ofHom_hom, Spec.map_comp]
    simp only [Scheme.isoSpec, asIso_hom]
    rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id])
  have hN := hF.isLB
  let N' : LB (A ⊗ spO R Γ(T.left, ⊤)).left := ev N (fst A _) (snd A _ ≫ e.inv)
  have hN' : N'.IsLB := pull_isLB hN _
  have H : ∀ (Y : Over (Sp R)) (x : Y ⟶ A) (y : Y ⟶ spO R Γ(T.left, ⊤)),
      evc hN' x y = evc hN x (y ≫ e.inv) := by
    intro Y x y
    rw [evc_ev hN, lift_fst, lift_snd_assoc]
  have hF' : Fam A N' := ⟨hN', (isAdditive_iff hN').2 fun Y a a' y => by
    rw [H, H, H]
    exact (isAdditive_iff hN).1 hF.add _ _ _ _⟩
  obtain ⟨t, N₀, h₀, hs⟩ := exists_fam_stage A N' hF'
  refine ⟨stage R _ t, e.hom ≫ toStage R _ t, N₀, inferInstance, locallyOfFiniteType_stage t, h₀, ?_⟩
  rw [same_iff hN' h₀.isLB] at hs
  rw [same_iff hN h₀.isLB]
  have k := congrArg (CechPic.pull (A ◁ e.hom).left) hs
  rw [pull_evc, pull_evc, whiskerLeft_fst, ← Category.assoc, whiskerLeft_snd, Category.comp_id, H,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, ← Category.assoc, whiskerLeft_snd,
    Category.assoc] at k
  rw [Category.comp_id]
  exact k

end GlobalTheory.DualApprox
