import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.InvDer

set_option backward.isDefEq.respectTransparency false in
private theorem specMap_comp_appLE' {Y : Scheme.{0}} {A B : CommRingCat.{0}} (χ : A ⟶ B) (q : Spec A ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (Spec.map χ ≫ q) ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) :
    (Spec.map χ ≫ q).appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom =
      q.appLE U ⊤ hq ≫ (Scheme.ΓSpecIso A).hom ≫ χ := by
  rw [Scheme.Hom.comp_appLE]
  have e1 : ∀ h' : ⊤ ≤ Spec.map χ ⁻¹ᵁ (q ⁻¹ᵁ U), (Spec.map χ).appLE (q ⁻¹ᵁ U) ⊤ h' =
      (Spec A).presheaf.map (homOfLE hq).op ≫ (Spec.map χ).appTop := by
    intro h'
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
    rfl
  rw [e1, Category.assoc, Category.assoc, Scheme.ΓSpecIso_naturality, Scheme.Hom.appLE]
  simp only [Category.assoc]

def ev {C : Type} [CommRing C] {X : Scheme.{0}} (y : Sp C ⟶ X) (V : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ V) : Γ(X, V) →+* C :=
  (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom.comp (y.appLE V ⊤ h).hom

theorem top_comp {C C' : Type} [CommRing C] [CommRing C'] {X : Scheme.{0}} (ψ : C →+* C') (y : Sp C ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ V) : ⊤ ≤ (spMap ψ ≫ y) ⁻¹ᵁ V := fun p _ => h (show spMap ψ p ∈ (⊤ : (Sp C).Opens) from trivial)

theorem ev_congr {C : Type} [CommRing C] {X : Scheme.{0}} {y y' : Sp C ⟶ X} (e : y = y') (V : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ V) (h' : ⊤ ≤ y' ⁻¹ᵁ V) : ev y V h = ev y' V h' := by
  subst e; rfl

theorem ev_comp {C C' : Type} [CommRing C] [CommRing C'] {X : Scheme.{0}} (ψ : C →+* C') (y : Sp C ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ V) (h' : ⊤ ≤ (spMap ψ ≫ y) ⁻¹ᵁ V) (g : Γ(X, V)) : ev (spMap ψ ≫ y) V h' g = ψ (ev y V h g) := by
  have e := specMap_comp_appLE' (CommRingCat.ofHom ψ) y V h' h
  exact congrArg (fun m => m.hom g) e

def bmap {R C : Type} [CommRing R] [CommRing C] (b : Sp C ⟶ Sp R) : R →+* C := (Spec.preimage b).hom

theorem spMap_bmap {R C : Type} [CommRing R] [CommRing C] (b : Sp C ⟶ Sp R) : spMap (bmap b) = b := by
  simp [spMap, bmap]

theorem bmap_spMap {R C : Type} [CommRing R] [CommRing C] (β : R →+* C) : bmap (spMap β) = β := by
  simp [spMap, bmap]

theorem dualMap_sq {R C : Type} [CommRing R] [CommRing C] (β : R →+* C) :
    spMap (dualMap β) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap C (DualNumber C)) ≫ spMap β := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun r => ?_
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_fst_sq {R C : Type} [CommRing R] [CommRing C] (β : R →+* C) :
    spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap (dualMap β) =
      spMap β ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun r => ?_
  simp [dualMap]

theorem dualMap_comp {R C C' : Type} [CommRing R] [CommRing C] [CommRing C'] (β : R →+* C) (ψ : C →+* C') :
    dualMap (ψ.comp β) = (dualMap ψ).comp (dualMap β) := by
  refine RingHom.ext fun r => ?_
  ext <;> simp [dualMap]

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

def piE {C : Type} [CommRing C] (b : Sp C ⟶ Sp R) : epsAt b ⟶ Over.mk b :=
  Over.homMk (spMap (algebraMap C (DualNumber C))) rfl

def rhoE {C : Type} [CommRing C] (b : Sp C ⟶ Sp R) : epsAt b ⟶ epsAt (𝟙 (Sp R)) :=
  Over.homMk (spMap (dualMap (bmap b))) (by
    show spMap _ ≫ spMap (algebraMap R _) ≫ 𝟙 _ = spMap _ ≫ b
    rw [Category.comp_id, dualMap_sq, spMap_bmap])

def tr (v : epsAt (𝟙 (Sp R)) ⟶ G) {C : Type} [CommRing C] (y : Sp C ⟶ G.left) : Sp (DualNumber C) ⟶ G.left :=
  ((piE (y ≫ G.hom) ≫ (Over.homMk y rfl : Over.mk (y ≫ G.hom) ⟶ G)) * (rhoE (y ≫ G.hom) ≫ v)).left

theorem tr_comp (v : epsAt (𝟙 (Sp R)) ⟶ G) {C C' : Type} [CommRing C] [CommRing C'] (ψ : C →+* C') (y : Sp C ⟶ G.left) :
    tr v (spMap ψ ≫ y) = spMap (dualMap ψ) ≫ tr v y := by
  have hb : bmap ((spMap ψ ≫ y) ≫ G.hom) = ψ.comp (bmap (y ≫ G.hom)) := by
    have : (spMap ψ ≫ y) ≫ G.hom = spMap (ψ.comp (bmap (y ≫ G.hom))) := by
      rw [Category.assoc]
      conv_lhs => rw [← spMap_bmap (y ≫ G.hom)]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, bmap_spMap]
  let Ψ : epsAt ((spMap ψ ≫ y) ≫ G.hom) ⟶ epsAt (y ≫ G.hom) :=
    Over.homMk (spMap (dualMap ψ)) (by
      show spMap (dualMap ψ) ≫ spMap (algebraMap C _) ≫ y ≫ G.hom = spMap (algebraMap C' _) ≫ (spMap ψ ≫ y) ≫ G.hom
      rw [← Category.assoc, dualMap_sq]
      simp only [Category.assoc])
  have h1 : piE ((spMap ψ ≫ y) ≫ G.hom) ≫ (Over.homMk (spMap ψ ≫ y) rfl : Over.mk ((spMap ψ ≫ y) ≫ G.hom) ⟶ G) =
      Ψ ≫ piE (y ≫ G.hom) ≫ (Over.homMk y rfl : Over.mk (y ≫ G.hom) ⟶ G) := by
    apply Over.OverMorphism.ext
    show spMap (algebraMap C' _) ≫ spMap ψ ≫ y = spMap (dualMap ψ) ≫ spMap (algebraMap C _) ≫ y
    rw [← Category.assoc, ← Category.assoc, dualMap_sq]
  have h2 : rhoE ((spMap ψ ≫ y) ≫ G.hom) = Ψ ≫ rhoE (y ≫ G.hom) := by
    apply Over.OverMorphism.ext
    show spMap (dualMap (bmap ((spMap ψ ≫ y) ≫ G.hom))) = spMap (dualMap ψ) ≫ spMap (dualMap (bmap (y ≫ G.hom)))
    rw [hb, dualMap_comp]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h2' : rhoE ((spMap ψ ≫ y) ≫ G.hom) ≫ v = Ψ ≫ rhoE (y ≫ G.hom) ≫ v := by
    rw [h2]; exact Category.assoc _ _ _
  unfold tr
  rw [h1, h2', ← MonObj.comp_mul]
  rfl

theorem tr_fst (v : epsAt (𝟙 (Sp R)) ⟶ G) (hv : IsTanAt G (𝟙 (Sp R)) v) {C : Type} [CommRing C] (y : Sp C ⟶ G.left) :
    spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ tr v y = y := by
  let δ : Over.mk (y ≫ G.hom) ⟶ epsAt (y ≫ G.hom) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom C C C).toRingHom) (by
      show spMap _ ≫ spMap (algebraMap C _) ≫ y ≫ G.hom = y ≫ G.hom
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : (TrivSqZeroExt.fstHom C C C).toRingHom.comp (algebraMap C (DualNumber C)) = RingHom.id C := by
        refine RingHom.ext fun r => ?_
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [show ((algebraMap C (DualNumber C) : C →+* DualNumber C)) = algebraMap C (DualNumber C) from rfl]
      erw [this]
      simp)
  have h1 : δ ≫ piE (y ≫ G.hom) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    show spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap (algebraMap C _) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom C C C).toRingHom.comp (algebraMap C (DualNumber C)) = RingHom.id C := by
      refine RingHom.ext fun r => ?_
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    erw [this]
    simp
  have h2 : δ ≫ rhoE (y ≫ G.hom) ≫ v = 1 := by
    let τ : Over.mk (y ≫ G.hom) ⟶ Over.mk (𝟙 (Sp R)) := Over.homMk (y ≫ G.hom) (by simp)
    have : δ ≫ rhoE (y ≫ G.hom) ≫ v = τ ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G) := by
      apply Over.OverMorphism.ext
      show spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap (dualMap (bmap (y ≫ G.hom))) ≫ v.left =
        (y ≫ G.hom) ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left
      rw [← Category.assoc, dualMap_fst_sq, Category.assoc, hv, spMap_bmap]
    rw [this, MonObj.comp_one]
  have h3 : δ ≫ ((piE (y ≫ G.hom) ≫ (Over.homMk y rfl : Over.mk (y ≫ G.hom) ⟶ G)) * (rhoE (y ≫ G.hom) ≫ v)) =
      Over.homMk y rfl := by
    rw [MonObj.comp_mul, h2, ← Category.assoc, h1, Category.id_comp, _root_.mul_one]
  exact congrArg (fun m => m.left) h3

theorem surj_fst {C : Type} [CommRing C] (q : Sp (DualNumber C)) :
    ∃ p : Sp C, spMap (TrivSqZeroExt.fstHom C C C).toRingHom p = q := by
  refine ⟨PrimeSpectrum.comap (algebraMap C (DualNumber C)) q, ?_⟩
  show PrimeSpectrum.comap (TrivSqZeroExt.fstHom C C C).toRingHom (PrimeSpectrum.comap (algebraMap C (DualNumber C)) q) = q
  apply PrimeSpectrum.ext
  ext x
  have hn : TrivSqZeroExt.inr x.snd ∈ q.asIdeal := by
    have h2 : (TrivSqZeroExt.inr x.snd : DualNumber C) * TrivSqZeroExt.inr x.snd = 0 := by simp
    have : (TrivSqZeroExt.inr x.snd : DualNumber C) * TrivSqZeroExt.inr x.snd ∈ q.asIdeal := by
      rw [h2]; exact zero_mem _
    exact (q.isPrime.mem_or_mem this).elim id id
  have hx : x = algebraMap C (DualNumber C) x.fst + TrivSqZeroExt.inr x.snd := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  show algebraMap C (DualNumber C) x.fst ∈ q.asIdeal ↔ x ∈ q.asIdeal
  constructor
  · intro h; rw [hx]; exact add_mem h hn
  · intro h
    have : algebraMap C (DualNumber C) x.fst = x - TrivSqZeroExt.inr x.snd := eq_sub_of_add_eq hx.symm
    rw [this]; exact sub_mem h hn

theorem tr_top (v : epsAt (𝟙 (Sp R)) ⟶ G) (hv : IsTanAt G (𝟙 (Sp R)) v) {C : Type} [CommRing C] (y : Sp C ⟶ G.left)
    (V : G.left.Opens) (h : ⊤ ≤ y ⁻¹ᵁ V) : ⊤ ≤ (tr v y) ⁻¹ᵁ V := by
  intro q _
  obtain ⟨p, rfl⟩ := surj_fst q
  have : (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ tr v y) p ∈ V := by
    rw [tr_fst v hv]; exact h (show p ∈ (⊤ : (Sp C).Opens) from trivial)
  exact this

section Aff

variable {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V)

include hV in
theorem from_top : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := by rw [hV.fromSpec_preimage_self]

theorem ev_fromSpec (g : Γ(X, V)) : ev (C := Γ(X, V)) hV.fromSpec V (from_top hV) g = g := by
  have e : hV.fromSpec.appLE V ⊤ (from_top hV) = (Scheme.ΓSpecIso Γ(X, V)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, V)).presheaf.map_id _
  show (Scheme.ΓSpecIso _).hom.hom ((hV.fromSpec.appLE V ⊤ (from_top hV)).hom g) = g
  rw [e]
  exact congrArg (fun m => m.hom g) (Scheme.ΓSpecIso Γ(X, V)).inv_hom_id

theorem point_fac {C : Type} [CommRing C] (y : Sp C ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ V) : spMap (ev y V h) ≫ hV.fromSpec = y := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec y hV (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have e2 : CommRingCat.ofHom (ev y V h) = y.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom := rfl
  show Spec.map (CommRingCat.ofHom (ev y V h)) ≫ _ = y
  rw [e2, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id]
  simp

theorem ev_res {C : Type} [CommRing C] (y : Sp C ⟶ X) {V V' : X.Opens} (le : V' ≤ V) (h : ⊤ ≤ y ⁻¹ᵁ V)
    (h' : ⊤ ≤ y ⁻¹ᵁ V') (g : Γ(X, V)) : ev y V' h' ((X.presheaf.map (homOfLE le).op).hom g) = ev y V h g := by
  have e : (X.presheaf.map (homOfLE le).op) ≫ y.appLE V' ⊤ h' = y.appLE V ⊤ h := Scheme.Hom.map_appLE _ _ _
  show (Scheme.ΓSpecIso _).hom.hom ((y.appLE V' ⊤ h').hom ((X.presheaf.map (homOfLE le).op).hom g)) =
    (Scheme.ΓSpecIso _).hom.hom ((y.appLE V ⊤ h).hom g)
  rw [← e]
  rfl

end Aff

theorem ev_const {C : Type} [CommRing C] {X : Scheme.{0}} (p : X ⟶ Sp R) (y : Sp C ⟶ X) (V : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ V)
    (c : R) : ev y V h (constFn p V c) = bmap (y ≫ p) c := by
  have m1 : (y ≫ p).appTop = p.appLE ⊤ V le_top ≫ y.appLE V ⊤ h :=
    ((Scheme.Hom.appLE_comp_appLE y p ⊤ V ⊤ le_top h).trans (Scheme.Hom.appLE_eq_app (f := y ≫ p) (U := ⊤))).symm
  have hq : y ≫ p = spMap (bmap (y ≫ p)) := (spMap_bmap _).symm
  have m2 : (y ≫ p).appTop = (spMap (bmap (y ≫ p))).appTop := by
    generalize bmap (y ≫ p) = β at hq
    rw [hq]
  have m3 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (bmap (y ≫ p)))
  have e1 : (y.appLE V ⊤ h).hom (constFn p V c) =
      (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (bmap (y ≫ p) c) := by
    have e2 : (y.appLE V ⊤ h).hom (constFn p V c) = (p.appLE ⊤ V le_top ≫ y.appLE V ⊤ h).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := rfl
    rw [e2, ← m1, m2]
    exact congrArg (fun m => m.hom c) m3.symm
  show (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom ((y.appLE V ⊤ h).hom (constFn p V c)) = _
  rw [e1]
  exact congrArg (fun m => m.hom (bmap (y ≫ p) c)) (Scheme.ΓSpecIso (CommRingCat.of C)).inv_hom_id

section Der

variable (v : epsAt (𝟙 (Sp R)) ⟶ G) (hv : IsTanAt G (𝟙 (Sp R)) v) {V : G.left.Opens} (hV : IsAffineOpen V)

def trV : Γ(G.left, V) →+* DualNumber Γ(G.left, V) :=
  ev (tr v (C := Γ(G.left, V)) hV.fromSpec) V (tr_top v hv _ V (from_top hV))

theorem fst_trV (g : Γ(G.left, V)) : (trV v hv hV g).fst = g := by
  have h1 := ev_comp (TrivSqZeroExt.fstHom Γ(G.left, V) Γ(G.left, V) Γ(G.left, V)).toRingHom
    (tr v (C := Γ(G.left, V)) hV.fromSpec) V (tr_top v hv _ V (from_top hV))
    (by rw [tr_fst v hv]; exact from_top hV) g
  rw [ev_congr (tr_fst v hv _) V _ (from_top hV), ev_fromSpec] at h1
  exact h1.symm

def der : Γ(G.left, V) →+ Γ(G.left, V) where
  toFun g := (trV v hv hV g).snd
  map_zero' := by simp
  map_add' a b := by simp

theorem der_apply (g : Γ(G.left, V)) : der v hv hV g = (trV v hv hV g).snd := rfl

theorem der_mul (a b : Γ(G.left, V)) : der v hv hV (a * b) = a * der v hv hV b + b * der v hv hV a := by
  simp only [der_apply, map_mul, TrivSqZeroExt.snd_mul, fst_trV, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  ring

theorem ev_tr {C : Type} [CommRing C] (y : Sp C ⟶ G.left) (h : ⊤ ≤ y ⁻¹ᵁ V) (h' : ⊤ ≤ (tr v y) ⁻¹ᵁ V) (g : Γ(G.left, V)) :
    ev (tr v y) V h' g = dualMap (ev y V h) (trV v hv hV g) := by
  have e : tr v y = spMap (dualMap (ev y V h)) ≫ tr v (C := Γ(G.left, V)) hV.fromSpec := by
    rw [← tr_comp, point_fac hV y h]
  rw [ev_congr e V h' (by rw [← e]; exact h')]
  exact ev_comp _ _ V (tr_top v hv _ V (from_top hV)) _ g

theorem snd_ev_tr {C : Type} [CommRing C] (y : Sp C ⟶ G.left) (h : ⊤ ≤ y ⁻¹ᵁ V) (h' : ⊤ ≤ (tr v y) ⁻¹ᵁ V)
    (g : Γ(G.left, V)) : (ev (tr v y) V h' g).snd = ev y V h (der v hv hV g) := by
  rw [ev_tr v hv hV y h h' g]
  simp [dualMap, der_apply]

theorem der_res {V' : G.left.Opens} (hV' : IsAffineOpen V') (le : V' ≤ V) (g : Γ(G.left, V)) :
    der v hv hV' ((G.left.presheaf.map (homOfLE le).op).hom g) =
      (G.left.presheaf.map (homOfLE le).op).hom (der v hv hV g) := by
  have hy : ⊤ ≤ hV'.fromSpec ⁻¹ᵁ V := fun p hp => le (from_top hV' hp)
  have h1 := snd_ev_tr v hv hV (C := Γ(G.left, V')) hV'.fromSpec hy (tr_top v hv _ V hy) g
  rw [← ev_res _ le (tr_top v hv _ V hy) (tr_top v hv _ V' (from_top hV'))] at h1
  rw [der_apply, trV, h1, ← ev_res _ le hy (from_top hV'), ev_fromSpec]

theorem tr_hom {C : Type} [CommRing C] (y : Sp C ⟶ G.left) :
    tr v y ≫ G.hom = spMap (algebraMap C (DualNumber C)) ≫ y ≫ G.hom :=
  Over.w ((piE (y ≫ G.hom) ≫ (Over.homMk y rfl : Over.mk (y ≫ G.hom) ⟶ G)) * (rhoE (y ≫ G.hom) ≫ v))

theorem der_const (c : R) : der v hv hV (constFn G.hom V c) = 0 := by
  have e : bmap (tr v (C := Γ(G.left, V)) hV.fromSpec ≫ G.hom) =
      (algebraMap Γ(G.left, V) (DualNumber Γ(G.left, V))).comp (bmap (hV.fromSpec ≫ G.hom)) := by
    rw [tr_hom]
    conv_lhs => rw [← spMap_bmap (hV.fromSpec ≫ G.hom)]
    rw [show spMap (algebraMap Γ(G.left, V) (DualNumber Γ(G.left, V))) ≫ spMap (bmap (hV.fromSpec ≫ G.hom)) =
      spMap ((algebraMap Γ(G.left, V) (DualNumber Γ(G.left, V))).comp (bmap (hV.fromSpec ≫ G.hom))) by
        simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp], bmap_spMap]
  rw [der_apply, trV, ev_const, e]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem der_const_mul (c : R) (g : Γ(G.left, V)) :
    der v hv hV (constFn G.hom V c * g) = constFn G.hom V c * der v hv hV g := by
  rw [der_mul, der_const, mul_zero, add_zero]

end Der

theorem jet_mul_of_vanish {B K : Type} [CommRing B] [CommRing K] (D : B →+ B)
    (hD : ∀ a b, D (a * b) = a * D b + b * D a) (e : B →+* K) (i : ℕ) :
    ∀ u a : B, (∀ k < i, e (D^[k] a) = 0) →
      e (D^[i] (u * a)) = e u * e (D^[i] a) := by
  induction i with
  | zero => intro u a _; simp
  | succ i ih =>
    intro u a h
    have h1 := ih u (D a) (fun k hk => by
      have := h (k + 1) (Nat.succ_lt_succ hk)
      rwa [Function.iterate_succ_apply] at this)
    have h2 := ih (D u) a (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have h3 : D^[i] (a * D u) = D^[i] (D u * a) := by rw [mul_comm]
    rw [Function.iterate_succ_apply, hD, iterate_map_add, map_add, h1, h3, h2, h i (Nat.lt_succ_self i), mul_zero, add_zero,
      Function.iterate_succ_apply]

theorem jet_vanish_of_mul {B K : Type} [CommRing B] [CommRing K] [IsDomain K] (D : B →+ B)
    (hD : ∀ a b, D (a * b) = a * D b + b * D a) (e : B →+* K) (u a : B) (hu : e u ≠ 0) (i : ℕ)
    (h : ∀ k < i, e (D^[k] (u * a)) = 0) : ∀ k < i, e (D^[k] a) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have h1 := jet_mul_of_vanish D hD e k u a (fun l hl => ih l hl (hl.trans hk))
    rw [h k hk] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hu

end GlobalTheory.CompanionTheory.Ar.InvDer
