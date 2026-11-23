import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsUnitAddMonoidAlgebraIffOfTwoUniqueSums

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (epsR IsLieBasis isMonHom_of_mul)
open scoped CategoryTheory.Obj
open AddMonoidAlgebra (single mapDomainAlgHom)

namespace GlobalTheory.TorusDefect

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.SqZero GlobalTheory.Diag

variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
  {C C' : Type} [CommRing C] [Algebra A C] [CommRing C'] [Algebra A C']

theorem algHom_ext' {φ ψ : AddMonoidAlgebra A X →ₐ[A] C}
    (h : ∀ x, φ (single x 1) = ψ (single x 1)) : φ = ψ := AddMonoidAlgebra.algHom_ext h (Subsingleton.elim _ _)

theorem charVal_spMap (φ : C →ₐ[A] C') (w : sp C ⟶ splitTorus (Spec (CommRingCat.of A)) X) (x : X) :
    charVal (spMap φ ≫ w) x = φ (charVal w x) := by
  refine (GlobalTheory.Diag.left_eq_iff (g := Spec.map (CommRingCat.ofHom (algebraMap A C))) φ.toRingHom ?_
    (spMap φ ≫ w) w).1 ?_ x
  · have h := Over.w (spMap φ)
    rw [spMap_left] at h
    exact h.symm
  · rw [Over.comp_left, spMap_left]

variable (A X) in

def univ : sp (AddMonoidAlgebra A X) ⟶ splitTorus (Spec (CommRingCat.of A)) X :=
  ofVal _ (AddMonoidAlgebra.of A X)

theorem charVal_univ (φ : AddMonoidAlgebra A X →ₐ[A] C) (x : X) :
    charVal (spMap φ ≫ univ A X) x = φ (single x 1) := by
  rw [charVal_spMap, univ, GlobalTheory.Diag.charVal_ofVal, AddMonoidAlgebra.of_apply, toAdd_ofAdd]

def valHom (w : sp C ⟶ splitTorus (Spec (CommRingCat.of A)) X) : Multiplicative X →* C where
  toFun x := charVal w x.toAdd
  map_one' := charVal_zero w
  map_mul' _ _ := charVal_add w _ _

theorem exists_eq_univ (w : sp C ⟶ splitTorus (Spec (CommRingCat.of A)) X) :
    ∃ φ : AddMonoidAlgebra A X →ₐ[A] C, spMap φ ≫ univ A X = w := by
  refine ⟨AddMonoidAlgebra.lift A C X (valHom w), GlobalTheory.Diag.charVal_ext fun x => ?_⟩
  rw [charVal_univ, AddMonoidAlgebra.lift_single, one_smul]
  rfl

theorem exists_eq_univ₂ (v w : sp C ⟶ splitTorus (Spec (CommRingCat.of A)) X) :
    ∃ φ : AddMonoidAlgebra A (X × X) →ₐ[A] C,
      spMap (φ.comp (mapDomainAlgHom A A (AddMonoidHom.inl X X))) ≫ univ A X = v ∧
      spMap (φ.comp (mapDomainAlgHom A A (AddMonoidHom.inr X X))) ≫ univ A X = w := by
  let F : Multiplicative (X × X) →* C :=
    (valHom v).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst X X)) *
      (valHom w).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd X X))
  refine ⟨AddMonoidAlgebra.lift A C (X × X) F, GlobalTheory.Diag.charVal_ext fun x => ?_,
    GlobalTheory.Diag.charVal_ext fun x => ?_⟩ <;>
  · rw [charVal_univ]
    simp [F, valHom, GlobalTheory.Diag.charVal_zero]

theorem univ_add (φ : AddMonoidAlgebra A Y →ₐ[A] C) (u v : X →+ Y) :
    spMap (φ.comp (mapDomainAlgHom A A (u + v))) ≫ univ A X =
      spMap (φ.comp (mapDomainAlgHom A A u)) ≫ univ A X *
        spMap (φ.comp (mapDomainAlgHom A A v)) ≫ univ A X := by
  refine GlobalTheory.Diag.charVal_ext fun x => ?_
  rw [GlobalTheory.Diag.charVal_mul, charVal_univ, charVal_univ, charVal_univ]
  simp only [AlgHom.comp_apply]
  rw [← map_mul]
  congr 1
  simp [AddMonoidAlgebra.single_mul_single]

theorem exists_affinization (Z : Over (Spec (CommRingCat.of A))) :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (p : Z ⟶ sp C),
      (∀ a : Z ⟶ splitTorus (Spec (CommRingCat.of A)) X, ∃ a', p ≫ a' = a) ∧
      ∀ (J : Ideal A) (s : Z.left ⟶ Spec (CommRingCat.of (A ⧸ J))),
        Z.hom = s ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) →
        ∀ j ∈ J, algebraMap A C j = 0 := by
  let inst : Algebra A Γ(Z.left, ⊤) :=
    (Z.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).toAlgebra
  have e : CommRingCat.ofHom (algebraMap A Γ(Z.left, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ Z.hom.appTop := rfl
  have hw : Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap A Γ(Z.left, ⊤))) = Z.hom := by
    rw [e, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  refine ⟨Γ(Z.left, ⊤), inferInstance, inst, Over.homMk Z.left.toSpecΓ hw, ?_, ?_⟩
  · intro a
    let F : Multiplicative X →* Γ(Z.left, ⊤) :=
      { toFun := fun x => SplitTorus.val a x.toAdd
        map_one' := SplitTorus.val_zero a
        map_mul' := fun x y => SplitTorus.val_add a x.toAdd y.toAdd }
    refine ⟨GlobalTheory.Diag.ofVal _ F, SplitTorus.hom_ext fun x => ?_⟩
    have h1 := GlobalTheory.Diag.charVal_ofVal
      (g := Spec.map (CommRingCat.ofHom (algebraMap A Γ(Z.left, ⊤)))) F x
    unfold GlobalTheory.Diag.charVal at h1
    rw [SplitTorus.val_comp, SplitTorus.val_eq]
    change (Z.left.toSpecΓ.appTop).hom _ = _
    rw [Scheme.toSpecΓ_appTop]
    exact h1
  · intro J s hs j hj
    show Z.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom j) = 0
    rw [hs, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
      SplitTorus.specMap_appTop_apply, CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.2 hj,
      map_zero, map_zero]

theorem exists_inv_univ : ∃ r : splitTorus (Spec (CommRingCat.of A)) X ⟶ sp (AddMonoidAlgebra A X),
    r ≫ univ A X = 𝟙 _ ∧ univ A X ≫ r = 𝟙 _ := by
  obtain ⟨C, _, _, p, hp, -⟩ := exists_affinization (A := A) (X := X) (splitTorus (Spec (CommRingCat.of A)) X)
  obtain ⟨a', ha'⟩ := hp (𝟙 _)
  obtain ⟨φ, hφ⟩ := exists_eq_univ a'
  refine ⟨p ≫ spMap φ, by rw [Category.assoc, hφ, ha'], ?_⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SqZero.exists_spMap (univ A X ≫ p ≫ spMap φ)
  have h1 : spMap α ≫ univ A X = spMap (AlgHom.id A (AddMonoidAlgebra A X)) ≫ univ A X := by
    rw [spMap_id, Category.id_comp, ← hα, Category.assoc, Category.assoc, hφ, ha', Category.comp_id]
  have h2 : α = AlgHom.id A _ := algHom_ext' fun x => by
    have h3 := congrArg (fun w => charVal w x) h1
    simpa only [charVal_univ] using h3
  rw [hα, h2, spMap_id]

theorem mul_comp_of_pullback {S S' : Scheme.{0}} (i : S' ⟶ S) {G H : Over S} [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom ((Over.pullback i).map f)] {W : Scheme.{0}} (s : W ⟶ S') (z : W ⟶ S)
    (hz : z = s ≫ i) (a b : Over.mk z ⟶ G) : (a * b) ≫ f = a ≫ f * b ≫ f := by
  subst hz
  obtain ⟨a', ha'⟩ : ∃ a' : Over.mk s ⟶ (Over.pullback i).obj G,
      a'.left ≫ pullback.fst G.hom i = a.left :=
    ⟨Over.homMk (pullback.lift a.left s (Over.w a)) (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩
  obtain ⟨b', hb'⟩ : ∃ b' : Over.mk s ⟶ (Over.pullback i).obj G,
      b'.left ≫ pullback.fst G.hom i = b.left :=
    ⟨Over.homMk (pullback.lift b.left s (Over.w b)) (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩
  have hpf : ((Over.pullback i).map f).left ≫ pullback.fst H.hom i = pullback.fst G.hom i ≫ f.left :=
    pullback.lift_fst _ _ _
  have h1 := SplitTorus.mul_left_comp_fst G i a' b' a b ha'.symm hb'.symm
  have h2 := SplitTorus.mul_left_comp_fst H i (a' ≫ (Over.pullback i).map f)
    (b' ≫ (Over.pullback i).map f) (a ≫ f) (b ≫ f)
    (by rw [Over.comp_left, Over.comp_left, Category.assoc, hpf, ← Category.assoc, ha'])
    (by rw [Over.comp_left, Over.comp_left, Category.assoc, hpf, ← Category.assoc, hb'])
  apply Over.OverMorphism.ext
  rw [h2, ← MonObj.mul_comp, Over.comp_left, Over.comp_left, Category.assoc, hpf, ← Category.assoc,
    ← h1]

theorem mem_map_iff (J : Ideal A) (b : AddMonoidAlgebra A X) :
    b ∈ J.map (algebraMap A (AddMonoidAlgebra A X)) ↔ ∀ x, b.coeff x ∈ J := by
  constructor
  · intro hb x
    have h0 : b ∈ RingHom.ker (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk J)) := by
      refine (Ideal.map_le_iff_le_comap.2 ?_) hb
      intro a ha
      simp [AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.mapRingHom_single,
        Ideal.Quotient.eq_zero_iff_mem, ha]
    have h1 := congrArg (fun c => c.coeff x) (RingHom.mem_ker.1 h0)
    simpa [AddMonoidAlgebra.coeff_mapRingHom, Ideal.Quotient.eq_zero_iff_mem] using h1
  · intro hb
    rw [← AddMonoidAlgebra.sum_coeff_single b, Finsupp.sum]
    refine Ideal.sum_mem _ fun x _ => ?_
    have hx : single x (b.coeff x) =
        algebraMap A (AddMonoidAlgebra A X) (b.coeff x) * single x 1 := by
      rw [← Algebra.smul_def, AddMonoidAlgebra.smul_single', _root_.mul_one]
    rw [hx]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hb x))

theorem map_mem_map {J : Ideal A} (φ : C →ₐ[A] C') :
    ∀ a ∈ J.map (algebraMap A C), φ a ∈ J.map (algebraMap A C') := fun a ha => by
  have h := Ideal.mem_map_of_mem (φ : C →+* C') ha
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at h

theorem map_algebraMap_sq {J : Ideal A} (hJ : J ^ 2 = ⊥) : J.map (algebraMap A C) ^ 2 = ⊥ := by rw [← Ideal.map_pow, hJ, Ideal.map_bot]

section Cocycle

variable {G : Over (Spec (CommRingCat.of A))} [GrpObj G] {J : Ideal A}
  {Z : Type} [AddCommGroup Z]

def pull (G : Over (Spec (CommRingCat.of A))) [GrpObj G] (u : X →+ Y) :
    (sp (AddMonoidAlgebra A X) ⟶ G) →* (sp (AddMonoidAlgebra A Y) ⟶ G) :=
  pointsMap G (mapDomainAlgHom A A u)

theorem pull_pull (u : X →+ Y) (v : Y →+ Z) (y : sp (AddMonoidAlgebra A X) ⟶ G) :
    pull G v (pull G u y) = pull G (v.comp u) y := by
  rw [pull, pull, pull, ptsMap_apply, ptsMap_apply, ptsMap_apply, ← Category.assoc, spMap_comp,
    AddMonoidAlgebra.mapDomainAlgHom_comp]

def pullKer (G : Over (Spec (CommRingCat.of A))) [GrpObj G] (J : Ideal A) (u : X →+ Y) :
    redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A X))) →*
      redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A Y))) :=
  ((pull G u).comp (Subgroup.subtype _)).codRestrict _ fun y =>
    comp_mem_redKer y.2 _ (map_mem_map _)

theorem coe_pullKer (u : X →+ Y)
    (y : redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A X)))) :
    (pullKer G J u y).1 = pull G u y.1 := rfl

variable [IsCommMonObj G] [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR A ⟶ G)}

theorem kerEquiv_pullKer (hv : IsLieBasis v) (hJ : J ^ 2 = ⊥) (u : X →+ Y)
    (y : redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A X)))) (i : Fin n) :
    (kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul (pullKer G J u y)) i :
      AddMonoidAlgebra A Y) =
      AddMonoidAlgebra.mapDomain u (kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul y) i :
        AddMonoidAlgebra A X) := by
  have h := kerEquiv_map hv (map_algebraMap_sq hJ) (map_algebraMap_sq hJ) (mapDomainAlgHom A A u)
    (map_mem_map _) y i
  have e : pullKer G J u y = ⟨spMap (mapDomainAlgHom A A u) ≫ y.1,
      comp_mem_redKer y.2 (mapDomainAlgHom A A u) (map_mem_map _)⟩ := Subtype.ext (coe_pullKer u y)
  rw [e, h]
  simp

open AddMonoidHom in

theorem exists_coboundary (hv : IsLieBasis v) (hJ : J ^ 2 = ⊥)
    (δ : redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A (X × X)))))
    (hδ : pullKer G J (inr X (X × X)) δ / pullKer G J ((AddMonoidHom.fst X X).prod (AddMonoidHom.id _)) δ *
      pullKer G J ((AddMonoidHom.fst X X).prod ((AddMonoidHom.snd X X).prod (AddMonoidHom.snd X X))) δ /
      pullKer G J (prodMap (AddMonoidHom.id X) (inl X X)) δ = 1) :
    ∃ κ : redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A X))),
      pullKer G J (inr X X) κ / pullKer G J (inl X X + inr X X) κ * pullKer G J (inl X X) κ = δ := by
  set f : Fin n → AddMonoidAlgebra A (X × X) :=
    fun i => ((kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul δ) i : AddMonoidAlgebra A (X × X))) with hf
  have hcoc : ∀ i, AddMonoidAlgebra.mapDomain (fun p : X × X => ((0 : X), p.1, p.2)) (f i) -
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.1, p.2)) (f i) +
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, p.2)) (f i) -
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, (0 : X))) (f i) = 0 := by
    intro i
    have h := congrArg (fun z => ((kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul z) i :
      AddMonoidAlgebra A (X × (X × X))))) hδ
    simp only [ofMul_div, ofMul_mul, ofMul_one, map_sub, map_add, map_zero, Pi.sub_apply,
      Pi.add_apply, Pi.zero_apply, AddSubgroupClass.coe_sub, AddMemClass.coe_add,
      ZeroMemClass.coe_zero] at h
    rw [kerEquiv_pullKer hv hJ, kerEquiv_pullKer hv hJ, kerEquiv_pullKer hv hJ,
      kerEquiv_pullKer hv hJ] at h
    exact h
  have key : ∀ i, ∃ g : AddMonoidAlgebra A X,
      AddMonoidAlgebra.mapDomain (fun y : X => ((0 : X), y)) g -
        AddMonoidAlgebra.mapDomain (fun y : X => (y, y)) g +
        AddMonoidAlgebra.mapDomain (fun y : X => (y, (0 : X))) g = f i :=
    fun i => (addMonoidAlgebra_existsUnique_coboundary (f i) (hcoc i)).exists
  choose g hg using key
  have hmem : ∀ i, g i ∈ J.map (algebraMap A (AddMonoidAlgebra A X)) := by
    intro i
    rw [mem_map_iff]
    intro x
    rw [(addMonoidAlgebra_coboundary_eq_iff (f i) (hcoc i) (g i)).1 (hg i) x]
    exact (mem_map_iff J (f i)).1 (kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul δ) i).2 (0, x)
  refine ⟨Additive.toMul ((kerEquiv hv (map_algebraMap_sq hJ)).symm fun i => ⟨g i, hmem i⟩), ?_⟩
  apply Additive.ofMul.injective
  apply (kerEquiv hv (map_algebraMap_sq hJ)).injective
  funext i
  apply Subtype.ext
  have e2 : (⇑(AddMonoidHom.inl X X + AddMonoidHom.inr X X) : X → X × X) = fun y => (y, y) :=
    funext fun y => by simp
  simp only [ofMul_div, ofMul_mul, map_sub, map_add, Pi.sub_apply, Pi.add_apply,
    AddSubgroupClass.coe_sub, AddMemClass.coe_add]
  rw [kerEquiv_pullKer hv hJ, kerEquiv_pullKer hv hJ, kerEquiv_pullKer hv hJ]
  simp only [ofMul_toMul, AddEquiv.apply_symm_apply, e2]
  exact hg i

open AddMonoidHom in

theorem exists_correction (hv : IsLieBasis v) (hJ : J ^ 2 = ⊥) (h : sp (AddMonoidAlgebra A X) ⟶ G)
    (hh : pull G (inr X X) h / pull G (inl X X + inr X X) h * pull G (inl X X) h ∈
      redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A (X × X))))) :
    ∃ κ ∈ redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A X))),
      pull G (inl X X + inr X X) (h / κ) = pull G (inl X X) (h / κ) * pull G (inr X X) (h / κ) := by
  have e1 : ((AddMonoidHom.fst X X).prod (AddMonoidHom.id (X × X))).comp (AddMonoidHom.inr X X) =
      (AddMonoidHom.inr X (X × X)).comp (AddMonoidHom.inr X X) := AddMonoidHom.ext fun y => by simp
  have e2 : ((AddMonoidHom.fst X X).prod ((AddMonoidHom.snd X X).prod (AddMonoidHom.snd X X))).comp
      (AddMonoidHom.inr X X) = (AddMonoidHom.inr X (X × X)).comp
        (AddMonoidHom.inl X X + AddMonoidHom.inr X X) := AddMonoidHom.ext fun y => by simp
  have e3 : (prodMap (AddMonoidHom.id X) (AddMonoidHom.inl X X)).comp (AddMonoidHom.inr X X) =
      (AddMonoidHom.inr X (X × X)).comp (AddMonoidHom.inl X X) := AddMonoidHom.ext fun y => by simp
  have e4 : ((AddMonoidHom.fst X X).prod ((AddMonoidHom.snd X X).prod (AddMonoidHom.snd X X))).comp
      (AddMonoidHom.inl X X + AddMonoidHom.inr X X) =
      ((AddMonoidHom.fst X X).prod (AddMonoidHom.id (X × X))).comp
        (AddMonoidHom.inl X X + AddMonoidHom.inr X X) := AddMonoidHom.ext fun y => by simp
  have e5 : (prodMap (AddMonoidHom.id X) (AddMonoidHom.inl X X)).comp
      (AddMonoidHom.inl X X + AddMonoidHom.inr X X) =
      ((AddMonoidHom.fst X X).prod (AddMonoidHom.id (X × X))).comp (AddMonoidHom.inl X X) :=
    AddMonoidHom.ext fun y => by simp
  have e6 : (prodMap (AddMonoidHom.id X) (AddMonoidHom.inl X X)).comp (AddMonoidHom.inl X X) =
      ((AddMonoidHom.fst X X).prod ((AddMonoidHom.snd X X).prod (AddMonoidHom.snd X X))).comp
        (AddMonoidHom.inl X X) := AddMonoidHom.ext fun y => by simp
  obtain ⟨κ, hκ⟩ := exists_coboundary hv hJ ⟨_, hh⟩ (by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_div, Subgroup.coe_one, coe_pullKer, map_mul, map_div,
      pull_pull]
    rw [e1, e2, e3, e4, e5, e6]
    apply Additive.ofMul.injective
    simp only [ofMul_div, ofMul_mul, ofMul_one]
    abel)
  refine ⟨κ.1, κ.2, ?_⟩
  have h1 := congrArg (fun z => Additive.ofMul (Subtype.val z)) hκ
  simp only [Subgroup.coe_mul, Subgroup.coe_div, coe_pullKer, ofMul_div, ofMul_mul] at h1
  rw [map_div, map_div, map_div]
  apply Additive.ofMul.injective
  simp only [ofMul_div, ofMul_mul]
  rw [← sub_eq_zero] at h1 ⊢
  rw [← h1]
  abel

end Cocycle

end GlobalTheory.TorusDefect

namespace GlobalTheory

open SqZero TorusDefect

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_isMonHom_splitTorus_of_sq_eq_bot (A : Type) [CommRing A] [IsLocalRing A]
    (J : Ideal A) (hJ : J ^ 2 = ⊥) (X : Type) [AddCommGroup X]
    (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G)
    (hf : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f)) :
    ∃ f' : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, IsMonHom f' ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f' =
        (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f := by
  have hL : ∃ (n : ℕ) (v : Fin n → (epsR A ⟶ G)), IsLieBasis v :=
    ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis G inferInstance
  obtain ⟨r, hr1, hr2⟩ := TorusDefect.exists_inv_univ (A := A) (X := X)
  obtain ⟨n, v, hv⟩ := hL
  have hur : ∀ {W : Over (Spec (CommRingCat.of A))} (q : sp (AddMonoidAlgebra A X) ⟶ W),
      univ A X ≫ r ≫ q = q := fun q => by rw [← Category.assoc, hr2, Category.id_comp]

  have hh : pull G (AddMonoidHom.inr X X) (univ A X ≫ f) /
      pull G (AddMonoidHom.inl X X + AddMonoidHom.inr X X) (univ A X ≫ f) *
      pull G (AddMonoidHom.inl X X) (univ A X ≫ f) ∈
      redKer G (J.map (algebraMap A (AddMonoidAlgebra A (X × X)))) := by
    rw [mem_redKer]
    have hx : ∀ u : X →+ X × X,
        spMap (Ideal.Quotient.mkₐ A (J.map (algebraMap A (AddMonoidAlgebra A (X × X))))) ≫
          pull G u (univ A X ≫ f) =
        (spMap ((Ideal.Quotient.mkₐ A (J.map (algebraMap A (AddMonoidAlgebra A (X × X))))).comp
          (mapDomainAlgHom A A u)) ≫ univ A X) ≫ f := fun u => by
      rw [pull, ptsMap_apply, ← Category.assoc, spMap_comp, Category.assoc]
    have hz : Spec.map (CommRingCat.ofHom (algebraMap A
        (AddMonoidAlgebra A (X × X) ⧸ J.map (algebraMap A (AddMonoidAlgebra A (X × X)))))) =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap
          (J.map (algebraMap A (AddMonoidAlgebra A (X × X)))) (algebraMap A _) Ideal.le_comap_map)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    rw [MonObj.comp_mul, GrpObj.comp_div, hx, hx, hx, univ_add,
      mul_comp_of_pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) f _ _ hz]
    apply Additive.ofMul.injective
    simp only [ofMul_div, ofMul_mul, ofMul_one]
    abel
  obtain ⟨κ, hκ, hmul⟩ := TorusDefect.exists_correction hv hJ (univ A X ≫ f) hh
  have hpull : ∀ {C : Type} [CommRing C] [Algebra A C] (φ : AddMonoidAlgebra A (X × X) →ₐ[A] C)
      (u : X →+ X × X), spMap (φ.comp (mapDomainAlgHom A A u)) ≫ (univ A X ≫ f / κ) =
        spMap φ ≫ pull G u (univ A X ≫ f / κ) := fun φ u => by
    rw [pull, ptsMap_apply, ← Category.assoc, spMap_comp]
  refine ⟨r ≫ (univ A X ≫ f / κ), ?_, ?_⟩
  · refine isMonHom_of_mul _ fun T x y => ?_
    obtain ⟨C, _, _, p, hp, -⟩ := TorusDefect.exists_affinization (X := X) T
    obtain ⟨x', rfl⟩ := hp x
    obtain ⟨y', rfl⟩ := hp y
    obtain ⟨φ, rfl, rfl⟩ := TorusDefect.exists_eq_univ₂ x' y'
    rw [← MonObj.comp_mul, ← univ_add]
    simp only [Category.assoc, hur]
    rw [← MonObj.comp_mul, hpull, hpull, hpull, hmul]
    congr 1
    exact MonObj.comp_mul _ _ _
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst]
      obtain ⟨a, ha⟩ : ∃ a : Over.mk (pullback.snd (splitTorus (Spec (CommRingCat.of A)) X).hom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⟶ splitTorus (Spec (CommRingCat.of A)) X,
          a.left = pullback.fst _ _ := ⟨Over.homMk _ pullback.condition, rfl⟩
      obtain ⟨C, _, _, p, hp, hJC⟩ := TorusDefect.exists_affinization (X := X) (Over.mk
        (pullback.snd (splitTorus (Spec (CommRingCat.of A)) X).hom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
      obtain ⟨a', ha'⟩ := hp a
      obtain ⟨ψ, hψ⟩ := TorusDefect.exists_eq_univ a'
      have hle : J.map (algebraMap A (AddMonoidAlgebra A X)) ≤ RingHom.ker (ψ : AddMonoidAlgebra A X →+* C) :=
        Ideal.map_le_iff_le_comap.2 fun j hj => by
          show ψ (algebraMap A _ j) = 0
          rw [AlgHom.commutes]
          exact hJC J _ rfl j hj
      have hκ0 : spMap ψ ≫ κ = 1 :=
        comp_eq_one_of_mem_redKer hκ ψ fun b hb => RingHom.mem_ker.1 (hle hb)
      have E : a ≫ r ≫ (univ A X ≫ f / κ) = a ≫ f := by
        rw [← ha', ← hψ]
        simp only [Category.assoc, hur]
        rw [GrpObj.comp_div, hκ0, div_one]
      rw [← ha, ← Over.comp_left, ← Over.comp_left, E]
    · simp only [Over.pullback_map_left, pullback.lift_snd]

end GlobalTheory
