import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace TorusNil

variable {A : Type} [CommRing A]

abbrev sp (A C : Type) [CommRing A] [CommRing C] [Algebra A C] : Over (Spec (CommRingCat.of A)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A C)))

def spm {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D] (φ : C →ₐ[A] D) :
    sp A D ⟶ sp A C :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    simp only [Over.mk_left, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a; simp)

section
variable {C D E : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
  [CommRing E] [Algebra A E]

theorem spm_left (φ : C →ₐ[A] D) : (spm φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

theorem spm_comp (φ : C →ₐ[A] D) (ψ : D →ₐ[A] E) : spm (ψ.comp φ) = spm ψ ≫ spm φ := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, spm_left, spm_left, spm_left]
  exact (Spec.map_comp (CommRingCat.ofHom φ.toRingHom) (CommRingCat.ofHom ψ.toRingHom))

theorem spm_injective {φ ψ : C →ₐ[A] D} (h : spm φ = spm ψ) : φ = ψ := by
  have h1 := Spec.map_injective (congrArg CommaMorphism.left h)
  ext a
  exact congrArg (fun g : CommRingCat.of C ⟶ CommRingCat.of D => g.hom a) h1

theorem spm_surjective (g : sp A D ⟶ sp A C) : ∃ φ : C →ₐ[A] D, spm φ = g := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of C) (S := CommRingCat.of D) g.left
  have hw : CommRingCat.ofHom (algebraMap A C) ≫ φ = CommRingCat.ofHom (algebraMap A D) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ]
    exact Over.w g
  refine ⟨⟨φ.hom, fun a => congrArg
    (fun g : CommRingCat.of A ⟶ CommRingCat.of D => g.hom a) hw⟩, ?_⟩
  apply Over.OverMorphism.ext
  exact hφ

theorem spm_left_surjective (π : C →ₐ[A] D) (hs : Function.Surjective π)
    (hn : ∀ x, π x = 0 → IsNilpotent x) : Function.Surjective (spm π).left := by
  have h := range_comap_of_surjective D π.toRingHom hs
  have h2 : PrimeSpectrum.zeroLocus (RingHom.ker π.toRingHom : Set C) = Set.univ := by
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    exact hn x hx
  rw [h2, Set.range_eq_univ] at h
  exact h

end

def triples (A : Type) [CommRing A] {C : Type} [CommRing C] [Algebra A C] (K : Ideal C) :
    Subalgebra A (C × C × C) where
  carrier := {t | t.1 - t.2.2 ∈ K ∧ t.2.1 - t.2.2 ∈ K}
  mul_mem' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
    simp only [Set.mem_setOf_eq, Prod.mk_mul_mk] at *
    constructor
    · have : a * a' - c * c' = a * (a' - c') + c' * (a - c) := by ring
      rw [this]; exact K.add_mem (K.mul_mem_left _ h3) (K.mul_mem_left _ h1)
    · have : b * b' - c * c' = b * (b' - c') + c' * (b - c) := by ring
      rw [this]; exact K.add_mem (K.mul_mem_left _ h4) (K.mul_mem_left _ h2)
  add_mem' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
    simp only [Set.mem_setOf_eq, Prod.mk_add_mk] at *
    constructor
    · have : a + a' - (c + c') = (a - c) + (a' - c') := by ring
      rw [this]; exact K.add_mem h1 h3
    · have : b + b' - (c + c') = (b - c) + (b' - c') := by ring
      rw [this]; exact K.add_mem h2 h4
  algebraMap_mem' r := by simp

section
variable {C : Type} [CommRing C] [Algebra A C] (K : Ideal C)

def tr₁ : triples A K →ₐ[A] C := (AlgHom.fst A C (C × C)).comp (triples A K).val

def tr₂ : triples A K →ₐ[A] C :=
  (AlgHom.fst A C C).comp ((AlgHom.snd A C (C × C)).comp (triples A K).val)

def tr₃ : triples A K →ₐ[A] C :=
  (AlgHom.snd A C C).comp ((AlgHom.snd A C (C × C)).comp (triples A K).val)

def trSum : triples A K →ₐ[A] C ⧸ K ^ 2 where
  toFun t := Ideal.Quotient.mk _ (t.1.1 + t.1.2.1 - t.1.2.2)
  map_one' := by simp
  map_zero' := by simp
  map_add' s t := by
    rw [← map_add]; congr 1
    simp only [Subalgebra.coe_add, Prod.fst_add, Prod.snd_add]; ring
  map_mul' := by
    rintro ⟨⟨a, b, c⟩, h1, h2⟩ ⟨⟨a', b', c'⟩, h3, h4⟩
    rw [← map_mul, Ideal.Quotient.eq]
    change a * a' + b * b' - c * c' - (a + b - c) * (a' + b' - c') ∈ K ^ 2
    have : a * a' + b * b' - c * c' - (a + b - c) * (a' + b' - c') =
      -((a - c) * (b' - c') + (b - c) * (a' - c')) := by ring
    rw [this, sq]
    exact neg_mem (add_mem (Ideal.mul_mem_mul h1 h4) (Ideal.mul_mem_mul h2 h3))
  commutes' r := by simp [← Ideal.Quotient.mk_algebraMap]

end

section
variable {B : Over (Spec (CommRingCat.of A))} [GrpObj B] {R : Type} [CommRing R] [Algebra A R]
  (j : sp A R ⟶ B) [IsOpenImmersion j.left] (ε : R →ₐ[A] A) (hε : spm ε ≫ j = 1)

omit [GrpObj B] in
theorem pt_injective {C : Type} [CommRing C] [Algebra A C] {φ ψ : R →ₐ[A] C}
    (h : spm φ ≫ j = spm ψ ≫ j) : φ = ψ := by
  apply spm_injective
  apply Over.OverMorphism.ext
  rw [← cancel_mono j.left, ← Over.comp_left, h, Over.comp_left]

omit [IsOpenImmersion j.left] in
include hε in
theorem pt_one (C : Type) [CommRing C] [Algebra A C] :
    spm ((Algebra.ofId A C).comp ε) ≫ j = 1 := by
  rw [spm_comp, Category.assoc, hε, MonObj.comp_one]

include hε in

theorem exists_pt {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
    (π : C →ₐ[A] D) (hs : Function.Surjective π) (hn : ∀ x, π x = 0 → IsNilpotent x)
    (g : sp A C ⟶ B) (hg : spm π ≫ g = 1) : ∃ φ : R →ₐ[A] C, spm φ ≫ j = g := by
  have hr : Set.range g.left ⊆ Set.range j.left := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := spm_left_surjective π hs hn x
    rw [← pt_one j ε hε D] at hg
    refine ⟨(spm ((Algebra.ofId A D).comp ε)).left y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, hg]
  obtain ⟨φ, hφ⟩ := spm_surjective (C := R) (D := C)
    (Over.homMk (IsOpenImmersion.lift j.left g.left hr) (by
      rw [← Over.w j, IsOpenImmersion.lift_fac_assoc, Over.w g]))
  refine ⟨φ, ?_⟩
  rw [hφ]
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

include hε in

theorem mul_pt {C : Type} [CommRing C] [Algebra A C] (K : Ideal C) (hK : ∀ x ∈ K, IsNilpotent x)
    (φ₁ φ₂ φ : R →ₐ[A] C) (h₁ : ∀ a, φ₁ a - algebraMap A C (ε a) ∈ K)
    (h₂ : ∀ a, φ₂ a - algebraMap A C (ε a) ∈ K)
    (h : (spm φ₁ ≫ j) * (spm φ₂ ≫ j) = spm φ ≫ j) (a : R) :
    φ a - (φ₁ a + φ₂ a - algebraMap A C (ε a)) ∈ K ^ 2 := by
  set e : R →ₐ[A] C := (Algebra.ofId A C).comp ε with he
  have he1 : spm e ≫ j = 1 := pt_one j ε hε C
  let G₁ : R →ₐ[A] triples A K := (φ₁.prod (e.prod e)).codRestrict _
    (fun a => ⟨h₁ a, by simp⟩)
  let G₂ : R →ₐ[A] triples A K := (e.prod (φ₂.prod e)).codRestrict _
    (fun a => ⟨by simp, h₂ a⟩)
  have key : ∀ {D : Type} [CommRing D] [Algebra A D] (p : triples A K →ₐ[A] D),
      spm p ≫ ((spm G₁ ≫ j) * (spm G₂ ≫ j)) =
        (spm (p.comp G₁) ≫ j) * (spm (p.comp G₂) ≫ j) := by
    intro D _ _ p
    rw [MonObj.comp_mul, spm_comp, spm_comp, Category.assoc, Category.assoc]
  have k3 : spm (tr₃ K) ≫ ((spm G₁ ≫ j) * (spm G₂ ≫ j)) = 1 := by
    rw [key]
    change (spm e ≫ j) * (spm e ≫ j) = 1
    rw [he1, _root_.mul_one]
  obtain ⟨Ψ, hΨ⟩ := exists_pt j ε hε (tr₃ K) (fun c => ⟨⟨(c, c, c), by simp, by simp⟩, rfl⟩)
    (by
      rintro ⟨⟨x, y, z⟩, hx, hy⟩ h0
      obtain rfl : z = 0 := h0
      obtain ⟨n, hn⟩ := hK x (by simpa using hx)
      obtain ⟨m, hm⟩ := hK y (by simpa using hy)
      refine ⟨n + m + 1, Subtype.ext ?_⟩
      simp [pow_add, hn, hm]) _ k3
  rw [← hΨ] at key k3
  have e3 : (tr₃ K).comp Ψ = e := pt_injective j (by
    rw [spm_comp, Category.assoc, k3, he1])
  have e1 : (tr₁ K).comp Ψ = φ₁ := pt_injective j (by
    rw [spm_comp, Category.assoc, key]
    change (spm φ₁ ≫ j) * (spm e ≫ j) = _
    rw [he1, _root_.mul_one])
  have e2 : (tr₂ K).comp Ψ = φ₂ := pt_injective j (by
    rw [spm_comp, Category.assoc, key]
    change (spm e ≫ j) * (spm φ₂ ≫ j) = _
    rw [he1, _root_.one_mul])
  have s1 : (trSum K).comp G₁ = (Ideal.Quotient.mkₐ A (K ^ 2)).comp φ₁ := by
    ext a
    change Ideal.Quotient.mk _ (φ₁ a + e a - e a) = Ideal.Quotient.mk _ (φ₁ a)
    rw [add_sub_cancel_right]
  have s2 : (trSum K).comp G₂ = (Ideal.Quotient.mkₐ A (K ^ 2)).comp φ₂ := by
    ext a
    change Ideal.Quotient.mk _ (e a + φ₂ a - e a) = Ideal.Quotient.mk _ (φ₂ a)
    rw [add_sub_cancel_left]
  have e4 : (Ideal.Quotient.mkₐ A (K ^ 2)).comp φ = (trSum K).comp Ψ := pt_injective j (by
    rw [spm_comp Ψ, Category.assoc, key, s1, s2, spm_comp, spm_comp, spm_comp, Category.assoc,
      Category.assoc, Category.assoc, ← MonObj.comp_mul, h])
  rw [← Ideal.Quotient.eq]
  refine (AlgHom.congr_fun e4 a).trans ?_
  rw [← e1, ← e2]
  have := AlgHom.congr_fun e3 a
  change _ = Ideal.Quotient.mk _ (_ - e a)
  rw [← this]
  rfl

end

theorem pullback_map_fst {S S' : Scheme.{0}} {p : S' ⟶ S} {Z : Over S'} {V W : Over S}
    (u : Z ⟶ (Over.pullback p).obj V) (f : V ⟶ W) :
    (u ≫ (Over.pullback p).map f).left ≫ pullback.fst W.hom p =
      u.left ≫ pullback.fst V.hom p ≫ f.left := by
  rw [Over.comp_left]
  refine (Category.assoc _ _ _).trans (congrArg (u.left ≫ ·) ?_)
  exact pullback.lift_fst _ _ _

theorem comp_eq_of_pullback_map_eq {S S' : Scheme.{0}} {p : S' ⟶ S} {Z V W : Over S}
    {f g : V ⟶ W} (h : (Over.pullback p).map f = (Over.pullback p).map g) (t : Z ⟶ V)
    (s : Z.left ⟶ S') (hs : s ≫ p = Z.hom) : t ≫ f = t ≫ g := by
  let u : Over.mk s ⟶ (Over.pullback p).obj V :=
    Over.homMk (pullback.lift t.left s ((Over.w t).trans hs.symm)) (pullback.lift_snd _ _ _)
  have hu : u.left ≫ pullback.fst V.hom p = t.left := pullback.lift_fst _ _ _
  have h1 := pullback_map_fst u f
  have h2 := pullback_map_fst u g
  rw [h, h2] at h1
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, ← hu]
  exact (Category.assoc _ _ _).trans (h1.symm.trans (Category.assoc _ _ _).symm)

section
variable (A) (X : Type) [AddCommGroup X]

def torusPt {C : Type} [CommRing C] [Algebra A C] (χ : Multiplicative X →* C) :
    sp A C ⟶ splitTorus (Spec (CommRingCat.of A)) X :=
  letI : Algebra (ULift.{0} ℤ) C := ULift.algebra' ℤ C
  (Over.homMk (V := (Over.pullback (toZ (Spec (CommRingCat.of A)))).obj
      ((Spec (CommRingCat.of C)).asOver (Spec (CommRingCat.of (ULift.{0} ℤ)))))
    (pullback.lift (𝟙 _) (sp A C).hom (specULiftZIsTerminal.hom_ext _ _))
      (pullback.lift_snd _ _ _)) ≫
    (Over.pullback (toZ (Spec (CommRingCat.of A)))).map
      (Spec.mapMulEquiv (R := ULift.{0} ℤ) (S := AddMonoidAlgebra (ULift.{0} ℤ) X) (T := C)
        (WithConv.toConv (AddMonoidAlgebra.lift (ULift.{0} ℤ) C X χ)))

theorem torusPt_mul {C : Type} [CommRing C] [Algebra A C] (χ χ' : Multiplicative X →* C) :
    torusPt A X (χ * χ') = torusPt A X χ * torusPt A X χ' := by
  letI : Algebra (ULift.{0} ℤ) C := ULift.algebra' ℤ C
  have h : WithConv.toConv (AddMonoidAlgebra.lift (ULift.{0} ℤ) C X (χ * χ')) =
      WithConv.toConv (AddMonoidAlgebra.lift (ULift.{0} ℤ) C X χ) *
        WithConv.toConv (AddMonoidAlgebra.lift (ULift.{0} ℤ) C X χ') := by
    apply WithConv.ofConv_injective
    ext x
    simp
  unfold torusPt
  rw [h, map_mul, Functor.map_mul]
  exact MonObj.comp_mul _ _ _

theorem torusPt_fst {C : Type} [CommRing C] [Algebra A C] (χ : Multiplicative X →* C) :
    ∃ φ : AddMonoidAlgebra (ULift.{0} ℤ) X →+* C,
      (∀ x, φ (AddMonoidAlgebra.single x 1) = χ (Multiplicative.ofAdd x)) ∧
      (torusPt A X χ).left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ _) =
        Spec.map (CommRingCat.ofHom φ) := by
  letI : Algebra (ULift.{0} ℤ) C := ULift.algebra' ℤ C
  refine ⟨(AddMonoidAlgebra.lift (ULift.{0} ℤ) C X χ).toRingHom, fun x => by simp, ?_⟩
  refine (pullback_map_fst _ _).trans ?_
  erw [pullback.lift_fst_assoc]
  exact Category.id_comp _

theorem ringHom_uliftInt_ext {C : Type} [Semiring C] (f g : ULift.{0} ℤ →+* C) : f = g := by
  have h := RingHom.ext_int (f.comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).symm.toRingHom)
    (g.comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).symm.toRingHom)
  ext ⟨n⟩
  exact RingHom.congr_fun h n

theorem ringHom_ext_int_torus {C : Type} [Semiring C]
    {f g : AddMonoidAlgebra (ULift.{0} ℤ) X →+* C}
    (h : ∀ y, f (AddMonoidAlgebra.single y 1) = g (AddMonoidAlgebra.single y 1)) : f = g :=
  AddMonoidAlgebra.ringHom_ext (fun r => RingHom.congr_fun
    (ringHom_uliftInt_ext (f.comp AddMonoidAlgebra.singleZeroRingHom)
      (g.comp AddMonoidAlgebra.singleZeroRingHom)) r) h

theorem spm_torusPt {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
    (ψ : C →ₐ[A] D) (χ : Multiplicative X →* C) :
    spm ψ ≫ torusPt A X χ = torusPt A X ((ψ : C →* D).comp χ) := by
  obtain ⟨φ, h1, h2⟩ := torusPt_fst A X χ
  obtain ⟨φ', h1', h2'⟩ := torusPt_fst A X ((ψ : C →* D).comp χ)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · refine Eq.trans ?_ h2'.symm
    refine (Category.assoc _ _ _).trans ((congrArg ((spm ψ).left ≫ ·) h2).trans ?_)
    refine (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ.toRingHom)).symm.trans ?_
    rw [← CommRingCat.ofHom_comp]
    congr 2
    apply ringHom_ext_int_torus
    intro y
    simp [h1, h1']
  · exact (Over.w _).trans (Over.w _).symm

open scoped AlgebraMonoidAlgebra in
theorem isIso_torusPt_of :
    IsIso (torusPt A X (AddMonoidAlgebra.of A X)).left := by
  letI : Algebra ZU.{0} A := ULift.algebra' ℤ A
  haveI : IsScalarTower ZU.{0} (AddMonoidAlgebra ZU.{0} X) (AddMonoidAlgebra A X) :=
    ⟨fun r a b => by
      obtain ⟨n⟩ := r
      show (n • a) • b = n • (a • b)
      simp only [Algebra.smul_def, map_mul, _root_.mul_assoc, eq_intCast, map_intCast]⟩
  have hp := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout ZU.{0} (AddMonoidAlgebra ZU.{0} X) A (AddMonoidAlgebra A X))
  have hz : Spec.map (CommRingCat.ofHom (algebraMap ZU.{0} A)) = toZ (Spec (.of A)) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [hz] at hp
  obtain ⟨φ, h1, h2⟩ := torusPt_fst A X (AddMonoidAlgebra.of A X)
  have : (torusPt A X (AddMonoidAlgebra.of A X)).left = hp.isoPullback.hom := by
    apply pullback.hom_ext
    · refine h2.trans (Eq.trans ?_ hp.isoPullback_hom_fst.symm)
      congr 2
      apply ringHom_ext_int_torus
      intro y
      rw [h1]
      simp
    · exact (Over.w _).trans hp.isoPullback_hom_snd.symm
  rw [this]
  exact hp.isoPullback.isIso_hom

abbrev dm (g : X →+ X × X) : AddMonoidAlgebra A X →ₐ[A] AddMonoidAlgebra A (X × X) :=
  AddMonoidAlgebra.mapDomainAlgHom A A g

theorem torus_diag :
    (spm (dm A X (AddMonoidHom.inl X X)) ≫ torusPt A X (AddMonoidAlgebra.of A X)) *
      (spm (dm A X (AddMonoidHom.inr X X)) ≫ torusPt A X (AddMonoidAlgebra.of A X)) =
    spm (dm A X ((AddMonoidHom.id X).prod (AddMonoidHom.id X))) ≫
      torusPt A X (AddMonoidAlgebra.of A X) := by
  rw [spm_torusPt, spm_torusPt, spm_torusPt, ← torusPt_mul]
  congr 1
  ext x
  simp [AddMonoidAlgebra.single_mul_single]

theorem exists_retraction : ∃ r : AddMonoidAlgebra A (X × X) →ₗ[A] AddMonoidAlgebra A X,
    ∀ d, r (dm A X ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) d -
      (dm A X (AddMonoidHom.inl X X) d + dm A X (AddMonoidHom.inr X X) d)) = d := by
  classical
  let r : AddMonoidAlgebra A (X × X) →ₗ[A] AddMonoidAlgebra A X :=
    (AddMonoidAlgebra.basis (X × X) A).constr A (fun p =>
      if p.1 = p.2 then (if p.1 = 0 then -AddMonoidAlgebra.single 0 1 else
        AddMonoidAlgebra.single p.1 1) else 0)
  have hr : ∀ p : X × X, r (AddMonoidAlgebra.single p 1) =
      if p.1 = p.2 then (if p.1 = 0 then -AddMonoidAlgebra.single 0 1 else
        AddMonoidAlgebra.single p.1 1) else 0 := fun p =>
    (AddMonoidAlgebra.basis (X × X) A).constr_basis A _ p
  refine ⟨r, fun d => ?_⟩
  have : r ∘ₗ ((dm A X ((AddMonoidHom.id X).prod (AddMonoidHom.id X))).toLinearMap -
      ((dm A X (AddMonoidHom.inl X X)).toLinearMap +
        (dm A X (AddMonoidHom.inr X X)).toLinearMap)) = LinearMap.id := by
    apply (AddMonoidAlgebra.basis X A).ext
    intro x
    by_cases hx : x = 0
    · simp [hr, hx]
    · simp [hr, hx, Ne.symm hx]
  exact LinearMap.congr_fun this d

end

theorem exists_chart [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra A R) (j : sp A R ⟶ B) (_ : IsOpenImmersion j.left)
      (ε : R →ₐ[A] A), spm ε ≫ j = 1 := by
  let e : sp A A ⟶ B := 1
  obtain ⟨R, i, hi, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := B.left) (x := e.left (IsLocalRing.closedPoint A)) (U := ⊤) trivial
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (i ≫ B.hom)
  letI : Algebra A R := ρ.hom.toAlgebra
  let j : sp A R ⟶ B := Over.homMk i hρ.symm
  have hr : Set.range e.left ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    have := Scheme.preimage_eq_top_of_closedPoint_mem (R := .of A) e.left (U := i.opensRange) hx
    have hx' : x ∈ e.left ⁻¹ᵁ i.opensRange := by rw [this]; trivial
    exact hx'
  obtain ⟨ε, hε⟩ := spm_surjective (A := A) (C := R) (D := A)
    (Over.homMk (IsOpenImmersion.lift i e.left hr) (by
      change _ ≫ Spec.map ρ = _
      rw [hρ, IsOpenImmersion.lift_fac_assoc, Over.w e]))
  refine ⟨R, inferInstance, inferInstance, j, hi, ε, ?_⟩
  rw [hε]
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

theorem isNilpotent_of_mem_map {C : Type} [CommRing C] [Algebra A C] {J : Ideal A}
    (hJ : IsNilpotent J) (k : ℕ) (x : C) (hx : x ∈ (J ^ (k + 1)).map (algebraMap A C)) :
    IsNilpotent x := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  have := Ideal.pow_mem_pow hx n
  rw [← Ideal.map_pow, ← pow_mul, mul_comm, pow_mul, hn] at this
  simpa using this

theorem map_mem_map {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
    (I : Ideal A) (r : C →ₗ[A] D) {x : C} (hx : x ∈ I.map (algebraMap A C)) :
    r x ∈ I.map (algebraMap A D) := by
  have h1 : x ∈ I • (⊤ : Submodule A C) := by rw [Ideal.smul_top_eq_map]; exact hx
  have h2 : r x ∈ I • (⊤ : Submodule A D) := by
    have := Submodule.mem_map_of_mem (f := r) h1
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  rw [Ideal.smul_top_eq_map] at h2
  exact h2

end TorusNil

open TorusNil in

theorem splitTorus_hom_eq_one_of_nilpotent (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A)
    (hJ : IsNilpotent J) (X : Type) [AddCommGroup X] (B : Over (Spec (CommRingCat.of A)))
    [GrpObj B] (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ B) (hf : IsMonHom f)
    (h : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map
        (toUnit _ ≫ η[B])) : f = toUnit _ ≫ η[B] := by
  obtain ⟨R, _, _, j, _, ε, hε⟩ := exists_chart B
  set t := torusPt A X (AddMonoidAlgebra.of A X) with ht
  let K₀ : Ideal (AddMonoidAlgebra A X) := (J ^ (0 + 1)).map (algebraMap A _)
  have h0 : spm (Ideal.Quotient.mkₐ A K₀) ≫ t ≫ f = 1 := by
    rw [← Category.assoc, comp_eq_of_pullback_map_eq h _
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J
        (algebraMap A (AddMonoidAlgebra A X ⧸ K₀)) (fun a ha => by
          rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_map_of_mem _ (by simpa using ha)))))
      (by rw [← Spec.map_comp]; rfl)]
    exact MonObj.comp_one _
  obtain ⟨φ, hφ⟩ := exists_pt j ε hε (Ideal.Quotient.mkₐ A K₀) Ideal.Quotient.mk_surjective
    (fun x hx => isNilpotent_of_mem_map hJ 0 x (Ideal.Quotient.eq_zero_iff_mem.1 hx)) _ h0
  have main : ∀ k : ℕ, ∀ a, φ a - algebraMap A _ (ε a) ∈
      (J ^ (k + 1)).map (algebraMap A (AddMonoidAlgebra A X)) := by
    intro k
    induction k with
    | zero =>
      intro a
      rw [← hφ, ← pt_one j ε hε, ← Category.assoc, ← spm_comp] at h0
      have := AlgHom.congr_fun (pt_injective j h0) a
      exact Ideal.Quotient.eq.1 this
    | succ k ih =>
      intro a
      have hd : ∀ (g : X →+ X × X) a, (dm A X g).comp φ a - algebraMap A _ (ε a) =
          dm A X g (φ a - algebraMap A _ (ε a)) := by
        intro g a
        rw [map_sub, AlgHom.commutes, AlgHom.comp_apply]
      have hm := mul_pt j ε hε ((J ^ (k + 1)).map (algebraMap A (AddMonoidAlgebra A (X × X))))
        (isNilpotent_of_mem_map hJ k) ((dm A X (AddMonoidHom.inl X X)).comp φ)
        ((dm A X (AddMonoidHom.inr X X)).comp φ)
        ((dm A X ((AddMonoidHom.id X).prod (AddMonoidHom.id X))).comp φ)
        (fun a => by rw [hd]; exact map_mem_map _ (dm A X _).toLinearMap (ih a))
        (fun a => by rw [hd]; exact map_mem_map _ (dm A X _).toLinearMap (ih a))
        (by
          simp only [spm_comp, Category.assoc, hφ]
          simp only [← Category.assoc]
          rw [← MonObj.mul_comp, ht, torus_diag]) a
      obtain ⟨r, hr⟩ := exists_retraction A X
      rw [← hr (φ a - algebraMap A _ (ε a)), ← hd, ← hd, ← hd]
      apply map_mem_map
      rw [← Ideal.map_pow, ← pow_mul] at hm
      refine Ideal.map_mono (Ideal.pow_le_pow_right (n := (k + 1) * 2) (by omega)) ?_
      convert hm using 1
      ring
  obtain ⟨n, hn⟩ := hJ
  have hφε : φ = (Algebra.ofId A _).comp ε := by
    ext1 a
    have := main n a
    rw [pow_succ, hn] at this
    simpa [sub_eq_zero] using this
  rw [hφε, pt_one j ε hε] at hφ
  haveI := isIso_torusPt_of A X
  have h1 : t ≫ f = t ≫ toUnit _ ≫ η[B] := hφ.symm.trans (MonObj.comp_one t).symm
  apply Over.OverMorphism.ext
  rw [← cancel_epi t.left, ← Over.comp_left, h1, ← Over.comp_left]

end GlobalTheory
