import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMapStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.Tan.Univ

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

section Ring

variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

def iota : TrivSqZeroExt R V →+* DualNumber (TrivSqZeroExt R V) where
  toFun a := TrivSqZeroExt.inl (TrivSqZeroExt.inl a.fst) + TrivSqZeroExt.inr (TrivSqZeroExt.inr a.snd)
  map_one' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_zero' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · refine TrivSqZeroExt.ext ?_ ?_ <;> simp [add_comm, mul_comm]

theorem iota_fst (a : TrivSqZeroExt R V) : (iota a).fst = TrivSqZeroExt.inl a.fst := by simp [iota]

theorem iota_snd (a : TrivSqZeroExt R V) : (iota a).snd = TrivSqZeroExt.inr a.snd := by simp [iota]

theorem iota_injective : Function.Injective (iota : TrivSqZeroExt R V →+* _) := by
  intro a b h
  have h₁ := congrArg (fun c => (TrivSqZeroExt.fst c).fst) h
  have h₂ := congrArg (fun c => (TrivSqZeroExt.snd c).snd) h
  simp only [iota_fst, iota_snd, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inr] at h₁ h₂
  exact TrivSqZeroExt.ext h₁ h₂

theorem iota_surjective_spec :
    Function.Surjective (Spec.map (CommRingCat.ofHom (iota : TrivSqZeroExt R V →+* _))) := by
  intro p
  let q : PrimeSpectrum (DualNumber (TrivSqZeroExt R V)) :=
    PrimeSpectrum.comap (TrivSqZeroExt.fstHom (TrivSqZeroExt R V) (TrivSqZeroExt R V) (TrivSqZeroExt R V)).toRingHom p
  refine ⟨q, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change (iota a).fst ∈ p.asIdeal ↔ a ∈ p.asIdeal
  rw [iota_fst]
  set b : TrivSqZeroExt R V := TrivSqZeroExt.inl a.fst with hb
  have h0 : (b - a).fst = 0 := by simp [hb]
  have hm : b - a ∈ p.asIdeal := by
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : (b - a) ^ 2 = 0 := by
      rw [pow_two]
      ext1 <;> simp [h0]
    rw [this]; exact zero_mem _
  constructor
  · intro h; simpa using p.asIdeal.sub_mem h hm
  · intro h; simpa using p.asIdeal.add_mem hm h

theorem epsMul_fst {A : Type} [CommRing A] (c : A) (a : DualNumber A) : (epsMul c a).fst = a.fst := by
  simp [epsMul]

theorem epsMul_snd {A : Type} [CommRing A] (c : A) (a : DualNumber A) : (epsMul c a).snd = c * a.snd := by
  simp [epsMul]

theorem dualMap_fst {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (a : DualNumber A) :
    (dualMap f a).fst = f a.fst := by
  simp [dualMap]

theorem dualMap_snd {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (a : DualNumber A) :
    (dualMap f a).snd = f a.snd := by
  simp [dualMap]

theorem iota_comp_map (q : V) :
    iota.comp (TrivSqZeroExt.map (LinearMap.toSpanSingleton R V q)).toRingHom =
      (epsMul (TrivSqZeroExt.inr q : TrivSqZeroExt R V)).comp (dualMap (algebraMap R (TrivSqZeroExt R V))) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [iota_fst, epsMul_fst, dualMap_fst, TrivSqZeroExt.algebraMap_eq_inl]
  · simp only [RingHom.comp_apply, iota_snd, epsMul_snd, dualMap_snd]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_iota :
    (TrivSqZeroExt.fstHom (TrivSqZeroExt R V) (TrivSqZeroExt R V) (TrivSqZeroExt R V)).toRingHom.comp iota =
      (algebraMap R (TrivSqZeroExt R V)).comp (TrivSqZeroExt.fstHom R R V).toRingHom :=
  RingHom.ext fun a => by simp [iota_fst, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_fst_comp_iota :
    (dualMap (TrivSqZeroExt.fstHom R R V).toRingHom).comp iota =
      (TrivSqZeroExt.map (0 : V →ₗ[R] R)).toRingHom := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [iota_fst, dualMap_fst]
  · simp [iota_snd, dualMap_snd]

theorem reduce_epsMul (b : TrivSqZeroExt R V) :
    ((dualMap (TrivSqZeroExt.fstHom R R V).toRingHom).comp (epsMul b)).comp (dualMap (algebraMap R (TrivSqZeroExt R V))) =
      epsMul b.fst := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [epsMul_fst, dualMap_fst, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [epsMul_snd, dualMap_snd, TrivSqZeroExt.algebraMap_eq_inl]

end Ring

section Mor

variable {S : Scheme.{0}} {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S)
  (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

abbrev xB : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) ≫ x

def cMor : epsAt (xB x V) ⟶ ob x V :=
  Over.homMk (Spec.map (CommRingCat.ofHom iota)) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ Spec.map _ ≫ x
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext r : 2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [iota_fst, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [iota_snd, TrivSqZeroExt.algebraMap_eq_inl])

def dMor : epsAt x ⟶ epsAt (xB x V) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (dualMap (TrivSqZeroExt.fstHom R R V).toRingHom))) (by
    change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext r : 2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [dualMap_fst, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [dualMap_snd, TrivSqZeroExt.algebraMap_eq_inl])

theorem dMor_cMor : dMor x V ≫ cMor x V = hom x (0 : V →ₗ[R] R) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext1
  exact dualMap_fst_comp_iota

theorem cMor_hom (q : V) : (cMor x V ≫ hom x (LinearMap.toSpanSingleton R V q)).left =
    Spec.map (CommRingCat.ofHom (epsMul (TrivSqZeroExt.inr q : TrivSqZeroExt R V))) ≫
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R (TrivSqZeroExt R V)))) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  exact iota_comp_map q

theorem cMor_cancel {Z : Over S} (f g : ob x V ⟶ Z) (h : cMor x V ≫ f = cMor x V ≫ g) : f = g := by
  ext1
  have h₀ : (cMor x V).left ≫ f.left = (cMor x V).left ≫ g.left := congrArg CommaMorphism.left h
  have h₁ : Function.Surjective (cMor x V).left := iota_surjective_spec
  have h₂ : IsSchemeTheoreticallyDominant (cMor x V).left :=
    std_of_inj (CommRingCat.ofHom (iota : TrivSqZeroExt R V →+* _)) iota_injective
  have h₃ : QuasiCompact (cMor x V).left :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (iota : TrivSqZeroExt R V →+* _))))
  exact epi_of_surj (cMor x V).left h₁ f.left g.left h₀

end Mor

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {L L' : Type} [AddCommGroup L] [Module R L]
  [AddCommGroup L'] [Module B L'] [Module R L'] [IsScalarTower R B L'] {β : L →ₗ[R] L'}
  {J : Type} [Fintype J] {e : J → L} {w : J → Module.Dual R L}

def extForm (hβ : IsBaseChange B β) (f : Module.Dual R L) : L' →ₗ[B] B :=
  hβ.lift (Algebra.linearMap R B ∘ₗ f)

theorem extForm_apply (hβ : IsBaseChange B β) (f : Module.Dual R L) (y : L) :
    extForm hβ f (β y) = algebraMap R B (f y) :=
  hβ.lift_eq _ y

theorem expand (hβ : IsBaseChange B β) (he : ∀ y, ∑ k, w k y • e k = y) (l : L') :
    l = ∑ k, extForm hβ (w k) l • β (e k) := by
  refine hβ.inductionOn l (fun l => l = ∑ k, extForm hβ (w k) l • β (e k)) ?_ ?_ ?_ ?_
  · simp
  · intro y
    simp only [extForm_apply, algebraMap_smul]
    conv_lhs => rw [← he y]
    simp only [map_sum, map_smul]
  · intro s n h
    simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← h]
  · intro a b ha hb
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    rw [← ha, ← hb]

theorem dual_expand (he : ∀ y, ∑ k, w k y • e k = y) (f : Module.Dual R L) : ∑ k, f (e k) • w k = f := by
  ext y
  conv_rhs => rw [← he y]
  simp [mul_comm]

theorem extForm_sum (hβ : IsBaseChange B β) (f : Module.Dual R L) (b : J → B) :
    extForm hβ f (∑ k, b k • β (e k)) = ∑ k, b k * algebraMap R B (f (e k)) := by
  simp [extForm_apply]

end Alg

section Sq

variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
  {L L' : Type} [AddCommGroup L] [Module R L]
  [AddCommGroup L'] [Module (TrivSqZeroExt R V) L'] [Module R L'] [IsScalarTower R (TrivSqZeroExt R V) L']
  {β : L →ₗ[R] L'} {J : Type} [Fintype J] {e : J → L} {w : J → Module.Dual R L}

theorem inr_sum (s : J → V) :
    (TrivSqZeroExt.inr (∑ j, s j) : TrivSqZeroExt R V) = ∑ j, TrivSqZeroExt.inr (s j) :=
  map_sum (TrivSqZeroExt.inrHom R V) s _

theorem resum (he : ∀ y, ∑ k, w k y • e k = y) (q : J → V) :
    ∑ k, (TrivSqZeroExt.inr (∑ j, w k (e j) • q j) : TrivSqZeroExt R V) • β (e k) =
      ∑ j, (TrivSqZeroExt.inr (q j) : TrivSqZeroExt R V) • β (e j) := by
  have h1 : ∀ j, ∑ k, (TrivSqZeroExt.inr (w k (e j) • q j) : TrivSqZeroExt R V) • β (e k) =
      (TrivSqZeroExt.inr (q j) : TrivSqZeroExt R V) • β (e j) := by
    intro j
    conv_rhs => rw [← he (e j)]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, TrivSqZeroExt.inr_smul, smul_assoc, smul_comm]
  simp only [inr_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => h1 j

theorem extForm_inr (hβ : IsBaseChange (TrivSqZeroExt R V) β) (he : ∀ y, ∑ k, w k y • e k = y)
    (φ : Module.Dual R L →ₗ[R] V) (f : Module.Dual R L) :
    extForm hβ f (∑ k, (TrivSqZeroExt.inr (φ (w k)) : TrivSqZeroExt R V) • β (e k)) =
      TrivSqZeroExt.inr (φ f) := by
  rw [extForm_sum]
  conv_rhs => rw [← dual_expand he f]
  rw [map_sum, inr_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, TrivSqZeroExt.inr_smul, Algebra.smul_def, mul_comm]

theorem fst_extForm (hβ : IsBaseChange (TrivSqZeroExt R V) β) (he : ∀ y, ∑ k, w k y • e k = y) (l : L')
    (h : ∑ k, (extForm hβ (w k) l).fst • e k = 0) (k : J) : (extForm hβ (w k) l).fst = 0 := by
  have h₁ := congrArg (extForm hβ (w k)) (expand hβ he l)
  rw [extForm_sum] at h₁
  have h₂ := congrArg TrivSqZeroExt.fst h₁
  have h₃ := congrArg (w k) h
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h₃
  rw [h₂, ← h₃]
  simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_sum]

end Sq

section Grp

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {R : Type} [CommRing R]
  {x : Spec (CommRingCat.of R) ⟶ S} {L : Type} [AddCommGroup L] [Module R L]

theorem comp_prod {T T' : Over S} (f : T' ⟶ T) {I : Type} (s : Finset I) (g : I → (T ⟶ G)) :
    f ≫ ∏ l ∈ s, g l = ∏ l ∈ s, f ≫ g l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

theorem pt_zero (M : LieModel G x L) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem pt_sum (M : LieModel G x L) {I : Type} (s : Finset I) (f : I → L) :
    M.pt (∑ l ∈ s, f l) = ∏ l ∈ s, M.pt (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pt_zero M
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, M.add, ih]

theorem hom_scalar_pt (M : LieModel G x L) (c : R) (y : L) :
    hom x (LinearMap.toSpanSingleton R R c) ≫ M.pt y = M.pt (c • y) := by
  have h : LinearMap.toSpanSingleton R R c = c • LinearMap.id := by
    ext
    simp
  ext1
  rw [M.smul, h]
  rfl

variable {J : Type} [Fintype J]

def univ (M : LieModel G x L) (e : J → L) (w : J → Module.Dual R L) : ob x (Module.Dual R L) ⟶ G :=
  ∏ k, hom x (LinearMap.toSpanSingleton R (Module.Dual R L) (w k)) ≫ M.pt (e k)

theorem zsec_univ (M : LieModel G x L) (e : J → L) (w : J → Module.Dual R L) : zsec x ≫ univ M e w = 1 := by
  rw [univ, comp_prod]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [← Category.assoc, zsec_hom]
  exact (isTanAt_iff x G _).1 (M.tan (e k))

variable {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

theorem hom_univ (M : LieModel G x L) (e : J → L) (w : J → Module.Dual R L) (φ : Module.Dual R L →ₗ[R] V) :
    hom x φ ≫ univ M e w = ∏ k, hom x (LinearMap.toSpanSingleton R V (φ (w k))) ≫ M.pt (e k) := by
  rw [univ, comp_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Category.assoc, LieEx.hom_comp]
  congr 2
  ext
  simp

theorem eval_univ (M : LieModel G x L) {e : J → L} {w : J → Module.Dual R L}
    (he : ∀ y, ∑ k, w k y • e k = y) (y : L) :
    hom x (Module.Dual.eval R L y) ≫ univ M e w = M.pt y := by
  rw [hom_univ]
  conv_rhs => rw [← he y, pt_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  exact hom_scalar_pt M _ _

variable {L' : Type} [AddCommGroup L'] [Module (TrivSqZeroExt R V) L'] [Module R L']
  [IsScalarTower R (TrivSqZeroExt R V) L'] {β : L →ₗ[R] L'}

theorem cMor_pt (M : LieModel G x L) (M' : LieModel G (xB x V) L')
    (hj : ∀ y, (M'.pt (β y)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R (TrivSqZeroExt R V)))) ≫ (M.pt y).left)
    (q : V) (y : L) :
    cMor x V ≫ hom x (LinearMap.toSpanSingleton R V q) ≫ M.pt y =
      M'.pt ((TrivSqZeroExt.inr q : TrivSqZeroExt R V) • β y) := by
  ext1
  rw [M'.smul, hj, ← Category.assoc (cMor x V), Over.comp_left, cMor_hom, Category.assoc]

theorem dMor_pt (M : LieModel G x L) (M' : LieModel G (xB x V) L')
    (hj : ∀ y, (M'.pt (β y)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R (TrivSqZeroExt R V)))) ≫ (M.pt y).left)
    (b : TrivSqZeroExt R V) (y : L) :
    dMor x V ≫ M'.pt (b • β y) = M.pt (b.fst • y) := by
  ext1
  rw [M.smul, Over.comp_left, M'.smul, hj, ← reduce_epsMul b]
  change Spec.map _ ≫ _ ≫ _ ≫ _ = _
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

theorem cMor_hom_univ (M : LieModel G x L) (M' : LieModel G (xB x V) L')
    (hj : ∀ y, (M'.pt (β y)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R (TrivSqZeroExt R V)))) ≫ (M.pt y).left)
    (e : J → L) (w : J → Module.Dual R L) (φ : Module.Dual R L →ₗ[R] V) :
    cMor x V ≫ hom x φ ≫ univ M e w =
      M'.pt (∑ k, (TrivSqZeroExt.inr (φ (w k)) : TrivSqZeroExt R V) • β (e k)) := by
  rw [hom_univ, comp_prod, pt_sum]
  exact Finset.prod_congr rfl fun k _ => cMor_pt M M' hj _ _

theorem cMor_tan {v : ob x V ⟶ G} (hv : zsec x ≫ v = 1) : IsTanAt G (xB x V) (cMor x V ≫ v) := by
  rw [isTanAt_iff]
  have h : zsec (xB x V) ≫ cMor x V = (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V)))) rfl : Over.mk (xB x V) ⟶ Over.mk x) ≫ zsec x := by
    ext1
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    exact fst_comp_iota
  rw [← Category.assoc, h, Category.assoc, hv, MonObj.comp_one]

theorem hom_zero_tan {v : ob x V ⟶ G} (hv : zsec x ≫ v = 1) : hom x (0 : V →ₗ[R] R) ≫ v = 1 := by
  rw [hom_zero, Category.assoc, hv, MonObj.comp_one]

theorem exists_form (M : LieModel G x L) (M' : LieModel G (xB x V) L')
    (hj : ∀ y, (M'.pt (β y)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R (TrivSqZeroExt R V)))) ≫ (M.pt y).left)
    (hβ : IsBaseChange (TrivSqZeroExt R V) β) {e : J → L} {w : J → Module.Dual R L}
    (he : ∀ y, ∑ k, w k y • e k = y) {v : ob x V ⟶ G} (hv : zsec x ≫ v = 1) :
    ∃ φ : Module.Dual R L →ₗ[R] V, hom x φ ≫ univ M e w = v := by
  obtain ⟨l, hl⟩ := M'.onto _ (cMor_tan hv)
  have hexp := expand hβ he l
  have h1 : M.pt (∑ k, (extForm hβ (w k) l).fst • e k) = 1 := by
    rw [pt_sum]
    have h2 : dMor x V ≫ M'.pt l = 1 := by
      rw [hl, ← Category.assoc, dMor_cMor]
      exact hom_zero_tan hv
    rw [hexp, pt_sum, comp_prod] at h2
    rw [← h2]
    exact Finset.prod_congr rfl fun k _ => (dMor_pt M M' hj _ _).symm
  have h3 := fst_extForm hβ he l (M.inj (h1.trans (pt_zero M).symm))
  have hb : ∀ k, extForm hβ (w k) l = TrivSqZeroExt.inr (extForm hβ (w k) l).snd := fun k =>
    TrivSqZeroExt.ext (by simpa using h3 k) (by simp)
  refine ⟨∑ k, (Module.Dual.eval R L (e k)).smulRight (extForm hβ (w k) l).snd, ?_⟩
  apply cMor_cancel
  rw [cMor_hom_univ M M' hj, ← hl]
  congr 1
  conv_rhs => rw [hexp]
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Module.Dual.eval_apply]
  rw [resum he]
  exact Finset.sum_congr rfl fun k _ => by rw [← hb]

theorem form_unique (M : LieModel G x L) (M' : LieModel G (xB x V) L')
    (hj : ∀ y, (M'.pt (β y)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R (TrivSqZeroExt R V)))) ≫ (M.pt y).left)
    (hβ : IsBaseChange (TrivSqZeroExt R V) β) {e : J → L} {w : J → Module.Dual R L}
    (he : ∀ y, ∑ k, w k y • e k = y) {φ φ' : Module.Dual R L →ₗ[R] V}
    (h : hom x φ ≫ univ M e w = hom x φ' ≫ univ M e w) : φ = φ' := by
  have h1 := congrArg (cMor x V ≫ ·) h
  simp only [cMor_hom_univ M M' hj] at h1
  have h2 := M'.inj h1
  ext f
  have h3 := congrArg (extForm hβ f) h2
  rw [extForm_inr hβ he, extForm_inr hβ he] at h3
  exact TrivSqZeroExt.inr_injective h3

end Grp

theorem tangent_universal (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R : Type) [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) :
    ∃ u : ob x (Module.Dual R L) ⟶ G, zsec x ≫ u = 1 ∧
      (∀ e : L, hom x (Module.Dual.eval R L e) ≫ u = M.pt e) ∧
      ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (v : ob x V ⟶ G),
        zsec x ≫ v = 1 → ∃! φ : Module.Dual R L →ₗ[R] V, hom x φ ≫ u = v := by
  obtain ⟨hfin, hproj, hbc⟩ := GlobalTheory.T.lie_model_finite_base_change S G R x L M
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R L
  let e : Fin n → L := fun k => f (Pi.single k 1)
  let w : Fin n → Module.Dual R L := fun k => LinearMap.proj k ∘ₗ g
  have he : ∀ y, ∑ k, w k y • e k = y := by
    intro y
    have h := LinearMap.congr_fun hfg y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    conv_rhs => rw [← h, ← Finset.univ_sum_single (g y)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : Pi.single k (g y k) = g y k • (Pi.single k 1 : Fin n → R) := by
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    rw [this, map_smul]
    rfl
  refine ⟨univ M e w, zsec_univ M e w, eval_univ M he, ?_⟩
  intro V _ _ _ _ v hv
  obtain ⟨L', _, _, ⟨M'⟩⟩ := lieModel_exists S G (TrivSqZeroExt R V) (xB x V)
  obtain ⟨j, hj1, hj2, -⟩ := GlobalTheory.T.lie_model_base_change_map S G R (TrivSqZeroExt R V) x L L' M M'
  letI : Module R L' := Module.compHom L' (algebraMap R (TrivSqZeroExt R V))
  haveI : IsScalarTower R (TrivSqZeroExt R V) L' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let β : L →ₗ[R] L' := { toFun := j, map_add' := j.map_add, map_smul' := hj2 }
  have hB : IsBaseChange (TrivSqZeroExt R V) β := hbc (TrivSqZeroExt R V) L' M' β hj1
  obtain ⟨φ, hφ⟩ := exists_form M M' hj1 hB he hv
  exact ⟨φ, hφ, fun φ' h => form_unique M M' hj1 hB he (h.trans hφ.symm)⟩

end GlobalTheory.CompanionTheory.Ar.BT.Tan.Univ
