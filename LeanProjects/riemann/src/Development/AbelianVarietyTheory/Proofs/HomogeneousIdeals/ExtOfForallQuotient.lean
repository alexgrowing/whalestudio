import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

namespace GlobalTheory.LaurentConst

section Algebra

open AddMonoidAlgebra

attribute [-simp] LaurentPolynomial.single_eq_C_mul_T

variable {L R : Type} [CommRing L] [CommRing R]

noncomputable def evalAt {A : Type} [CommRing A] (r : L →+* A) (u : Aˣ) :
    AddMonoidAlgebra L ℤ →+* A :=
  AddMonoidAlgebra.liftNCRingHom r ((Units.coeHom A).comp (zpowersHom Aˣ u))
    fun _ _ ↦ Commute.all _ _

theorem evalAt_single {A : Type} [CommRing A] (r : L →+* A) (u : Aˣ) (n : ℤ) (c : L) :
    evalAt r u (single n c) = r c * ((u ^ n : Aˣ) : A) := by
  simp [evalAt]

theorem hom_ext {A : Type} [CommRing A] {f g : AddMonoidAlgebra L ℤ →+* A}
    (h₀ : ∀ c, f (single 0 c) = g (single 0 c)) (h₁ : f (single 1 1) = g (single 1 1)) : f = g := by
  have := MonoidHom.ext_mint (f := f.toMonoidHom.comp (AddMonoidAlgebra.of L ℤ))
    (g := g.toMonoidHom.comp (AddMonoidAlgebra.of L ℤ)) h₁
  exact AddMonoidAlgebra.ringHom_ext h₀ fun n ↦ DFunLike.congr_fun this (Multiplicative.ofAdd n)

variable (R) in

noncomputable def var : (AddMonoidAlgebra R ℤ)ˣ where
  val := single 1 1
  inv := single (-1) 1
  val_inv := by simp [single_mul_single, one_def]
  inv_val := by simp [single_mul_single, one_def]

variable (R) in

noncomputable def svar : (LaurentSeries R)ˣ where
  val := HahnSeries.single 1 1
  inv := HahnSeries.single (-1) 1
  val_inv := by simp [HahnSeries.single_mul_single]
  inv_val := by simp [HahnSeries.single_mul_single]

theorem svar_zpow (n : ℤ) : ((svar R ^ n : (LaurentSeries R)ˣ) : LaurentSeries R) =
    HahnSeries.single n 1 := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, Units.val_mul, ih]; simp [svar, HahnSeries.single_mul_single]
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, ih]; simp [svar, HahnSeries.single_mul_single, sub_eq_add_neg]

variable (R) in

noncomputable def atZero : AddMonoidAlgebra R ℤ →+* LaurentSeries R := evalAt HahnSeries.C (svar R)

variable (R) in

noncomputable def atInf : AddMonoidAlgebra R ℤ →+* LaurentSeries R := evalAt HahnSeries.C (svar R)⁻¹

theorem evalAt_const {A : Type} [CommRing A] (r : L →+* A) (u : Aˣ) (c : L) :
    evalAt r u (algebraMap L _ c) = r c := by
  simpa using evalAt_single r u 0 c

theorem evalAt_var {A : Type} [CommRing A] (r : L →+* A) (u : Aˣ) :
    evalAt r u (var L : AddMonoidAlgebra L ℤ) = u := by
  simpa [var] using evalAt_single r u 1 1

theorem atZero_const (c : R) : atZero R (algebraMap R _ c) = HahnSeries.C c := evalAt_const _ _ c

theorem atInf_const (c : R) : atInf R (algebraMap R _ c) = HahnSeries.C c := evalAt_const _ _ c

theorem coeff_atZero (z : AddMonoidAlgebra R ℤ) (n : ℤ) : (atZero R z).coeff n = z.coeff n := by
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single m r =>
    rw [atZero, evalAt_single, svar_zpow]
    simp [HahnSeries.coeff_single, Finsupp.single_apply, eq_comm]

theorem coeff_atInf (z : AddMonoidAlgebra R ℤ) (n : ℤ) : (atInf R z).coeff (-n) = z.coeff n := by
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single m r =>
    rw [atInf, evalAt_single, inv_zpow', svar_zpow]
    simp [HahnSeries.coeff_single, Finsupp.single_apply, eq_comm]

theorem eq_const {z : AddMonoidAlgebra R ℤ} {p q : PowerSeries R}
    (hp : atZero R z = HahnSeries.ofPowerSeries ℤ R p)
    (hq : atInf R z = HahnSeries.ofPowerSeries ℤ R q) :
    z = algebraMap R _ (PowerSeries.constantCoeff p) := by
  ext n
  rcases lt_trichotomy n 0 with h | rfl | h
  · rw [← coeff_atZero, hp, PowerSeries.coeff_coe, if_pos h]
    simp [Finsupp.single_apply, h.ne]
  · rw [← coeff_atZero, hp, PowerSeries.coeff_coe]
    simp
  · rw [← coeff_atInf, hq, PowerSeries.coeff_coe, if_pos (by omega)]
    simp [Finsupp.single_apply, h.ne']

variable (r : L →+* R) (t : Rˣ)

noncomputable def scale : AddMonoidAlgebra L ℤ →+* AddMonoidAlgebra R ℤ :=
  evalAt ((algebraMap R _).comp r) (Units.map (algebraMap R _).toMonoidHom t * var R)

noncomputable def scaleP : PowerSeries L →+* PowerSeries R :=
  (PowerSeries.rescale (t : R)).comp (PowerSeries.map r)

theorem coe_scaleP_X : HahnSeries.ofPowerSeries ℤ R (scaleP r t PowerSeries.X) =
    HahnSeries.C (t : R) * (svar R : LaurentSeries R) := by
  simp [scaleP, svar, PowerSeries.rescale_X]

theorem scaleP_C (c : L) : scaleP r t (PowerSeries.C c) = PowerSeries.C (r c) := by
  ext n
  simp [scaleP, PowerSeries.coeff_C]
  aesop

noncomputable def scaleL : LaurentSeries L →+* LaurentSeries R :=
  IsLocalization.Away.lift (PowerSeries.X : PowerSeries L)
    (g := (HahnSeries.ofPowerSeries ℤ R).comp (scaleP r t)) (by
      rw [RingHom.comp_apply, coe_scaleP_X]
      exact (t.isUnit.map _).mul (svar R).isUnit)

theorem scaleL_coe (p : PowerSeries L) : scaleL r t (HahnSeries.ofPowerSeries ℤ L p) =
    HahnSeries.ofPowerSeries ℤ R (scaleP r t p) :=
  IsLocalization.Away.lift_eq _ _ p

theorem scaleL_C (c : L) : scaleL r t (HahnSeries.C c) = HahnSeries.C (r c) := by
  rw [← HahnSeries.ofPowerSeries_C, scaleL_coe, scaleP_C, HahnSeries.ofPowerSeries_C]

theorem scaleL_svar : scaleL r t (svar L : LaurentSeries L) =
    HahnSeries.C (t : R) * (svar R : LaurentSeries R) := by
  rw [← coe_scaleP_X r, ← scaleL_coe, HahnSeries.ofPowerSeries_X]; rfl

theorem scale_single_zero (c : L) : scale r t (single 0 c) = single 0 (r c) := by
  simp [scale, evalAt_single]

theorem scale_single_one : scale r t (single 1 1) = single 1 (t : R) := by
  simp [scale, evalAt_single, var, single_mul_single]

theorem atZero_scale : (atZero R).comp (scale r t) = (scaleL r t).comp (atZero L) := by
  refine hom_ext (fun c ↦ ?_) ?_
  · simp only [RingHom.comp_apply, scale_single_zero, atZero, evalAt_single, zpow_zero,
      Units.val_one, mul_one, scaleL_C]
  · simp only [RingHom.comp_apply, scale_single_one, atZero, evalAt_single, zpow_one, map_one,
      one_mul, scaleL_svar]

theorem atInf_scale : (atInf R).comp (scale r t) = (scaleL r t⁻¹).comp (atInf L) := by
  refine hom_ext (fun c ↦ ?_) ?_
  · simp only [RingHom.comp_apply, scale_single_zero, atInf, evalAt_single, zpow_zero,
      Units.val_one, mul_one, scaleL_C]
  · simp only [RingHom.comp_apply, scale_single_one, atInf, evalAt_single, zpow_one, map_one,
      one_mul]
    have h := congrArg (scaleL r t⁻¹) (svar L).inv_mul
    rw [map_mul, scaleL_svar, map_one] at h
    have h' : (HahnSeries.C t.val : LaurentSeries R) * ((svar R)⁻¹).val *
        (HahnSeries.C (t⁻¹).val * (svar R).val) = 1 := by
      rw [mul_mul_mul_comm, ← map_mul, Units.mul_inv, Units.inv_mul, map_one, mul_one]
    rw [mul_comm] at h
    exact left_inv_eq_right_inv h' h

theorem constantCoeff_scaleP : PowerSeries.constantCoeff.comp (scaleP r t) =
    r.comp PowerSeries.constantCoeff := by
  refine RingHom.ext fun p ↦ ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, scaleP, RingHom.comp_apply,
    PowerSeries.coeff_rescale, PowerSeries.coeff_map, pow_zero, one_mul]

variable {t}

theorem map_eq_one {A : Type} [CommRing A] [IsReduced A] (ht : IsNilpotent ((t : R) - 1))
    (ρ : R →+* A) : ρ t = 1 := by
  have := (ht.map ρ).eq_zero
  rwa [map_sub, map_one, sub_eq_zero] at this

theorem comp_scale {A : Type} [CommRing A] [IsReduced A] (ht : IsNilpotent ((t : R) - 1))
    (ρ : AddMonoidAlgebra R ℤ →+* A) : ρ.comp (scale r t) = ρ.comp (scale r 1) := by
  refine hom_ext (fun c ↦ by simp only [RingHom.comp_apply, scale_single_zero]) ?_
  have e : (single 1 (t : R) : AddMonoidAlgebra R ℤ) = algebraMap R _ t * single 1 1 := by
    simp [single_mul_single]
  simp only [RingHom.comp_apply, scale_single_one, Units.val_one]
  rw [e, map_mul, ← RingHom.comp_apply, map_eq_one ht, one_mul]

theorem comp_scaleP {A : Type} [CommRing A] [IsReduced A] (ht : IsNilpotent ((t : R) - 1))
    (ρ : PowerSeries R →+* A) : ρ.comp (scaleP r t) = ρ.comp (scaleP r 1) := by
  refine RingHom.ext fun p ↦ ?_
  choose c hc using fun n : ℕ ↦ sub_one_dvd_pow_sub_one (t : R) n
  have e : scaleP r t p = scaleP r 1 p +
      (PowerSeries.C (t : R) - 1) * PowerSeries.mk fun n ↦ c n * r (PowerSeries.coeff n p) := by
    ext n
    rw [← map_one PowerSeries.C, ← map_sub]
    simp only [scaleP, RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_map,
      map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Units.val_one, one_pow]
    linear_combination (r (PowerSeries.coeff n p)) * hc n
  have h1 : ρ (PowerSeries.C (t : R)) = 1 := map_eq_one ht (ρ.comp PowerSeries.C)
  simp only [RingHom.comp_apply]
  rw [e, map_add, map_mul, map_sub, h1, map_one, sub_self, zero_mul, add_zero]

end Algebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Geometry

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {W Z : Scheme.{0}}

noncomputable def quot (a b : Z ⟶ B.left) (h : b ≫ B.hom = a ≫ B.hom) : Z ⟶ B.left :=
  ((Over.homMk a rfl : Over.mk (a ≫ B.hom) ⟶ B) * (Over.homMk b h : Over.mk (a ≫ B.hom) ⟶ B)⁻¹).left

theorem comp_quot (j : W ⟶ Z) (a b : Z ⟶ B.left) (h : b ≫ B.hom = a ≫ B.hom) :
    j ≫ quot a b h = quot (j ≫ a) (j ≫ b) (by simp [h]) := by
  let j' : Over.mk ((j ≫ a) ≫ B.hom) ⟶ Over.mk (a ≫ B.hom) := Over.homMk j (by simp)
  have : j' ≫ ((Over.homMk a rfl : Over.mk (a ≫ B.hom) ⟶ B) *
      (Over.homMk b h : Over.mk (a ≫ B.hom) ⟶ B)⁻¹) =
      (Over.homMk (j ≫ a) rfl) * (Over.homMk (j ≫ b) (by simp [h]))⁻¹ := by
    rw [MonObj.comp_mul, GrpObj.comp_inv]; rfl
  exact congrArg (·.left) this

theorem quot_eq_iff (a b : Z ⟶ B.left) (h : b ≫ B.hom = a ≫ B.hom) :
    quot a b h = a ≫ B.hom ≫ (η[B] : 𝟙_ (Over S) ⟶ B).left ↔ a = b := by
  have e : a ≫ B.hom ≫ (η[B] : 𝟙_ (Over S) ⟶ B).left = (1 : Over.mk (a ≫ B.hom) ⟶ B).left := by
    rw [Hom.one_def, Over.comp_left, ← Category.assoc]; rfl
  rw [e]
  refine ⟨fun H ↦ congrArg (·.left) (mul_inv_eq_one.1 (Over.OverMorphism.ext H)), ?_⟩
  rintro rfl
  rw [quot, mul_inv_cancel]

theorem quot_congr {a b a' b' : Z ⟶ B.left} (h : b ≫ B.hom = a ≫ B.hom)
    (h' : b' ≫ B.hom = a' ≫ B.hom) (ha : a = a') (hb : b = b') : quot a b h = quot a' b' h' := by
  subst ha hb; rfl

theorem quot_apply {D A : Type} [CommRing D] [CommRing A] (f : Spec (.of D) ⟶ B.left)
    (α β : D →+* A) (h) (H : ∀ (C : Type) [CommRing C] [IsReduced C] (ρ : A →+* C),
      ρ.comp α = ρ.comp β) (z : Spec (.of A)) :
    quot (Spec.map (CommRingCat.ofHom α) ≫ f) (Spec.map (CommRingCat.ofHom β) ≫ f) h z =
      ((Spec.map (CommRingCat.ofHom α) ≫ f) ≫ B.hom ≫ (η[B] : 𝟙_ (Over S) ⟶ B).left) z := by
  have hz : z.asIdeal.IsPrime := z.isPrime
  let j : Spec (.of (A ⧸ z.asIdeal)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk z.asIdeal))
  obtain ⟨w, hw⟩ : z ∈ Set.range j := ⟨(⊥ : PrimeSpectrum (A ⧸ z.asIdeal)), by
    apply PrimeSpectrum.ext
    exact Ideal.mk_ker⟩
  rw [← hw, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, comp_quot,
    (quot_eq_iff _ _ _).2, Category.assoc]
  simp only [j, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, H]

theorem ext_of_forall_quotient {Y : Scheme.{0}} (p : Y ⟶ S) [IsSeparated p] {D : Type} [CommRing D]
    {a b : Spec (.of D) ⟶ Y} (hab : a ≫ p = b ≫ p) (I : ℕ → Ideal D) (hI : ⨅ n, I n = ⊥)
    (H : ∀ n, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I n))) ≫ a =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I n))) ≫ b) : a = b := by
  have := isClosedImmersion_equalizer_ι_of_isSeparated p hab
  have : IsIso (equalizer.ι a b) := by
    refine IsClosedImmersion.isIso_of_injective_of_isAffine ((injective_iff_map_eq_zero _).2 ?_)
    intro x hx
    obtain ⟨d, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of D)).inv).2 x
    have hd : d ∈ ⨅ n, I n := by
      refine Ideal.mem_iInf.2 fun n ↦ Ideal.Quotient.eq_zero_iff_mem.1 ?_
      apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (D ⧸ I n))).inv).1
      have e := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I n)))
      rw [← equalizer.lift_ι _ (H n), Scheme.Hom.comp_appTop] at e
      have e' := congrArg (fun φ ↦ φ.hom d) e
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e'
      rw [map_zero, e', hx, map_zero]
    rw [hI, Ideal.mem_bot] at hd
    rw [hd, map_zero]
  rw [← cancel_epi (equalizer.ι a b), equalizer.condition]

theorem eq_const_of_affine {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {R : Type}
    [CommRing R] (g : Spec (.of (AddMonoidAlgebra R ℤ)) ⟶ Y) (g₀ g₁ : Spec (.of (PowerSeries R)) ⟶ Y)
    (hg : Set.range g ⊆ U) (hg₀ : Set.range g₀ ⊆ U) (hg₁ : Set.range g₁ ⊆ U)
    (h₀ : Spec.map (CommRingCat.ofHom (atZero R)) ≫ g =
      Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ R)) ≫ g₀)
    (h₁ : Spec.map (CommRingCat.ofHom (atInf R)) ≫ g =
      Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ R)) ≫ g₁) :
    g = Spec.map (CommRingCat.ofHom (algebraMap R _)) ≫
      Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff) ≫ g₀ := by
  obtain ⟨φ, rfl⟩ := exists_specMap_fromSpec_eq g hU hg
  obtain ⟨φ₀, rfl⟩ := exists_specMap_fromSpec_eq g₀ hU hg₀
  obtain ⟨φ₁, rfl⟩ := exists_specMap_fromSpec_eq g₁ hU hg₁
  simp only [← Spec.map_comp_assoc, cancel_mono, Spec.map_inj] at h₀ h₁ ⊢
  ext1
  refine RingHom.ext fun u ↦ ?_
  exact eq_const (congrArg (fun ψ ↦ ψ.hom u) h₀) (congrArg (fun ψ ↦ ψ.hom u) h₁)

theorem exists_extension {Y : Scheme.{0}} (p : Y ⟶ S) [UniversallyClosed p] {L : Type} [Field L]
    (s : Spec (.of L) ⟶ S) (x : Spec (.of (LaurentSeries L)) ⟶ Y)
    (hx : x ≫ p = Spec.map (CommRingCat.ofHom HahnSeries.C) ≫ s) :
    ∃ y : Spec (.of (PowerSeries L)) ⟶ Y,
      Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ L)) ≫ y = x ∧
      y ≫ p = Spec.map (CommRingCat.ofHom PowerSeries.C) ≫ s := by
  have h : ValuativeCriterion.Existence p := by
    have : UniversallyClosed p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at this
    exact this.1
  obtain ⟨⟨l⟩⟩ := h
    { R := PowerSeries L, K := LaurentSeries L, i₁ := x
      i₂ := Spec.map (CommRingCat.ofHom PowerSeries.C) ≫ s
      commSq := ⟨by
        rw [hx, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
        congr 3
        exact RingHom.ext fun c ↦ (HahnSeries.ofPowerSeries_C c).symm⟩ }
  exact ⟨l.l, l.fac_left, l.fac_right⟩

theorem specMap_comp {A C D : Type} [CommRing A] [CommRing C] [CommRing D] (α : C →+* A)
    (β : D →+* C) {Y : Scheme.{0}} (f : Spec (.of D) ⟶ Y) :
    Spec.map (CommRingCat.ofHom α) ≫ Spec.map (CommRingCat.ofHom β) ≫ f =
      Spec.map (CommRingCat.ofHom (α.comp β)) ≫ f := by
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]

theorem scale_comp_eq [UniversallyClosed B.hom] {L R : Type} [Field L] [CommRing R]
    (s : Spec (.of L) ⟶ S) (f : Spec (.of (AddMonoidAlgebra L ℤ)) ⟶ B.left)
    (hf : f ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap L _)) ≫ s)
    (r : L →+* R) (t : Rˣ) (ht : IsNilpotent ((t : R) - 1)) :
    Spec.map (CommRingCat.ofHom (scale r t)) ≫ f = Spec.map (CommRingCat.ofHom (scale r 1)) ≫ f := by
  have ht' : IsNilpotent (((t⁻¹ : Rˣ) : R) - 1) := by
    have : ((t⁻¹ : Rˣ) : R) - 1 = -(t⁻¹ : Rˣ) * ((t : R) - 1) := by
      rw [mul_sub, neg_mul, Units.inv_mul]; ring
    rw [this]
    exact (Commute.all _ _).isNilpotent_mul_left ht
  obtain ⟨f₀, e₀, p₀⟩ := exists_extension B.hom s (Spec.map (CommRingCat.ofHom (atZero L)) ≫ f) (by
    rw [Category.assoc, hf, specMap_comp]
    congr 3
    exact RingHom.ext fun c ↦ atZero_const c)
  obtain ⟨f₁, e₁, p₁⟩ := exists_extension B.hom s (Spec.map (CommRingCat.ofHom (atInf L)) ≫ f) (by
    rw [Category.assoc, hf, specMap_comp]
    congr 3
    exact RingHom.ext fun c ↦ atInf_const c)
  have hs : ∀ u : Rˣ, (Spec.map (CommRingCat.ofHom (scale r u)) ≫ f) ≫ B.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap R _).comp r)) ≫ s := fun u ↦ by
    rw [Category.assoc, hf, specMap_comp]
    congr 3
    exact RingHom.ext fun c ↦ scale_single_zero r u c
  have hP : ∀ (u : Rˣ) (y : Spec (.of (PowerSeries L)) ⟶ B.left),
      y ≫ B.hom = Spec.map (CommRingCat.ofHom PowerSeries.C) ≫ s →
      (Spec.map (CommRingCat.ofHom (scaleP r u)) ≫ y) ≫ B.hom =
        Spec.map (CommRingCat.ofHom (PowerSeries.C.comp r)) ≫ s := fun u y hy ↦ by
    rw [Category.assoc, hy, specMap_comp]
    congr 3
    exact RingHom.ext fun c ↦ scaleP_C r u c
  have hL : ∀ u : Rˣ, (HahnSeries.ofPowerSeries ℤ R).comp (scaleP r u) =
      (scaleL r u).comp (HahnSeries.ofPowerSeries ℤ L) :=
    fun u ↦ RingHom.ext fun p ↦ (scaleL_coe r u p).symm
  let e : Spec (.of L) ⟶ B.left := s ≫ (η[B] : 𝟙_ (Over S) ⟶ B).left
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e default)) isOpen_univ
  have hin : ∀ {D A : Type} [CommRing D] [CommRing A] (y : Spec (.of D) ⟶ B.left)
      (α β : D →+* A) (h) (c : L →+* A), (∀ (C : Type) [CommRing C] [IsReduced C] (ρ : A →+* C),
      ρ.comp α = ρ.comp β) → (Spec.map (CommRingCat.ofHom α) ≫ y) ≫ B.hom =
        Spec.map (CommRingCat.ofHom c) ≫ s →
      Set.range (quot (Spec.map (CommRingCat.ofHom α) ≫ y)
        (Spec.map (CommRingCat.ofHom β) ≫ y) h) ⊆ U := by
    rintro D A _ _ y α β h c H hc _ ⟨z, rfl⟩
    rw [quot_apply y α β h H, ← Category.assoc, hc, Category.assoc, Scheme.Hom.comp_apply,
      Subsingleton.elim (Spec.map (CommRingCat.ofHom c) z) default]
    exact hx
  have key := eq_const_of_affine hU
    (quot _ _ ((hs 1).trans (hs t).symm)) (quot _ _ ((hP 1 f₀ p₀).trans (hP t f₀ p₀).symm))
    (quot _ _ ((hP 1 f₁ p₁).trans (hP t⁻¹ f₁ p₁).symm))
    (hin _ _ _ _ _ (fun _ _ _ ρ ↦ comp_scale r ht ρ) (hs t))
    (hin _ _ _ _ _ (fun _ _ _ ρ ↦ comp_scaleP r ht ρ) (hP t f₀ p₀))
    (hin _ _ _ _ _ (fun _ _ _ ρ ↦ comp_scaleP r ht' ρ) (hP t⁻¹ f₁ p₁))
    (by
      rw [comp_quot, comp_quot]
      refine quot_congr _ _ ?_ ?_ <;>
        rw [specMap_comp, specMap_comp, atZero_scale, hL, ← specMap_comp, ← specMap_comp, e₀])
    (by
      rw [comp_quot, comp_quot]
      refine quot_congr _ _ ?_ ?_
      · rw [specMap_comp, specMap_comp, atInf_scale, hL, ← specMap_comp, ← specMap_comp, e₁]
      · rw [specMap_comp, specMap_comp, atInf_scale, hL, inv_one, ← specMap_comp, ← specMap_comp,
          e₁])
  rw [comp_quot _ _ _ ((hP 1 f₀ p₀).trans (hP t f₀ p₀).symm), (quot_eq_iff
    (_ ≫ Spec.map (CommRingCat.ofHom (scaleP r t)) ≫ f₀) _ _).2 (by
    rw [specMap_comp, specMap_comp, constantCoeff_scaleP, constantCoeff_scaleP])] at key
  refine (quot_eq_iff _ _ ((hs 1).trans (hs t).symm)).1 (key.trans ?_)
  simp only [Category.assoc]
  rw [reassoc_of% (hs t), reassoc_of% (hP t f₀ p₀), specMap_comp, specMap_comp]
  congr 3

end Geometry

theorem _root_.GlobalTheory.laurent_point_const {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsProper B.hom]
    (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S)
    (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ B.left)
    (hf : f ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s) :
    ∃ k : Spec (CommRingCat.of L) ⟶ B.left,
      f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k := by
  refine ⟨Spec.map (CommRingCat.ofHom (evalAt (RingHom.id L) 1)) ≫ f, ?_⟩
  let I : Ideal (AddMonoidAlgebra L ℤ) := Ideal.span {(var L : AddMonoidAlgebra L ℤ) - 1}
  have hI : I ≠ ⊤ := by
    intro h
    have h1 := (Ideal.span_singleton_eq_top.1 h).map (evalAt (RingHom.id L) 1)
    rw [map_sub, map_one, evalAt_var] at h1
    simp at h1
  have : IsNoetherianRing (AddMonoidAlgebra L ℤ) :=
    Algebra.FiniteType.isNoetherianRing L _
  refine ext_of_forall_quotient B.hom ?_ (fun n ↦ I ^ n) (Ideal.iInf_pow_eq_bot_of_isDomain I hI)
    fun n ↦ ?_
  · simp only [Category.assoc, hf, specMap_comp]
    congr 3
    exact RingHom.ext fun c ↦ by simp only [RingHom.comp_apply, evalAt_const, RingHom.id_apply]
  · let ϖ := Ideal.Quotient.mk (I ^ n)
    let r : L →+* _ := ϖ.comp (algebraMap L _)
    let t := Units.map ϖ.toMonoidHom (var L)
    have ht : IsNilpotent ((t : _ ⧸ I ^ n) - 1) := ⟨n, by
      change (ϖ (var L) - 1) ^ n = 0
      rw [← map_one ϖ, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n⟩
    have h := congrArg (Spec.map (CommRingCat.ofHom (evalAt (RingHom.id _) 1)) ≫ ·)
      (scale_comp_eq s f hf r t ht)
    simp only [specMap_comp] at h ⊢
    convert h using 4 <;> refine LaurentConst.hom_ext (fun c ↦ ?_) ?_ <;>
      simp only [RingHom.comp_apply, scale_single_zero, scale_single_one, evalAt_single, one_zpow,
        Units.val_one, _root_.mul_one, RingHom.id_apply, map_one] <;> rfl

end GlobalTheory.LaurentConst
