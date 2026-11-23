import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard

open CategoryTheory Limits HomologicalComplex TensorProduct

universe v u

namespace GlobalTheory

section Retract

variable {R : Type u} [Ring R]

theorem nonempty_homology_equiv_of_retract (S : ShortComplex (ModuleCat.{v} R))
    {W : Type*} [AddCommGroup W] [Module R W] (I : W →ₗ[R] S.X₂) (Q : S.X₂ →ₗ[R] W)
    (hI : ∀ w, S.g.hom (I w) = 0) (hQ : ∀ y, Q (S.f.hom y) = 0) (hQI : ∀ w, Q (I w) = w)
    (hex : ∀ x, S.g.hom x = 0 → Q x = 0 → ∃ y, S.f.hom y = x) :
    Nonempty (S.homology ≃ₗ[R] W) := by
  let q : LinearMap.ker S.g.hom →ₗ[R] W := Q ∘ₗ (LinearMap.ker S.g.hom).subtype
  have hs : Function.Surjective q := fun w => ⟨⟨I w, hI w⟩, hQI w⟩
  have hk : LinearMap.range S.moduleCatToCycles = LinearMap.ker q := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hQ y
    · intro hx
      obtain ⟨y, hy⟩ := hex x.1 x.2 hx
      exact ⟨y, Subtype.ext hy⟩
  exact ⟨S.moduleCatHomologyIso.toLinearEquiv ≪≫ₗ Submodule.quotEquivOfEq _ _ hk ≪≫ₗ
    q.quotKerEquivOfSurjective hs⟩

end Retract

namespace Cube

section Total

variable {ι : Type} {R : Type u} [Ring R]

def restrictDeg (A : Cube.{v} ι R) (p : ℕ) : (∀ s, A.obj s) →ₗ[R] Term A p :=
  LinearMap.pi fun s => LinearMap.proj s.1

theorem restrictDeg_apply (A : Cube.{v} ι R) (p : ℕ) (x : ∀ s, A.obj s)
    (s : {s : Finset ι // s.card = p}) : restrictDeg A p x s = x s.1 := rfl

def degProj (A : Cube.{v} ι R) (p : ℕ) : Module.End R (∀ s, A.obj s) :=
  extend A p ∘ₗ restrictDeg A p

theorem degProj_apply (A : Cube.{v} ι R) (p : ℕ) (x : ∀ s, A.obj s) (s : Finset ι) :
    degProj A p x s = if s.card = p then x s else 0 := by
  by_cases h : s.card = p
  · rw [if_pos h]; exact extend_apply_of_eq A _ h
  · rw [if_neg h]; exact extend_apply_of_ne A _ h

def degSign (A : Cube.{v} ι R) : Module.End R (∀ s, A.obj s) :=
  LinearMap.pi fun s => (-1 : ℤ) ^ s.card • LinearMap.proj s

theorem degSign_apply (A : Cube.{v} ι R) (x : ∀ s, A.obj s) (s : Finset ι) :
    degSign A x s = (-1 : ℤ) ^ s.card • x s := rfl

theorem restrictDeg_extend (A : Cube.{v} ι R) (p : ℕ) (x : Term A p) :
    restrictDeg A p (extend A p x) = x :=
  funext fun s => extend_apply_of_eq A x s.2

theorem ext_restrictDeg {A : Cube.{v} ι R} {x y : ∀ s, A.obj s}
    (h : ∀ p, restrictDeg A p x = restrictDeg A p y) : x = y :=
  funext fun s => congrFun (h s.card) ⟨s, rfl⟩

theorem restrictDeg_degProj (A : Cube.{v} ι R) (p q : ℕ) (x : ∀ s, A.obj s) :
    restrictDeg A p (degProj A q x) = if p = q then restrictDeg A p x else 0 := by
  funext s
  rw [restrictDeg_apply, degProj_apply, s.2]
  split_ifs <;> rfl

theorem restrictDeg_degSign (A : Cube.{v} ι R) (p : ℕ) (x : ∀ s, A.obj s) :
    restrictDeg A p (degSign A x) = (-1 : ℤ) ^ p • restrictDeg A p x := by
  funext s
  rw [restrictDeg_apply, degSign_apply, s.2]
  rfl

theorem degProj_mul_degProj (A : Cube.{v} ι R) (p q : ℕ) :
    degProj A p * degProj A q = if p = q then degProj A p else 0 := by
  refine LinearMap.ext fun x => ?_
  change extend A p (restrictDeg A p (degProj A q x)) = _
  rw [restrictDeg_degProj]
  split_ifs
  · rfl
  · exact map_zero _

theorem degSign_mul_degSign (A : Cube.{v} ι R) : degSign A * degSign A = 1 := by
  refine LinearMap.ext fun x => funext fun s => ?_
  rw [Module.End.mul_apply, degSign_apply, degSign_apply, smul_smul, ← mul_pow]
  simp

variable [LinearOrder ι]

theorem restrictDeg_totalD_succ (A : Cube.{v} ι R) (p : ℕ) (x : ∀ s, A.obj s) :
    restrictDeg A (p + 1) (totalD A x) = d A p (restrictDeg A p x) :=
  funext fun t => (d_apply_eq_totalD A (restrictDeg A p x) x (fun _ => rfl) t).symm

theorem restrictDeg_totalD_zero (A : Cube.{v} ι R) (x : ∀ s, A.obj s) :
    restrictDeg A 0 (totalD A x) = 0 := by
  funext ⟨t, ht⟩
  obtain rfl := Finset.card_eq_zero.1 ht
  rw [restrictDeg_apply, totalD_apply]
  simp

theorem totalD_extend (A : Cube.{v} ι R) (p : ℕ) (x : Term A p) :
    totalD A (extend A p x) = extend A (p + 1) (d A p x) := by
  have key : ∀ (p q : ℕ) (x : Term A p), q ≠ p → restrictDeg A q (extend A p x) = 0 :=
    fun p q x h => funext fun s => extend_apply_of_ne A x (by rw [s.2]; exact h)
  refine ext_restrictDeg fun q => ?_
  cases q with
  | zero => rw [restrictDeg_totalD_zero, key _ _ _ (by omega)]
  | succ q =>
    rw [restrictDeg_totalD_succ]
    by_cases h : q = p
    · subst h
      rw [restrictDeg_extend, restrictDeg_extend]
    · rw [key _ _ _ h, key _ _ _ (by omega), map_zero]

theorem totalD_mul_degSign (A : Cube.{v} ι R) :
    (totalD A : Module.End R _) * degSign A = -(degSign A * totalD A) := by
  refine LinearMap.ext fun x => ext_restrictDeg fun p => ?_
  simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, restrictDeg_degSign]
  cases p with
  | zero => simp [restrictDeg_totalD_zero]
  | succ p =>
    rw [restrictDeg_totalD_succ, restrictDeg_totalD_succ, restrictDeg_degSign, map_zsmul, pow_succ]
    simp

end Total

end Cube

section Criterion

variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

open GlobalTheory.Cube

theorem nonempty_cubeHomology_equiv_of_retract (A : Cube.{v} ι R) (n : ℕ)
    {W : Type*} [AddCommGroup W] [Module R W] (I : W →ₗ[R] ∀ s, A.obj s)
    (Q : (∀ s, A.obj s) →ₗ[R] W) (hI : ∀ w, totalD A (I w) = 0)
    (hPI : ∀ w, degProj A n (I w) = I w) (hQ : ∀ y, Q (totalD A y) = 0) (hQI : ∀ w, Q (I w) = w)
    (hex : ∀ x, totalD A x = 0 → degProj A n x = x → Q x = 0 → ∃ y, totalD A y = x) :
    Nonempty ((cubeComplex A).homology n ≃ₗ[R] W) := by
  have h1 : ∀ w, d A n (restrictDeg A n (I w)) = 0 := fun w => by
    rw [← restrictDeg_totalD_succ, hI, map_zero]
  have h2 : ∀ w, Q (extend A n (restrictDeg A n (I w))) = w := fun w =>
    (congrArg Q (hPI w)).trans (hQI w)
  have h3 : ∀ x : Term A n, d A n x = 0 → Q (extend A n x) = 0 →
      ∃ y, restrictDeg A n (totalD A y) = x := fun x hx hx' => by
    obtain ⟨y, hy⟩ := hex (extend A n x) (by rw [totalD_extend, hx, map_zero])
      (congrArg (extend A n) (restrictDeg_extend A n x)) hx'
    exact ⟨y, by rw [hy, restrictDeg_extend]⟩
  have hd : ∀ (p : ℕ) (x : Term A p), ((cubeComplex A).d p (p + 1)).hom x = d A p x :=
    fun p x => by rw [cubeComplex_d]; rfl
  cases n with
  | zero =>
    have h0 : (cubeComplex A).d 0 0 = 0 := (cubeComplex A).shape 0 0 (by simp)
    obtain ⟨e⟩ := nonempty_homology_equiv_of_retract ((cubeComplex A).sc' 0 0 1)
      (restrictDeg A 0 ∘ₗ I) (Q ∘ₗ extend A 0) (fun w => (hd 0 _).trans (h1 w))
      (fun y => by
        change Q (extend A 0 (((cubeComplex A).d 0 0).hom y)) = 0
        rw [h0]
        exact (congrArg Q (map_zero _)).trans (map_zero _)) h2
      (fun x hx hx' => by
        obtain ⟨y, hy⟩ := h3 x ((hd 0 _).symm.trans hx) hx'
        rw [restrictDeg_totalD_zero] at hy
        exact ⟨0, (map_zero _).trans hy⟩)
    exact ⟨((cubeComplex A).homologyIsoSc' 0 0 1 (by simp) (by simp)).toLinearEquiv ≪≫ₗ e⟩
  | succ n =>
    obtain ⟨e⟩ := nonempty_homology_equiv_of_retract ((cubeComplex A).sc' n (n + 1) (n + 1 + 1))
      (restrictDeg A (n + 1) ∘ₗ I) (Q ∘ₗ extend A (n + 1)) (fun w => (hd (n + 1) _).trans (h1 w))
      (fun y => by
        change Q (extend A (n + 1) (((cubeComplex A).d n (n + 1)).hom y)) = 0
        exact (congrArg (fun z => Q (extend A (n + 1) z)) (hd n y)).trans
          ((congrArg Q (totalD_extend A n y).symm).trans (hQ _))) h2
      (fun x hx hx' => by
        obtain ⟨y, hy⟩ := h3 x ((hd (n + 1) _).symm.trans hx) hx'
        rw [restrictDeg_totalD_succ] at hy
        exact ⟨_, (hd n _).trans hy⟩)
    exact ⟨((cubeComplex A).homologyIsoSc' n (n + 1) (n + 1 + 1) (by simp)
      (by simp)).toLinearEquiv ≪≫ₗ e⟩

theorem nonempty_cubeHomology_equiv_of_homotopy (A : Cube.{v} ι R) (n : ℕ)
    {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (Φ : V ≃ₗ[R] ∀ s, A.obj s) (T P e h : Module.End R V)
    (hT : ∀ x, totalD A (Φ x) = Φ (T x)) (hP : ∀ x, degProj A n (Φ x) = Φ (P x))
    (hh : 1 - e = T * h + h * T) (hTe : T * e = 0) (heT : e * T = 0) (heP : P * e = e * P)
    (I : W →ₗ[R] V) (Q : V →ₗ[R] W) (hIQ : ∀ x, I (Q x) = e (P x)) (hQI : ∀ w, Q (I w) = w) :
    Nonempty ((cubeComplex A).homology n ≃ₗ[R] W) := by
  have hPe : ∀ x, P (e x) = e (P x) := fun x => congr($heP x)
  have hPP : ∀ x, P (P x) = P x := fun x => Φ.injective (by
    rw [← hP, ← hP]
    have := degProj_mul_degProj A n n
    rw [if_pos rfl] at this
    exact congr($this (Φ x)))
  have hI : ∀ w, e (P (I w)) = I w := fun w => by rw [← hIQ, hQI]
  refine nonempty_cubeHomology_equiv_of_retract A n (Φ.toLinearMap ∘ₗ I) (Q ∘ₗ Φ.symm.toLinearMap)
    (fun w => ?_) (fun w => ?_) (fun y => ?_) (fun w => by simp [hQI]) fun x hx hx' hx'' => ?_
  · change totalD A (Φ (I w)) = 0
    have : T (e (P (I w))) = 0 := congr($hTe (P (I w)))
    rw [hT, ← hI, this, map_zero]
  · change degProj A n (Φ (I w)) = Φ (I w)
    rw [hP, ← hI, hPe, hPP]
  · obtain ⟨y, rfl⟩ := Φ.surjective y
    have : e (T y) = 0 := congr($heT y)
    rw [hT]
    change Q (Φ.symm (Φ (T y))) = 0
    rw [Φ.symm_apply_apply, ← hQI (Q _), hIQ, ← hPe, this, map_zero, map_zero]
  · obtain ⟨x, rfl⟩ := Φ.surjective x
    rw [hT, map_eq_zero_iff _ Φ.injective] at hx
    rw [hP, Φ.injective.eq_iff] at hx'
    change Q (Φ.symm (Φ x)) = 0 at hx''
    rw [Φ.symm_apply_apply] at hx''
    have h1 : e x = 0 := by rw [← hx', ← hIQ, hx'', map_zero]
    have h2 : x - e x = T (h x) + h (T x) := congr($hh x)
    rw [h1, hx, map_zero, add_zero, sub_zero] at h2
    exact ⟨Φ (h x), by rw [hT, ← h2]⟩

end Criterion

section Contraction

variable {ι : Type} [LinearOrder ι] {K : Type u} [Field K]

open GlobalTheory.Cube

theorem exists_comp_comp_eq_of_field {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (f : V →ₗ[K] W) : ∃ g : W →ₗ[K] V, ∀ x, f (g (f x)) = f x := by
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨g, hg⟩ := s.exists_extend
  refine ⟨g, fun x => ?_⟩
  have h1 : g (f x) = s (f.rangeRestrict x) := congr($hg (f.rangeRestrict x))
  rw [h1]
  exact congrArg Subtype.val congr($hs (f.rangeRestrict x))

theorem Cube.exists_contraction (A : Cube.{v} ι K) : ∃ e h : Module.End K (∀ s, A.obj s),
    1 - e = (totalD A : Module.End K _) * h + h * totalD A ∧
    (totalD A : Module.End K _) * e = 0 ∧ e * totalD A = 0 ∧ e * e = e ∧
    (∀ p, degProj A p * e = e * degProj A p) ∧ degSign A * e = e * degSign A ∧
    degSign A * h = -(h * degSign A) := by
  choose g hg using fun p => exists_comp_comp_eq_of_field (d A p)
  set D : Module.End K (∀ s, A.obj s) := totalD A with hD
  let h : Module.End K (∀ s, A.obj s) := LinearMap.pi fun s =>
    LinearMap.proj (φ := fun t : {t : Finset ι // t.card = s.card} => A.obj t.1) ⟨s, rfl⟩ ∘ₗ
      g s.card ∘ₗ restrictDeg A (s.card + 1)
  have hr : ∀ p x, restrictDeg A p (h x) = g p (restrictDeg A (p + 1) x) := fun p x => by
    funext ⟨s, hs⟩
    subst hs
    rfl
  have hDD : D * D = 0 := LinearMap.ext (totalD_totalD A)
  have hDhD : D * h * D = D := LinearMap.ext fun x => ext_restrictDeg fun p => by
    simp only [Module.End.mul_apply, hD]
    cases p with
    | zero => rw [restrictDeg_totalD_zero, restrictDeg_totalD_zero]
    | succ p => rw [restrictDeg_totalD_succ, hr, restrictDeg_totalD_succ, hg]
  have hεh : degSign A * h = -(h * degSign A) := LinearMap.ext fun x => ext_restrictDeg fun p => by
    simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, restrictDeg_degSign, hr,
      map_zsmul, pow_succ]
    simp
  have hDε : D * degSign A = -(degSign A * D) := totalD_mul_degSign A
  have hP : ∀ q, degProj A q * (D * h + h * D) = (D * h + h * D) * degProj A q := fun q =>
    LinearMap.ext fun x => ext_restrictDeg fun p => by
      simp only [Module.End.mul_apply, LinearMap.add_apply, map_add, restrictDeg_degProj, hD, hr,
        restrictDeg_totalD_succ]
      cases p with
      | zero => split_ifs <;> simp [restrictDeg_totalD_zero]
      | succ p =>
        simp only [restrictDeg_totalD_succ, hr, restrictDeg_degProj]
        split_ifs <;> simp
  obtain ⟨e, he⟩ : ∃ e : Module.End K (∀ s, A.obj s), e = 1 - (D * h + h * D) := ⟨_, rfl⟩
  have h1 : D * e = 0 := by
    rw [he, mul_sub, mul_add, ← mul_assoc, ← mul_assoc, hDD, hDhD]; simp
  have h2 : e * D = 0 := by
    rw [he, sub_mul, add_mul, mul_assoc h, hDD, hDhD]; simp
  have h3 : e * e * e = e * e := by
    have : e * e * e = e * (1 - (D * h + h * D)) * e := by rw [← he]
    rw [this, mul_sub, mul_add, ← mul_assoc, h2, sub_mul, add_mul, mul_assoc e (h * D),
      mul_assoc h, h1]
    simp
  have h4 : ∀ q, degProj A q * e = e * degProj A q := fun q => by
    rw [he, mul_sub, sub_mul, hP]; simp
  have h5 : degSign A * e = e * degSign A := by
    have a1 : degSign A * (D * h) = D * h * degSign A := by
      rw [mul_assoc, ← neg_neg (h * _), ← hεh, mul_neg, ← mul_assoc D, hDε]; simp [mul_assoc]
    have a2 : degSign A * (h * D) = h * D * degSign A := by
      rw [mul_assoc, hDε, ← mul_assoc, hεh]; simp [mul_assoc]
    rw [he, mul_sub, sub_mul, mul_add, add_mul, a1, a2]; simp
  refine ⟨e * e, h + e * h, ?_, ?_, ?_, ?_, fun q => ?_, ?_, ?_⟩
  · have : e * e = e * (1 - (D * h + h * D)) := by rw [← he]
    rw [this, mul_sub, mul_add e, ← mul_assoc e D, h2, mul_add D, ← mul_assoc D e, h1, add_mul,
      ← mul_assoc]
    simp only [mul_one, zero_mul, zero_add, add_zero]
    nth_rewrite 1 [he]
    abel
  · rw [← mul_assoc, h1, zero_mul]
  · rw [mul_assoc, h2, mul_zero]
  · rw [← mul_assoc, h3, h3]
  · rw [← mul_assoc, h4, mul_assoc, h4, mul_assoc]
  · rw [← mul_assoc, h5, mul_assoc, h5, mul_assoc]
  · rw [mul_add, ← mul_assoc, h5, mul_assoc, hεh, add_mul, mul_neg, mul_assoc, neg_add]

end Contraction

section TensorAlgebra

variable {K : Type u} [CommRing K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V']

theorem tensor_homotopy {D e h ε : Module.End K V} {D' e' h' : Module.End K V'}
    (hh : 1 - e = D * h + h * D) (hDe : D * e = 0) (heD : e * D = 0) (hDε : D * ε = -(ε * D))
    (hεe : ε * e = e * ε) (hεh : ε * h = -(h * ε)) (hεε : ε * ε = 1)
    (hh' : 1 - e' = D' * h' + h' * D') :
    (1 : Module.End K (V ⊗[K] V')) - TensorProduct.map e e' =
      (TensorProduct.map D 1 + TensorProduct.map ε D') *
          (TensorProduct.map h 1 + TensorProduct.map (ε * e) h') +
        (TensorProduct.map h 1 + TensorProduct.map (ε * e) h') *
          (TensorProduct.map D 1 + TensorProduct.map ε D') := by
  have a1 : D * (ε * e) = 0 := by rw [← mul_assoc, hDε, neg_mul, mul_assoc, hDe]; simp
  have a2 : ε * (ε * e) = e := by rw [← mul_assoc, hεε, one_mul]
  have a3 : ε * e * D = 0 := by rw [mul_assoc, heD, mul_zero]
  have a4 : ε * e * ε = e := by rw [mul_assoc, ← hεe, a2]
  have a5 : D * h = 1 - e - h * D := by rw [hh]; abel
  have a6 : D' * h' = 1 - e' - h' * D' := by rw [hh']; abel
  simp only [mul_add, add_mul, ← TensorProduct.map_mul, a1, a2, a3, a4, a5, a6, hεh]
  refine TensorProduct.ext' fun x y => ?_
  simp only [LinearMap.sub_apply, LinearMap.add_apply, TensorProduct.map_tmul, Module.End.one_apply,
    LinearMap.zero_apply, LinearMap.neg_apply, mul_one, one_mul, sub_tmul, tmul_sub, neg_tmul,
    zero_tmul]
  abel

theorem rangeRestrict_comp_subtype_of_orthogonal {f : ℕ → Module.End K V}
    (hf : ∀ p q, f p * f q = if p = q then f p else 0) (p : ℕ) :
    (f p).rangeRestrict ∘ₗ (LinearMap.range (f p)).subtype = LinearMap.id := by
  refine LinearMap.ext ?_
  rintro ⟨_, x, rfl⟩
  have := hf p p
  rw [if_pos rfl] at this
  exact Subtype.ext congr($this x)

theorem rangeRestrict_comp_subtype_of_orthogonal_of_ne {f : ℕ → Module.End K V}
    (hf : ∀ p q, f p * f q = if p = q then f p else 0) {p q : ℕ} (h : p ≠ q) :
    (f p).rangeRestrict ∘ₗ (LinearMap.range (f q)).subtype = 0 := by
  refine LinearMap.ext ?_
  rintro ⟨_, x, rfl⟩
  have := hf p q
  rw [if_neg h] at this
  exact Subtype.ext congr($this x)

theorem exists_retraction_tensor_ranges {f : ℕ → Module.End K V} {g : ℕ → Module.End K V'}
    (hf : ∀ p q, f p * f q = if p = q then f p else 0)
    (hg : ∀ p q, g p * g q = if p = q then g p else 0) (S : Finset (ℕ × ℕ)) :
    ∃ (I : (∀ x : S, LinearMap.range (f x.1.1) ⊗[K] LinearMap.range (g x.1.2)) →ₗ[K] V ⊗[K] V')
      (Q : V ⊗[K] V' →ₗ[K] ∀ x : S, LinearMap.range (f x.1.1) ⊗[K] LinearMap.range (g x.1.2)),
      (∀ z, I (Q z) = ∑ x ∈ S, TensorProduct.map (f x.1) (g x.2) z) ∧ ∀ w, Q (I w) = w := by
  refine ⟨∑ x : S, TensorProduct.map (LinearMap.range (f x.1.1)).subtype
      (LinearMap.range (g x.1.2)).subtype ∘ₗ LinearMap.proj x,
    LinearMap.pi fun x => TensorProduct.map (f x.1.1).rangeRestrict (g x.1.2).rangeRestrict,
    fun z => ?_, fun w => funext fun x => ?_⟩
  · rw [LinearMap.sum_apply, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.pi_apply]
    rw [TensorProduct.map_map]
    rfl
  · rw [LinearMap.sum_apply, LinearMap.pi_apply, map_sum, Finset.sum_eq_single x]
    · simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [TensorProduct.map_map, rangeRestrict_comp_subtype_of_orthogonal hf,
        rangeRestrict_comp_subtype_of_orthogonal hg, TensorProduct.map_id, LinearMap.id_apply]
    · intro y _ hy
      simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [TensorProduct.map_map]
      by_cases h : x.1.1 = y.1.1
      · have h' : x.1.2 ≠ y.1.2 := fun h' => hy (Subtype.ext (Prod.ext h h')).symm
        rw [rangeRestrict_comp_subtype_of_orthogonal_of_ne hg h', TensorProduct.map_zero_right,
          LinearMap.zero_apply]
      · rw [rangeRestrict_comp_subtype_of_orthogonal_of_ne hf h, TensorProduct.map_zero_left,
          LinearMap.zero_apply]
    · simp

end TensorAlgebra

namespace Cube

section ExtTensor

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {K : Type u} [CommRing K]

noncomputable def extTensor (A : Cube.{v} ι K) (B : Cube.{v} κ K) : Cube.{v} (ι ⊕ₗ κ) K :=
  mk (fun w => ModuleCat.of K (A.obj (part (inlEmb ι κ) w) ⊗[K] B.obj (part (inrEmb ι κ) w)))
    (fun h => TensorProduct.map (res A (monotone_part _ h)) (res B (monotone_part _ h)))
    (fun _ x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => rw [map_add, hx, hy])
    (fun _ _ x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add])

theorem extTensor_obj (A : Cube.{v} ι K) (B : Cube.{v} κ K) (w : Finset (ι ⊕ₗ κ)) :
    (extTensor A B).obj w =
      ModuleCat.of K (A.obj (part (inlEmb ι κ) w) ⊗[K] B.obj (part (inrEmb ι κ) w)) := rfl

theorem res_extTensor (A : Cube.{v} ι K) (B : Cube.{v} κ K) {w w' : Finset (ι ⊕ₗ κ)}
    (h : w ⊆ w') : res (extTensor A B) h =
      TensorProduct.map (res A (monotone_part _ h)) (res B (monotone_part _ h)) := rfl

theorem sum_parts {M : Type*} [AddCommMonoid M] (w : Finset (ι ⊕ₗ κ)) (F : ι ⊕ₗ κ → M) :
    ∑ j ∈ w, F j = ∑ i ∈ part (inlEmb ι κ) w, F (inlEmb ι κ i) +
      ∑ k ∈ part (inrEmb ι κ) w, F (inrEmb ι κ k) := by
  conv_lhs => rw [← sumVertex_part w, sumVertex_eq_map_disjSum, Finset.sum_map, Finset.sum_disjSum]
  rfl

theorem card_parts (w : Finset (ι ⊕ₗ κ)) :
    w.card = (part (inlEmb ι κ) w).card + (part (inrEmb ι κ) w).card := by
  simp only [Finset.card_eq_sum_ones]
  exact sum_parts w _

theorem cubeSign_inlEmb (w : Finset (ι ⊕ₗ κ)) (i : ι) :
    cubeSign w (inlEmb ι κ i) = cubeSign (part (inlEmb ι κ) w) i := by
  have h1 : part (inlEmb ι κ) (w.filter (· < inlEmb ι κ i)) =
      (part (inlEmb ι κ) w).filter (· < i) := by
    ext; rw [mem_part, Finset.mem_filter]; simp
  have h2 : part (inrEmb ι κ) (w.filter (· < inlEmb ι κ i)) = ∅ := by
    ext; rw [mem_part, Finset.mem_filter]; simp
  rw [cubeSign, card_parts, h1, h2, cubeSign]
  simp

theorem cubeSign_inrEmb (w : Finset (ι ⊕ₗ κ)) (k : κ) :
    cubeSign w (inrEmb ι κ k) =
      (-1) ^ (part (inlEmb ι κ) w).card * cubeSign (part (inrEmb ι κ) w) k := by
  have h1 : part (inlEmb ι κ) (w.filter (· < inrEmb ι κ k)) = part (inlEmb ι κ) w := by
    ext; rw [mem_part, Finset.mem_filter]; simp
  have h2 : part (inrEmb ι κ) (w.filter (· < inrEmb ι κ k)) =
      (part (inrEmb ι κ) w).filter (· < k) := by
    ext; rw [mem_part, Finset.mem_filter]; simp
  rw [cubeSign, card_parts, h1, h2, cubeSign, pow_add]

variable (ι κ) in

noncomputable def partsEquiv : Finset (ι ⊕ₗ κ) ≃ Σ _ : Finset ι, Finset κ where
  toFun w := ⟨part (inlEmb ι κ) w, part (inrEmb ι κ) w⟩
  invFun x := sumVertex x.1 x.2
  left_inv := sumVertex_part
  right_inv x := by simp

noncomputable def totalTensorEquiv [Finite ι] [Finite κ] (A : Cube.{v} ι K) (B : Cube.{v} κ K) :
    (∀ s, A.obj s) ⊗[K] (∀ t, B.obj t) ≃ₗ[K] ∀ w, (extTensor A B).obj w :=
  haveI := Fintype.ofFinite ι
  haveI := Fintype.ofFinite κ
  TensorProduct.piLeft K (∀ t, B.obj t) (fun s => A.obj s) ≪≫ₗ
    (LinearEquiv.piCongrRight fun s => TensorProduct.piRight K K (A.obj s) fun t => B.obj t) ≪≫ₗ
    (LinearEquiv.piCurry K fun (s : Finset ι) (t : Finset κ) => A.obj s ⊗[K] B.obj t).symm ≪≫ₗ
    (LinearEquiv.piCongrLeft K (fun x : Σ _ : Finset ι, Finset κ => A.obj x.1 ⊗[K] B.obj x.2)
      (partsEquiv ι κ)).symm

variable [Finite ι] [Finite κ] (A : Cube.{v} ι K) (B : Cube.{v} κ K)

theorem totalTensorEquiv_tmul (x : ∀ s, A.obj s) (y : ∀ t, B.obj t) (w : Finset (ι ⊕ₗ κ)) :
    totalTensorEquiv A B (x ⊗ₜ y) w = x (part (inlEmb ι κ) w) ⊗ₜ[K] y (part (inrEmb ι κ) w) := rfl

theorem totalD_totalTensorEquiv (z : (∀ s, A.obj s) ⊗[K] (∀ t, B.obj t)) :
    totalD (extTensor A B) (totalTensorEquiv A B z) = totalTensorEquiv A B
      ((TensorProduct.map (totalD A) 1 + TensorProduct.map (degSign A) (totalD B) :
        Module.End K _) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    funext w
    rw [LinearMap.add_apply, map_add, Pi.add_apply, TensorProduct.map_tmul, TensorProduct.map_tmul,
      totalTensorEquiv_tmul, totalTensorEquiv_tmul, totalD_apply, totalD_apply, totalD_apply,
      sum_parts, sum_tmul, tmul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
      (Finset.sum_congr rfl fun k _ => ?_)
    · have h1 : part (inlEmb ι κ) (w.erase (inlEmb ι κ i)) = (part (inlEmb ι κ) w).erase i := by
        ext; simp
      have h2 : part (inrEmb ι κ) (w.erase (inlEmb ι κ i)) = part (inrEmb ι κ) w := by
        ext; simp
      have h3 : res (extTensor A B) (Finset.erase_subset (inlEmb ι κ i) w)
          (totalTensorEquiv A B (x ⊗ₜ y) _) = _ :=
        congrArg₂ (fun a b => a ⊗ₜ[K] b) (res_congr A x h1 _ (Finset.erase_subset _ _))
          ((res_congr B y h2 _ (subset_refl _)).trans (res_self B _ _))
      refine (congrArg (cubeSign w (inlEmb ι κ i) • ·) h3).trans ?_
      rw [cubeSign_inlEmb]
      rfl
    · have h1 : part (inlEmb ι κ) (w.erase (inrEmb ι κ k)) = part (inlEmb ι κ) w := by
        ext; simp
      have h2 : part (inrEmb ι κ) (w.erase (inrEmb ι κ k)) = (part (inrEmb ι κ) w).erase k := by
        ext; simp
      have h3 : res (extTensor A B) (Finset.erase_subset (inrEmb ι κ k) w)
          (totalTensorEquiv A B (x ⊗ₜ y) _) = _ :=
        congrArg₂ (fun a b => a ⊗ₜ[K] b) ((res_congr A x h1 _ (subset_refl _)).trans (res_self A _ _))
          (res_congr B y h2 _ (Finset.erase_subset _ _))
      refine (congrArg (cubeSign w (inrEmb ι κ k) • ·) h3).trans ?_
      rw [cubeSign_inrEmb, degSign_apply, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
        smul_smul, mul_comm]
      rfl

theorem degProj_totalTensorEquiv (n : ℕ) (z : (∀ s, A.obj s) ⊗[K] (∀ t, B.obj t)) :
    degProj (extTensor A B) n (totalTensorEquiv A B z) = totalTensorEquiv A B
      ((∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, TensorProduct.map (degProj A x.1) (degProj B x.2) :
        Module.End K _) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    funext w
    rw [LinearMap.sum_apply, map_sum, Finset.sum_apply, degProj_apply,
      card_parts]
    have h : ∀ p : ℕ × ℕ, totalTensorEquiv A B
        (TensorProduct.map (degProj A p.1) (degProj B p.2) (x ⊗ₜ y)) w =
        if ((part (inlEmb ι κ) w).card, (part (inrEmb ι κ) w).card) = p then
          totalTensorEquiv A B (x ⊗ₜ y) w else 0 := fun p => by
      rw [TensorProduct.map_tmul, totalTensorEquiv_tmul, totalTensorEquiv_tmul, degProj_apply,
        degProj_apply]
      by_cases h1 : (part (inlEmb ι κ) w).card = p.1
      · by_cases h2 : (part (inrEmb ι κ) w).card = p.2
        · rw [if_pos h1, if_pos h2]
          exact (if_pos (Prod.ext h1 h2)).symm
        · rw [if_neg h2, tmul_zero]
          exact (if_neg fun h => h2 (congrArg Prod.snd h)).symm
      · rw [if_neg h1, zero_tmul]
        exact (if_neg fun h => h1 (congrArg Prod.fst h)).symm
    rw [Finset.sum_congr rfl fun p _ => h p, Finset.sum_ite_eq]
    simp only [Finset.HasAntidiagonal.mem_antidiagonal]

omit [Finite ι] [Finite κ]

variable {A B}

noncomputable def extTensorMap {A' : Cube.{v} ι K} {B' : Cube.{v} κ K} (φ : A ⟶ A') (ψ : B ⟶ B') :
    extTensor A B ⟶ extTensor A' B' :=
  homMk (A := extTensor A B) (B := extTensor A' B')
    (fun w => TensorProduct.map (φ.app (part (inlEmb ι κ) w)).hom (ψ.app (part (inrEmb ι κ) w)).hom)
    fun {w w'} h x => by
      have : TensorProduct.map (φ.app (part (inlEmb ι κ) w')).hom
            (ψ.app (part (inrEmb ι κ) w')).hom ∘ₗ
          TensorProduct.map (res A (monotone_part _ h)) (res B (monotone_part _ h)) =
          TensorProduct.map (res A' (monotone_part _ h)) (res B' (monotone_part _ h)) ∘ₗ
            TensorProduct.map (φ.app (part (inlEmb ι κ) w)).hom
              (ψ.app (part (inrEmb ι κ) w)).hom :=
        TensorProduct.ext' fun a b => congrArg₂ (fun a b => a ⊗ₜ[K] b) (app_res φ _ a)
          (app_res ψ _ b)
      exact LinearMap.congr_fun this x

variable (A B)

noncomputable def trunc₂ExtTensorIso :
    trunc₂ (extTensor A B) ≅ extTensor (trunc₁ A) (trunc₁ B) :=
  (trunc₂Iso (extTensorMap (trunc₁Incl A) (trunc₁Incl B)) fun s t hs ht =>
    TensorProduct.map_bijective (trunc₁Incl_bijective A (by simpa using hs))
      (trunc₁Incl_bijective B (by simpa using ht))).symm ≪≫
  @asIso _ _ _ _ (trunc₂Incl _) (isIso_of_bijective _ fun w => by
    obtain ⟨s, t, rfl⟩ : ∃ s t, w = sumVertex s t := ⟨_, _, (sumVertex_part w).symm⟩
    by_cases h : s = ∅ ∨ t = ∅
    · have := subsingleton_trunc₂ (extTensor (trunc₁ A) (trunc₁ B)) h
      have : Subsingleton ((extTensor (trunc₁ A) (trunc₁ B)).obj (sumVertex s t)) := by
        rw [extTensor_obj, part_inlEmb_sumVertex, part_inrEmb_sumVertex]
        rcases h with rfl | rfl
        · have := subsingleton_trunc₁_empty A
          exact inferInstanceAs (Subsingleton (_ ⊗[K] _))
        · have := subsingleton_trunc₁_empty B
          exact inferInstanceAs (Subsingleton (_ ⊗[K] _))
      exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
    · rw [not_or] at h
      exact trunc₂Incl_bijective _ (Finset.nonempty_iff_ne_empty.2 h.1)
        (Finset.nonempty_iff_ne_empty.2 h.2))

theorem nonempty_trunc₂_iso_extTensor (C : Cube.{v} (ι ⊕ₗ κ) K)
    (μ : ∀ (s : Finset ι) (t : Finset κ), s.Nonempty → t.Nonempty →
      A.obj s ⊗[K] B.obj t →ₗ[K] C.obj (sumVertex s t))
    (hμ : ∀ s t hs ht, Function.Bijective (μ s t hs ht))
    (hnat : ∀ {s s' : Finset ι} {t t' : Finset κ} (hs : s.Nonempty) (ht : t.Nonempty)
      (h : s ⊆ s') (h' : t ⊆ t') (a : A.obj s) (b : B.obj t),
      μ s' t' (hs.mono h) (ht.mono h') (res A h a ⊗ₜ res B h' b) =
        res C (sumVertex_mono h h') (μ s t hs ht (a ⊗ₜ b))) :
    Nonempty (trunc₂ C ≅ trunc₂ (extTensor A B)) := by
  classical
  have hP := ordConnected_partsIn (inlEmb ι κ) (inrEmb ι κ) ordConnected_nonempty
    ordConnected_nonempty
  have hb : ∀ {w w' : Finset (ι ⊕ₗ κ)} (_ : w = w') (h : w ⊆ w'),
      Function.Bijective (res C h) := by
    rintro w _ rfl h
    have : ⇑(res C h) = id := funext (res_self C h)
    rw [this]
    exact Function.bijective_id
  let ν : ∀ w, w ∈ partsIn (inlEmb ι κ) (inrEmb ι κ) {s | s.Nonempty} {t | t.Nonempty} →
      (extTensor A B).obj w →ₗ[K] C.obj w := fun w hw =>
    res C (sumVertex_part w).le ∘ₗ μ _ _ hw.1 hw.2
  have hν : ∀ {w w'} (h : w ⊆ w') hw hw' (x : (extTensor A B).obj w),
      ν w' hw' (res (extTensor A B) h x) = res C h (ν w hw x) := fun {w w'} h hw hw' x => by
    have : ν w' hw' ∘ₗ res (extTensor A B) h = res C h ∘ₗ ν w hw :=
      TensorProduct.ext' fun a b => (congrArg (res C (sumVertex_part w').le)
        (hnat hw.1 hw.2 (monotone_part _ h) (monotone_part _ h) a b)).trans
        ((res_res C _ _ _).trans (res_res C _ _ _).symm)
    exact LinearMap.congr_fun this x
  let φ : supp (extTensor A B) _ hP ⟶ C :=
    homMk (fun w => if hw : _ then ν w hw ∘ₗ (suppEquiv _ hP hw).toLinearMap else 0)
      fun {w w'} h x => by
        by_cases hw : w ∈ partsIn (inlEmb ι κ) (inrEmb ι κ) {s | s.Nonempty} {t | t.Nonempty}
        · have hw' := isUpperSet_partsIn_nonempty _ _ h hw
          simp only [dif_pos hw, dif_pos hw', LinearMap.comp_apply, LinearEquiv.coe_coe]
          rw [suppEquiv_res h hw hw', hν h hw hw']
        · have := subsingleton_supp (extTensor A B) hP hw
          rw [Subsingleton.elim x 0]
          simp only [map_zero]
  refine ⟨(trunc₂Iso φ fun s t hs ht => ?_).symm ≪≫
    trunc₂Iso (trunc₂Incl (extTensor A B)) fun s t hs ht => trunc₂Incl_bijective _ hs ht⟩
  have hw : sumVertex s t ∈ partsIn (inlEmb ι κ) (inrEmb ι κ) {s | s.Nonempty} {t | t.Nonempty} := by
    simp [hs, ht]
  have : (φ.app (sumVertex s t)).hom = ν _ hw ∘ₗ (suppEquiv _ hP hw).toLinearMap := dif_pos hw
  rw [this]
  exact ((hb (sumVertex_part _) _).comp (hμ _ _ hw.1 hw.2)).comp (suppEquiv _ hP hw).bijective

end ExtTensor

end Cube

section Kuenneth

open GlobalTheory.Cube Finset.HasAntidiagonal Module

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Finite ι] [Finite κ] {K : Type u} [Field K]

theorem nonempty_cubeHomology_extTensor_equiv (A : Cube.{v} ι K) (B : Cube.{v} κ K) (n : ℕ) :
    Nonempty ((cubeComplex (extTensor A B)).homology n ≃ₗ[K] ∀ x : antidiagonal n,
      (cubeComplex A).homology x.1.1 ⊗[K] (cubeComplex B).homology x.1.2) := by
  obtain ⟨e, h, hh, hDe, heD, hee, hPe, hεe, hεh⟩ := A.exists_contraction
  obtain ⟨e', h', hh', hDe', heD', hee', hPe', -, -⟩ := B.exists_contraction
  have orth : ∀ {ι : Type} (A : Cube.{v} ι K) (e : Module.End K (∀ s, A.obj s)), e * e = e →
      (∀ p, degProj A p * e = e * degProj A p) → ∀ p q, (e * degProj A p) * (e * degProj A q) =
        if p = q then e * degProj A p else 0 := fun A e hee hPe p q => by
    rw [mul_assoc, ← mul_assoc (degProj A p), hPe, ← mul_assoc, ← mul_assoc, hee, mul_assoc,
      degProj_mul_degProj]
    split_ifs <;> simp
  have hA := fun p => nonempty_cubeHomology_equiv_of_homotopy A p (LinearEquiv.refl K _) _ _ e h
    (fun _ => rfl) (fun _ => rfl) hh hDe heD (hPe p) (LinearMap.range (e * degProj A p)).subtype
    (e * degProj A p).rangeRestrict (fun _ => rfl)
    (fun w => congr($(rangeRestrict_comp_subtype_of_orthogonal (orth A e hee hPe) p) w))
  have hB := fun p => nonempty_cubeHomology_equiv_of_homotopy B p (LinearEquiv.refl K _) _ _ e' h'
    (fun _ => rfl) (fun _ => rfl) hh' hDe' heD' (hPe' p)
    (LinearMap.range (e' * degProj B p)).subtype (e' * degProj B p).rangeRestrict (fun _ => rfl)
    (fun w => congr($(rangeRestrict_comp_subtype_of_orthogonal (orth B e' hee' hPe') p) w))
  obtain ⟨I, Q, hIQ, hQI⟩ := exists_retraction_tensor_ranges (orth A e hee hPe)
    (orth B e' hee' hPe') (antidiagonal n)
  obtain ⟨E⟩ := nonempty_cubeHomology_equiv_of_homotopy (extTensor A B) n (totalTensorEquiv A B)
    _ _ (TensorProduct.map e e') _ (totalD_totalTensorEquiv A B) (degProj_totalTensorEquiv A B n)
    (tensor_homotopy hh hDe heD (totalD_mul_degSign A) hεe hεh (degSign_mul_degSign A) hh')
    (by simp [add_mul, ← TensorProduct.map_mul, hDe, hDe'])
    (by simp [mul_add, ← TensorProduct.map_mul, heD, heD'])
    (by simp only [Finset.sum_mul, Finset.mul_sum, ← TensorProduct.map_mul, hPe, hPe']) I Q
    (fun z => by
      rw [hIQ, ← Module.End.mul_apply, Finset.mul_sum, LinearMap.sum_apply]
      simp only [TensorProduct.map_mul]) hQI
  exact ⟨E ≪≫ₗ LinearEquiv.piCongrRight fun x =>
    TensorProduct.congr (hA x.1.1).some.symm (hB x.1.2).some.symm⟩

theorem cube_kuenneth (A : Cube.{v} ι K) (B : Cube.{v} κ K)
    (hA : ∀ p, Module.Finite K ((cubeComplex A).homology p))
    (hB : ∀ q, Module.Finite K ((cubeComplex B).homology q)) (n : ℕ) :
    Module.Finite K ((cubeComplex (extTensor A B)).homology n) ∧
      finrank K ((cubeComplex (extTensor A B)).homology n) = ∑ x ∈ antidiagonal n,
        finrank K ((cubeComplex A).homology x.1) * finrank K ((cubeComplex B).homology x.2) := by
  obtain ⟨E⟩ := nonempty_cubeHomology_extTensor_equiv A B n
  refine ⟨Module.Finite.equiv E.symm, ?_⟩
  rw [E.finrank_eq, Module.finrank_pi_fintype, ← Finset.sum_coe_sort (antidiagonal n)]
  exact Finset.sum_congr rfl fun x _ => Module.finrank_tensorProduct

theorem cech_kuenneth (A : Cube.{v} ι K) (B : Cube.{v} κ K)
    (hA : ∀ p, Module.Finite K ((cechComplex A).homology p))
    (hB : ∀ q, Module.Finite K ((cechComplex B).homology q)) (n : ℕ) :
    Module.Finite K ((cubeComplex (trunc₂ (extTensor A B))).homology (n + 2)) ∧
      finrank K ((cubeComplex (trunc₂ (extTensor A B))).homology (n + 2)) = ∑ x ∈ antidiagonal n,
        finrank K ((cechComplex A).homology x.1) * finrank K ((cechComplex B).homology x.2) := by
  have h0 : ∀ {ι : Type} [LinearOrder ι] (A : Cube.{v} ι K),
      Subsingleton ((cubeComplex (trunc₁ A)).homology 0) := fun A =>
    ModuleCat.subsingleton_of_isZero
      ((exactAt_iff_isZero_homology _ _).1 (cubeComplex_trunc₁_exactAt_zero A))
  have hf : ∀ {ι : Type} [LinearOrder ι] (A : Cube.{v} ι K),
      (∀ p, Module.Finite K ((cechComplex A).homology p)) →
      ∀ p, Module.Finite K ((cubeComplex (trunc₁ A)).homology p) := fun A hA p => by
    cases p with
    | zero => have := h0 A; infer_instance
    | succ p => exact Module.Finite.equiv (truncHomologyIso A p).toLinearEquiv.symm
  obtain ⟨h1, h2⟩ := cube_kuenneth (trunc₁ A) (trunc₁ B) (hf A hA) (hf B hB) (n + 2)
  let E := (cubeHomologyMapIso (trunc₂ExtTensorIso A B) (n + 2)).toLinearEquiv
  refine ⟨Module.Finite.equiv E.symm, ?_⟩
  have := h0 A
  have := h0 B
  rw [E.finrank_eq, h2, Finset.Nat.antidiagonal_succ_succ', Finset.sum_cons, Finset.sum_cons,
    Finset.sum_map, Module.finrank_zero_of_subsingleton (M := (cubeComplex (trunc₁ A)).homology 0),
    Module.finrank_zero_of_subsingleton (M := (cubeComplex (trunc₁ B)).homology 0), zero_mul,
    mul_zero, zero_add, zero_add]
  exact Finset.sum_congr rfl fun x _ => congrArg₂ (· * ·)
    (truncHomologyIso A x.1).toLinearEquiv.finrank_eq
    (truncHomologyIso B x.2).toLinearEquiv.finrank_eq

theorem cech_kuenneth_of_bijective (A : Cube.{v} ι K) (B : Cube.{v} κ K)
    (C : Cube.{v} (ι ⊕ₗ κ) K)
    (μ : ∀ (s : Finset ι) (t : Finset κ), s.Nonempty → t.Nonempty →
      A.obj s ⊗[K] B.obj t →ₗ[K] C.obj (sumVertex s t))
    (hμ : ∀ s t hs ht, Function.Bijective (μ s t hs ht))
    (hnat : ∀ {s s' : Finset ι} {t t' : Finset κ} (hs : s.Nonempty) (ht : t.Nonempty)
      (h : s ⊆ s') (h' : t ⊆ t') (a : A.obj s) (b : B.obj t),
      μ s' t' (hs.mono h) (ht.mono h') (res A h a ⊗ₜ res B h' b) =
        res C (sumVertex_mono h h') (μ s t hs ht (a ⊗ₜ b)))
    (hA : ∀ p, Module.Finite K ((cechComplex A).homology p))
    (hB : ∀ q, Module.Finite K ((cechComplex B).homology q)) (n : ℕ) :
    Module.Finite K ((cubeComplex (trunc₂ C)).homology (n + 2)) ∧
      finrank K ((cubeComplex (trunc₂ C)).homology (n + 2)) = ∑ x ∈ antidiagonal n,
        finrank K ((cechComplex A).homology x.1) * finrank K ((cechComplex B).homology x.2) := by
  obtain ⟨φ⟩ := nonempty_trunc₂_iso_extTensor A B C μ hμ hnat
  obtain ⟨h1, h2⟩ := cech_kuenneth A B hA hB n
  let E := (cubeHomologyMapIso φ (n + 2)).toLinearEquiv
  exact ⟨Module.Finite.equiv E.symm, E.finrank_eq.trans h2⟩

end Kuenneth

end GlobalTheory
