import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.XSmulMemWeightedHomogeneousSubmodule
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.WeightAddLeOfMemSupportDividedContraction

open DirectSum MvPolynomial

noncomputable section

namespace GlobalTheory

open GradedHilbert

section Internal

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem grProj_sum (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (T : Finset ℤ) (v : ℤ → M)
    (hv : ∀ j ∈ T, v j ∈ ℳ j) {n : ℤ} (hn : n ∈ T) : proj ℳ n (∑ j ∈ T, v j) = v n := by
  rw [map_sum, Finset.sum_eq_single n (fun j hj h => proj_of_mem_ne ℳ (hv j hj) h)
    (fun h => absurd hn h), proj_of_mem ℳ (hv n hn)]

theorem exists_sum_grProj (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (m : M) :
    ∃ T : Finset ℤ, ∑ j ∈ T, proj ℳ j m = m := by
  classical
  exact ⟨_, DirectSum.sum_support_decompose ℳ m⟩

theorem isInternal_of_sum_eq_zero (ℳ : ℤ → Submodule R M)
    (h₁ : ∀ (T : Finset ℤ) (v : ℤ → M), (∀ j ∈ T, v j ∈ ℳ j) → ∑ j ∈ T, v j = 0 →
      ∀ j ∈ T, v j = 0) (h₂ : ∀ m, m ∈ ⨆ j, ℳ j) : IsInternal ℳ :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top ℳ).2
    ⟨(iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero ℳ).2 h₁, eq_top_iff.2 fun m _ => h₂ m⟩

end Internal

section Poly

variable (ι : Type*) (R : Type*) [CommRing R]

def polyGrading : ℤ → Submodule R (MvPolynomial ι R) :=
  weightedHomogeneousSubmodule R (fun _ : ι => (1 : ℤ))

instance polyGrading.gradedAlgebra : GradedAlgebra (polyGrading ι R) :=
  weightedGradedAlgebra R (fun _ : ι => (1 : ℤ))

variable {ι R}

theorem weight_one_int (a : ι →₀ ℕ) :
    Finsupp.weight (fun _ : ι => (1 : ℤ)) a = (a.degree : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]

theorem mem_polyGrading_iff {p : MvPolynomial ι R} {n : ℤ} :
    p ∈ polyGrading ι R n ↔ ∀ a, coeff a p ≠ 0 → (a.degree : ℤ) = n := by
  simp only [polyGrading, mem_weightedHomogeneousSubmodule, IsWeightedHomogeneous, weight_one_int]

theorem mem_polyGrading_natCast {p : MvPolynomial ι R} {d : ℕ} :
    p ∈ polyGrading ι R d ↔ p.IsHomogeneous d := by
  simp only [mem_polyGrading_iff, IsHomogeneous, IsWeightedHomogeneous, Nat.cast_inj,
    Finsupp.degree_eq_weight_one]
  rfl

variable (ι R) in

theorem polyGrading_natCast (d : ℕ) : polyGrading ι R d = homogeneousSubmodule ι R d :=
  Submodule.ext fun _ => mem_polyGrading_natCast

variable (ι R) in

theorem polyGrading_of_neg {n : ℤ} (hn : n < 0) : polyGrading ι R n = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  ext a
  by_contra h
  have := mem_polyGrading_iff.1 hp a h
  omega

theorem X_mem_polyGrading (i : ι) : (X i : MvPolynomial ι R) ∈ polyGrading ι R 1 :=
  mem_polyGrading_natCast (d := 1).2 (isHomogeneous_X R i)

theorem monomial_mem_polyGrading (a : ι →₀ ℕ) (r : R) :
    monomial a r ∈ polyGrading ι R (a.degree : ℤ) :=
  mem_polyGrading_natCast.2 (isHomogeneous_monomial r rfl)

end Poly

section Module

variable {ι : Type*} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]

variable (ι) in

abbrev PolyGradedSMul (ℳ : ℤ → Submodule R M) : Prop :=
  SetLike.GradedSMul (polyGrading ι R) ℳ

theorem grSMul_mem (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {p : MvPolynomial ι R} {d n : ℤ}
    {m : M} (hp : p ∈ polyGrading ι R d) (hm : m ∈ ℳ n) : p • m ∈ ℳ (n + d) := by
  rw [add_comm]
  exact SetLike.GradedSMul.smul_mem hp hm

theorem X_smul_mem_gr (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] (i : ι) (n : ℤ) (m : M)
    (hm : m ∈ ℳ n) : (X i : MvPolynomial ι R) • m ∈ ℳ (n + 1) :=
  grSMul_mem ℳ (X_mem_polyGrading i) hm

theorem polyGradedSMul_of_X_smul_mem [IsScalarTower R (MvPolynomial ι R) M]
    (ℳ : ℤ → Submodule R M)
    (hX : ∀ (i : ι) (n : ℤ), ∀ m ∈ ℳ n, (X i : MvPolynomial ι R) • m ∈ ℳ (n + 1)) :
    PolyGradedSMul ι ℳ where
  smul_mem d n p m hp hm := by
    rcases lt_or_ge d 0 with hd | hd
    · rw [polyGrading_of_neg ι R hd, Submodule.mem_bot] at hp
      rw [hp, zero_smul]
      exact zero_mem _
    · lift d to ℕ using hd
      rw [vadd_eq_add, add_comm]
      exact smul_mem_of_isHomogeneous ℳ hX (mem_polyGrading_natCast.1 hp) n m hm

theorem polyGradedSMul_iff [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) :
    PolyGradedSMul ι ℳ ↔
      ∀ (i : ι) (n : ℤ), ∀ m ∈ ℳ n, (X i : MvPolynomial ι R) • m ∈ ℳ (n + 1) :=
  ⟨fun _ => X_smul_mem_gr ℳ, polyGradedSMul_of_X_smul_mem ℳ⟩

def IsGradedMap (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N)
    (f : M →ₗ[MvPolynomial ι R] N) : Prop :=
  ∀ ⦃n : ℤ⦄ ⦃m : M⦄, m ∈ ℳ n → f m ∈ 𝒩 n

namespace IsGradedMap

variable {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {𝒬 : ℤ → Submodule R P}

variable (ι ℳ) in

theorem id : IsGradedMap ℳ ℳ (LinearMap.id : M →ₗ[MvPolynomial ι R] M) := fun _ _ h => h

variable (ι ℳ 𝒩) in

theorem zero : IsGradedMap ℳ 𝒩 (0 : M →ₗ[MvPolynomial ι R] N) := fun _ _ _ => zero_mem _

theorem comp {g : N →ₗ[MvPolynomial ι R] P} {f : M →ₗ[MvPolynomial ι R] N}
    (hg : IsGradedMap 𝒩 𝒬 g) (hf : IsGradedMap ℳ 𝒩 f) : IsGradedMap ℳ 𝒬 (g ∘ₗ f) :=
  fun _ _ h => hg (hf h)

theorem add {f g : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (hg : IsGradedMap ℳ 𝒩 g) :
    IsGradedMap ℳ 𝒩 (f + g) := fun _ _ h => add_mem (hf h) (hg h)

theorem neg {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) :
    IsGradedMap ℳ 𝒩 (-f) := fun _ _ h => neg_mem (hf h)

theorem sum {κ : Type*} (T : Finset κ) {f : κ → M →ₗ[MvPolynomial ι R] N}
    (hf : ∀ k ∈ T, IsGradedMap ℳ 𝒩 (f k)) : IsGradedMap ℳ 𝒩 (∑ k ∈ T, f k) := fun _ _ h => by
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun k hk => hf k hk h

variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) P]

def piece {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) : ℳ n →ₗ[R] 𝒩 n :=
  (f.restrictScalars R).restrict fun _ h => hf h

@[simp]
theorem coe_piece {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) (m : ℳ n) :
    (hf.piece n m : N) = f m := rfl

variable [Decomposition ℳ] [Decomposition 𝒩]

theorem proj_apply {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (n : ℤ) (m : M) :
    proj 𝒩 n (f m) = f (proj ℳ n m) := by
  simpa using proj_map ℳ 𝒩 (f.restrictScalars R) 0 (fun n m hm => by simpa using hf hm) n m

theorem isHomogeneous_ker {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) :
    (LinearMap.ker f).IsHomogeneous ℳ := fun n m hm => by
  change f (proj ℳ n m) = 0
  rw [← hf.proj_apply, LinearMap.mem_ker.1 hm, map_zero]

theorem isHomogeneous_range {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) :
    (LinearMap.range f).IsHomogeneous 𝒩 := by
  rintro n _ ⟨m, rfl⟩
  exact ⟨_, (hf.proj_apply n m).symm⟩

theorem exists_mem_of_mem_range {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) {n : ℤ}
    {y : N} (hy : y ∈ 𝒩 n) (h : y ∈ LinearMap.range f) : ∃ m ∈ ℳ n, f m = y := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨proj ℳ n m, proj_mem _ _ _, by rw [← hf.proj_apply, proj_of_mem _ hy]⟩

theorem injective_iff {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) :
    Function.Injective f ↔ ∀ n, Function.Injective (hf.piece n) := by
  refine ⟨fun h n a b hab => Subtype.ext (h (congrArg Subtype.val hab)), fun h => ?_⟩
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨T, hT⟩ := exists_sum_grProj ℳ m
  rw [← hT]
  refine Finset.sum_eq_zero fun n _ => congrArg Subtype.val
    ((injective_iff_map_eq_zero _).1 (h n) ⟨_, proj_mem ℳ n m⟩ (Subtype.ext ?_))
  change f (proj ℳ n m) = 0
  rw [← hf.proj_apply, hm, map_zero]

theorem surjective_iff {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) :
    Function.Surjective f ↔ ∀ n, Function.Surjective (hf.piece n) := by
  refine ⟨fun h n y => ?_, fun h y => ?_⟩
  · obtain ⟨m, hm, e⟩ := hf.exists_mem_of_mem_range y.2 (h y)
    exact ⟨⟨m, hm⟩, Subtype.ext e⟩
  · obtain ⟨T, hT⟩ := exists_sum_grProj 𝒩 y
    rw [← hT]
    refine (LinearMap.range f).sum_mem fun n _ => ?_
    obtain ⟨m, hm⟩ := h n ⟨_, proj_mem 𝒩 n y⟩
    exact ⟨m, congrArg Subtype.val hm⟩

theorem exact_piece {f : M →ₗ[MvPolynomial ι R] N} {g : N →ₗ[MvPolynomial ι R] P}
    (hf : IsGradedMap ℳ 𝒩 f) (hg : IsGradedMap 𝒩 𝒬 g) (h : Function.Exact f g) (n : ℤ) :
    Function.Exact (hf.piece n) (hg.piece n) := by
  intro y
  constructor
  · intro hy
    obtain ⟨m, hm, e⟩ := hf.exists_mem_of_mem_range y.2 ((h y).1 (congrArg Subtype.val hy))
    exact ⟨⟨m, hm⟩, Subtype.ext e⟩
  · rintro ⟨m, rfl⟩
    exact Subtype.ext (h.apply_apply_eq_zero m)

theorem exact_of_exact_piece [Decomposition 𝒬] {f : M →ₗ[MvPolynomial ι R] N}
    {g : N →ₗ[MvPolynomial ι R] P} (hf : IsGradedMap ℳ 𝒩 f) (hg : IsGradedMap 𝒩 𝒬 g)
    (h : ∀ n, Function.Exact (hf.piece n) (hg.piece n)) : Function.Exact f g := by
  intro y
  constructor
  · intro hy
    obtain ⟨T, hT⟩ := exists_sum_grProj 𝒩 y
    rw [← hT]
    refine (LinearMap.range f).sum_mem fun n _ => ?_
    obtain ⟨m, hm⟩ := (h n ⟨_, proj_mem 𝒩 n y⟩).1 (Subtype.ext (by
      change g (proj 𝒩 n y) = 0
      rw [← hg.proj_apply, hy, map_zero]))
    exact ⟨m, congrArg Subtype.val hm⟩
  · rintro ⟨m, rfl⟩
    obtain ⟨T, hT⟩ := exists_sum_grProj ℳ m
    rw [← hT, map_sum, map_sum]
    exact Finset.sum_eq_zero fun n _ =>
      congrArg Subtype.val ((h n).apply_apply_eq_zero ⟨_, proj_mem ℳ n m⟩)

theorem symm {e : M ≃ₗ[MvPolynomial ι R] N} (he : IsGradedMap ℳ 𝒩 e.toLinearMap) :
    IsGradedMap 𝒩 ℳ e.symm.toLinearMap := fun n y hy => by
  obtain ⟨m, hm, rfl⟩ := he.exists_mem_of_mem_range hy (e.surjective y)
  simpa using hm

end IsGradedMap

def grShift (ℳ : ℤ → Submodule R M) (d : ℤ) : ℤ → Submodule R M := fun n => ℳ (n + d)

@[simp]
theorem grShift_apply (ℳ : ℤ → Submodule R M) (d n : ℤ) : grShift ℳ d n = ℳ (n + d) := rfl

@[simp]
theorem grShift_zero (ℳ : ℤ → Submodule R M) : grShift ℳ 0 = ℳ := by
  funext n; simp

theorem grShift_grShift (ℳ : ℤ → Submodule R M) (d e : ℤ) :
    grShift (grShift ℳ d) e = grShift ℳ (d + e) := by
  funext n; simp only [grShift_apply]; congr 1; ring

instance grShift.polyGradedSMul (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] (d : ℤ) :
    PolyGradedSMul ι (grShift ℳ d) where
  smul_mem e n p m hp hm := by
    have := grSMul_mem ℳ hp hm
    rwa [grShift_apply, vadd_eq_add, show e + n + d = n + d + e by ring]

instance grShift.decomposition (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (d : ℤ) :
    Decomposition (grShift ℳ d) :=
  IsInternal.chooseDecomposition _ <| isInternal_of_sum_eq_zero _
    (fun T v hv h j hj => by
      have := congrArg (proj ℳ (j + d)) h
      rwa [map_sum, Finset.sum_eq_single j
        (fun i hi e => proj_of_mem_ne ℳ (hv i hi) (by omega)) (fun e => absurd hj e),
        proj_of_mem ℳ (hv j hj), map_zero] at this)
    fun m => by
      induction m using Decomposition.inductionOn ℳ with
      | zero => exact zero_mem _
      | @homogeneous n m => exact Submodule.mem_iSup_of_mem (n - d) (by simp)
      | add a b ha hb => exact add_mem ha hb

theorem proj_grShift (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (d n : ℤ) (m : M) :
    proj (grShift ℳ d) n m = proj ℳ (n + d) m := by
  simpa using (proj_map (grShift ℳ d) ℳ LinearMap.id d (fun n m hm => hm) n m).symm

theorem IsGradedMap.shift {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (d : ℤ) :
    IsGradedMap (grShift ℳ d) (grShift 𝒩 d) f := fun _ _ h => hf h

theorem isGradedMap_lsmul (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {p : MvPolynomial ι R}
    {d : ℤ} (hp : p ∈ polyGrading ι R d) :
    IsGradedMap ℳ (grShift ℳ d) (LinearMap.lsmul (MvPolynomial ι R) M p) :=
  fun _ _ h => grSMul_mem ℳ hp h

theorem isGradedMap_lsmul' (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {p : MvPolynomial ι R}
    {d : ℤ} (hp : p ∈ polyGrading ι R d) :
    IsGradedMap (grShift ℳ (-d)) ℳ (LinearMap.lsmul (MvPolynomial ι R) M p) :=
  fun _ _ h => by simpa using grSMul_mem ℳ hp h

theorem isGradedMap_toSpanSingleton (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {m : M} {d : ℤ}
    (hm : m ∈ ℳ d) : IsGradedMap (grShift (polyGrading ι R) (-d)) ℳ
      (LinearMap.toSpanSingleton (MvPolynomial ι R) M m) :=
  fun _ _ h => by simpa using grSMul_mem ℳ h hm

variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]

theorem proj_smul_of_mem (ℳ : ℤ → Submodule R M) [Decomposition ℳ] [PolyGradedSMul ι ℳ]
    {p : MvPolynomial ι R} {d : ℤ} (hp : p ∈ polyGrading ι R d) (n : ℤ) (m : M) :
    proj ℳ (n + d) (p • m) = p • proj ℳ n m := by
  rw [← proj_grShift]
  exact (isGradedMap_lsmul ℳ hp).proj_apply n m

theorem proj_smul_of_mem_right (ℳ : ℤ → Submodule R M) [Decomposition ℳ] [PolyGradedSMul ι ℳ]
    (p : MvPolynomial ι R) {d : ℤ} {m : M} (hm : m ∈ ℳ d) (n : ℤ) :
    proj ℳ n (p • m) = proj (polyGrading ι R) (n - d) p • m := by
  have := (isGradedMap_toSpanSingleton (ι := ι) ℳ hm).proj_apply n p
  rwa [proj_grShift] at this

def grSub (ℳ : ℤ → Submodule R M) (K : Submodule (MvPolynomial ι R) M) :
    ℤ → Submodule R K := fun n => (ℳ n).comap (K.subtype.restrictScalars R)

@[simp]
theorem mem_grSub {ℳ : ℤ → Submodule R M} {K : Submodule (MvPolynomial ι R) M} {n : ℤ}
    {m : K} : m ∈ grSub ℳ K n ↔ (m : M) ∈ ℳ n := Iff.rfl

def grQuot (ℳ : ℤ → Submodule R M) (K : Submodule (MvPolynomial ι R) M) :
    ℤ → Submodule R (M ⧸ K) := fun n => (ℳ n).map (K.mkQ.restrictScalars R)

theorem mem_grQuot {ℳ : ℤ → Submodule R M} {K : Submodule (MvPolynomial ι R) M} {n : ℤ}
    {y : M ⧸ K} : y ∈ grQuot ℳ K n ↔ ∃ m ∈ ℳ n, Submodule.Quotient.mk m = y := Iff.rfl

instance grSub.polyGradedSMul (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    (K : Submodule (MvPolynomial ι R) M) : PolyGradedSMul ι (grSub ℳ K) where
  smul_mem _ _ _ _ hp hm := SetLike.GradedSMul.smul_mem (B := ℳ) hp hm

instance grQuot.polyGradedSMul (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    (K : Submodule (MvPolynomial ι R) M) : PolyGradedSMul ι (grQuot ℳ K) where
  smul_mem := by
    rintro d n p _ hp ⟨m, hm, rfl⟩
    exact ⟨p • m, SetLike.GradedSMul.smul_mem (B := ℳ) hp hm, rfl⟩

theorem isGradedMap_subtype (ℳ : ℤ → Submodule R M) (K : Submodule (MvPolynomial ι R) M) :
    IsGradedMap (grSub ℳ K) ℳ K.subtype := fun _ _ h => h

theorem isGradedMap_mkQ (ℳ : ℤ → Submodule R M) (K : Submodule (MvPolynomial ι R) M) :
    IsGradedMap ℳ (grQuot ℳ K) K.mkQ := fun _ m h => ⟨m, h, rfl⟩

omit [IsScalarTower R (MvPolynomial ι R) M] in

theorem IsGradedMap.codRestrict {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (K : Submodule (MvPolynomial ι R) N)
    (h : ∀ m, f m ∈ K) : IsGradedMap ℳ (grSub 𝒩 K) (f.codRestrict K h) := fun _ _ h => hf h

omit [IsScalarTower R (MvPolynomial ι R) N] in

theorem IsGradedMap.liftQ {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (K : Submodule (MvPolynomial ι R) M)
    (h : K ≤ LinearMap.ker f) : IsGradedMap (grQuot ℳ K) 𝒩 (K.liftQ f h) := by
  rintro n _ ⟨m, hm, rfl⟩
  exact hf hm

theorem isInternal_grSub (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    {K : Submodule (MvPolynomial ι R) M} (hK : K.IsHomogeneous ℳ) :
    IsInternal (grSub ℳ K) :=
  isInternal_of_sum_eq_zero _
    (fun T v hv h j hj => Subtype.ext <| by
      have e := grProj_sum ℳ T (fun i => (v i : M)) hv hj
      rw [← e, ← Submodule.coe_sum, h]
      simp)
    fun m => by
      obtain ⟨T, hT⟩ := exists_sum_grProj ℳ (m : M)
      have : m = ∑ j ∈ T, (⟨proj ℳ j m, hK j m.2⟩ : K) := Subtype.ext (by simp [hT])
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j (proj_mem ℳ j m)

theorem isInternal_grQuot (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    {K : Submodule (MvPolynomial ι R) M} (hK : K.IsHomogeneous ℳ) :
    IsInternal (grQuot ℳ K) :=
  isInternal_of_sum_eq_zero _
    (fun T v hv h j hj => by
      choose! w hw e using fun i hi => mem_grQuot.1 (hv i hi)
      have h' : ∑ i ∈ T, w i ∈ K := by
        rw [← Submodule.Quotient.mk_eq_zero, ← h, ← Finset.sum_congr rfl e]
        exact map_sum K.mkQ _ _
      have := hK j h'
      rw [← GradedHilbert.proj_apply, grProj_sum ℳ T w hw hj] at this
      rw [← e j hj, Submodule.Quotient.mk_eq_zero]
      exact this)
    fun y => by
      obtain ⟨m, rfl⟩ := K.mkQ_surjective y
      induction m using Decomposition.inductionOn ℳ with
      | zero => rw [map_zero]; exact zero_mem _
      | @homogeneous n m => exact Submodule.mem_iSup_of_mem n ⟨m, m.2, rfl⟩
      | add a b ha hb => rw [map_add]; exact add_mem ha hb

@[instance_reducible]
def grSubDecomposition (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    {K : Submodule (MvPolynomial ι R) M} (hK : K.IsHomogeneous ℳ) :
    Decomposition (grSub ℳ K) :=
  (isInternal_grSub ℳ hK).chooseDecomposition _

@[instance_reducible]
def grQuotDecomposition (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    {K : Submodule (MvPolynomial ι R) M} (hK : K.IsHomogeneous ℳ) :
    Decomposition (grQuot ℳ K) :=
  (isInternal_grQuot ℳ hK).chooseDecomposition _

instance grSub.decomposition (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    [PolyGradedSMul ι ℳ] (K : HomogeneousSubmodule (polyGrading ι R) ℳ) :
    Decomposition (grSub ℳ K.toSubmodule) := grSubDecomposition ℳ K.isHomogeneous

instance grQuot.decomposition (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    [PolyGradedSMul ι ℳ] (K : HomogeneousSubmodule (polyGrading ι R) ℳ) :
    Decomposition (grQuot ℳ K.toSubmodule) := grQuotDecomposition ℳ K.isHomogeneous

theorem isHomogeneous_span_gr (ℳ : ℤ → Submodule R M) [Decomposition ℳ] [PolyGradedSMul ι ℳ]
    {G : Set M} (hG : ∀ g ∈ G, ∃ d, g ∈ ℳ d) :
    (Submodule.span (MvPolynomial ι R) G).IsHomogeneous ℳ := by
  intro n m hm
  change proj ℳ n m ∈ _
  obtain ⟨c, hc, rfl⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).1 hm
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun g _ => ?_
  obtain ⟨d, hd⟩ := hG g g.2
  rw [proj_smul_of_mem_right ℳ _ hd]
  exact Submodule.smul_mem _ _ (Submodule.subset_span g.2)

end Module

section Pi

variable {ι : Type*} {R : Type*} [CommRing R] {κ : Type*}
  {M : κ → Type*} [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
  [∀ k, Module (MvPolynomial ι R) (M k)]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]

def grPi (ℳ : ∀ k, ℤ → Submodule R (M k)) : ℤ → Submodule R (∀ k, M k) :=
  fun n => Submodule.pi Set.univ fun k => ℳ k n

@[simp]
theorem mem_grPi {ℳ : ∀ k, ℤ → Submodule R (M k)} {n : ℤ} {m : ∀ k, M k} :
    m ∈ grPi ℳ n ↔ ∀ k, m k ∈ ℳ k n := by
  simp [grPi, Submodule.mem_pi]

instance grPi.polyGradedSMul (ℳ : ∀ k, ℤ → Submodule R (M k))
    [∀ k, PolyGradedSMul ι (ℳ k)] : PolyGradedSMul ι (grPi ℳ) where
  smul_mem _ _ _ _ hp hm := mem_grPi.2 fun k =>
    SetLike.GradedSMul.smul_mem (B := ℳ k) hp (mem_grPi.1 hm k)

instance grPi.decomposition [Finite κ] (ℳ : ∀ k, ℤ → Submodule R (M k))
    [∀ k, Decomposition (ℳ k)] : Decomposition (grPi ℳ) :=
  IsInternal.chooseDecomposition _ <| isInternal_of_sum_eq_zero _
    (fun T v hv h j hj => funext fun k => by
      have e := grProj_sum (ℳ k) T (fun i => v i k) (fun i hi => mem_grPi.1 (hv i hi) k) hj
      rw [← e, ← Finset.sum_apply, h]
      simp)
    fun m => by
      classical
      have := Fintype.ofFinite κ
      rw [← Finset.univ_sum_single m]
      refine Submodule.sum_mem _ fun k _ => ?_
      induction m k using Decomposition.inductionOn (ℳ k) with
      | zero => rw [Pi.single_zero]; exact zero_mem _
      | @homogeneous n x =>
        refine Submodule.mem_iSup_of_mem n (mem_grPi.2 fun j => ?_)
        by_cases h : j = k
        · subst h; simp
        · rw [Pi.single_eq_of_ne h]; exact zero_mem _
      | add a b ha hb => rw [Pi.single_add]; exact add_mem ha hb

variable (ι) in

theorem isGradedMap_piProj (ℳ : ∀ k, ℤ → Submodule R (M k)) (k : κ) :
    IsGradedMap (grPi ℳ) (ℳ k) (LinearMap.proj (R := MvPolynomial ι R) k) :=
  fun _ _ h => mem_grPi.1 h k

variable (ι) in

theorem isGradedMap_piSingle [DecidableEq κ] (ℳ : ∀ k, ℤ → Submodule R (M k)) (k : κ) :
    IsGradedMap (ℳ k) (grPi ℳ) (LinearMap.single (MvPolynomial ι R) M k) :=
  fun _ m hm => mem_grPi.2 fun j => by
    by_cases h : j = k
    · subst h; simpa using hm
    · rw [LinearMap.coe_single, Pi.single_eq_of_ne h]; exact zero_mem _

theorem IsGradedMap.pi {𝒩 : ℤ → Submodule R N} {ℳ : ∀ k, ℤ → Submodule R (M k)}
    {f : ∀ k, N →ₗ[MvPolynomial ι R] M k} (hf : ∀ k, IsGradedMap 𝒩 (ℳ k) (f k)) :
    IsGradedMap 𝒩 (grPi ℳ) (LinearMap.pi f) := fun _ _ h => mem_grPi.2 fun k => hf k h

variable (ι R) in

abbrev grFree (d : κ → ℤ) : ℤ → Submodule R (κ → MvPolynomial ι R) :=
  grPi fun k => grShift (polyGrading ι R) (-d k)

theorem isGradedMap_linearCombination [Fintype κ] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩]
    {g : κ → N} {d : κ → ℤ} (hg : ∀ k, g k ∈ 𝒩 (d k)) :
    IsGradedMap (grFree ι R d) 𝒩 (Fintype.linearCombination (MvPolynomial ι R) g) :=
  fun _ _ h => by
    rw [Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun k _ =>
      isGradedMap_toSpanSingleton 𝒩 (hg k) (mem_grPi.1 h k)

theorem exists_graded_surjection (𝒩 : ℤ → Submodule R N) [Decomposition 𝒩] [PolyGradedSMul ι 𝒩]
    [Module.Finite (MvPolynomial ι R) N] :
    ∃ (r : ℕ) (d : Fin r → ℤ) (f : (Fin r → MvPolynomial ι R) →ₗ[MvPolynomial ι R] N),
      IsGradedMap (grFree ι R d) 𝒩 f ∧ Function.Surjective f := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := MvPolynomial ι R) (M := N)
  choose T hT using exists_sum_grProj 𝒩
  let U : Finset (N × ℤ) := G ×ˢ G.biUnion T
  let e := U.equivFin.symm
  refine ⟨U.card, fun k => (e k).1.2, Fintype.linearCombination _
    fun k => proj 𝒩 (e k).1.2 (e k).1.1,
    isGradedMap_linearCombination 𝒩 fun k => proj_mem _ _ _, ?_⟩
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← hG,
    Submodule.span_le]
  intro g hg
  rw [← hT g]
  refine Submodule.sum_mem _ fun j hj => Submodule.subset_span
    ⟨e.symm ⟨(g, j), Finset.mem_product.2 ⟨hg, Finset.mem_biUnion.2 ⟨g, hg, hj⟩⟩⟩, by simp⟩

end Pi

section Family

variable {ι : Type*} {R : Type*} [CommRing R]
  {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
  {B : ℤ → Type*} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]

def OperatorsCommute (x : ι → ∀ n, A n →ₗ[R] A (n + 1)) : Prop :=
  ∀ (i j : ι) (n : ℤ) (a : A n), x i (n + 1) (x j n a) = x j (n + 1) (x i n a)

@[nolint unusedArguments]
def GrSum {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (_ : OperatorsCommute x) : Type _ := ⨁ n, A n

namespace GrSum

variable {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
  {y : ι → ∀ n, B n →ₗ[R] B (n + 1)} (hy : OperatorsCommute y)

instance : AddCommGroup (GrSum hx) := inferInstanceAs (AddCommGroup (⨁ n, A n))

instance : Module R (GrSum hx) := inferInstanceAs (Module R (⨁ n, A n))

def equivDirectSum : GrSum hx ≃ₗ[R] ⨁ n, A n := LinearEquiv.refl R _

def of (n : ℤ) : A n →ₗ[R] GrSum hx := DirectSum.lof R ℤ A n

def component (n : ℤ) : GrSum hx →ₗ[R] A n := DirectSum.component R ℤ A n

@[simp]
theorem component_of (n : ℤ) (a : A n) : component hx n (of hx n a) = a :=
  DirectSum.component.lof_self R n a

theorem component_of_ne {n k : ℤ} (h : k ≠ n) (a : A k) : component hx n (of hx k a) = 0 :=
  (DirectSum.component.of R n k a).trans (dif_neg h)

theorem of_injective (n : ℤ) : Function.Injective (of hx n) :=
  Function.LeftInverse.injective (component_of hx n)

theorem lhom_ext {N : Type*} [AddCommGroup N] [Module R N] {f g : GrSum hx →ₗ[R] N}
    (h : ∀ n a, f (of hx n a) = g (of hx n a)) : f = g :=
  DirectSum.linearMap_ext R fun n => LinearMap.ext (h n)

def desc {N : Type*} [AddCommGroup N] [Module R N] (φ : ∀ n, A n →ₗ[R] N) : GrSum hx →ₗ[R] N :=
  DirectSum.toModule R ℤ N φ

@[simp]
theorem desc_of {N : Type*} [AddCommGroup N] [Module R N] (φ : ∀ n, A n →ₗ[R] N) (n : ℤ)
    (a : A n) : desc hx φ (of hx n a) = φ n a :=
  DirectSum.toModule_lof R n a

def op (i : ι) : Module.End R (GrSum hx) := desc hx fun n => of hx (n + 1) ∘ₗ x i n

@[simp]
theorem op_of (i : ι) (n : ℤ) (a : A n) : op hx i (of hx n a) = of hx (n + 1) (x i n a) :=
  desc_of hx _ n a

theorem commute_op (i j : ι) : Commute (op hx i) (op hx j) :=
  lhom_ext hx fun n a => by simp [hx i j n a]

instance : Module (MvPolynomial ι R) (GrSum hx) :=
  Module.compHom (GrSum hx) (Wick.commEval R (op hx) (commute_op hx)).toRingHom

theorem smul_def (p : MvPolynomial ι R) (m : GrSum hx) :
    p • m = Wick.commEval R (op hx) (commute_op hx) p m := rfl

instance : IsScalarTower R (MvPolynomial ι R) (GrSum hx) where
  smul_assoc r p m := by rw [smul_def, smul_def, map_smul]; rfl

theorem X_smul (i : ι) (m : GrSum hx) : (X i : MvPolynomial ι R) • m = op hx i m := by
  rw [smul_def, Wick.commEval_X]

@[simp]
theorem X_smul_of (i : ι) (n : ℤ) (a : A n) :
    (X i : MvPolynomial ι R) • of hx n a = of hx (n + 1) (x i n a) := by
  rw [X_smul, op_of]

def grading : ℤ → Submodule R (GrSum hx) := fun n => LinearMap.range (of hx n)

theorem mem_grading {n : ℤ} {m : GrSum hx} : m ∈ grading hx n ↔ ∃ a, of hx n a = m := Iff.rfl

theorem of_mem_grading (n : ℤ) (a : A n) : of hx n a ∈ grading hx n := ⟨a, rfl⟩

def pieceEquiv (n : ℤ) : A n ≃ₗ[R] grading hx n := LinearEquiv.ofInjective _ (of_injective hx n)

@[simp]
theorem coe_pieceEquiv (n : ℤ) (a : A n) : (pieceEquiv hx n a : GrSum hx) = of hx n a := rfl

instance : PolyGradedSMul ι (grading hx) :=
  polyGradedSMul_of_X_smul_mem _ (by
    rintro i n _ ⟨a, rfl⟩
    exact ⟨_, (X_smul_of hx i n a).symm⟩)

instance : Decomposition (grading hx) :=
  IsInternal.chooseDecomposition _ <| isInternal_of_sum_eq_zero _
    (fun T v hv h j hj => by
      choose! a ha using fun i hi => (mem_grading hx).1 (hv i hi)
      have := congrArg (component hx j) h
      rw [← Finset.sum_congr rfl ha, map_sum, Finset.sum_eq_single j
        (fun i _ e => component_of_ne hx e _) (fun e => absurd hj e), component_of,
        map_zero] at this
      rw [← ha j hj, this, map_zero])
    fun m => by
      induction m using DirectSum.induction_on with
      | zero => exact zero_mem _
      | of n a => exact Submodule.mem_iSup_of_mem n ⟨a, rfl⟩
      | add a b ha hb => exact add_mem ha hb

theorem proj_grading (n : ℤ) (m : GrSum hx) :
    proj (grading hx) n m = of hx n (component hx n m) := by
  have : proj (grading hx) n = of hx n ∘ₗ component hx n := lhom_ext hx fun k a => by
    by_cases h : k = n
    · subst h
      simp [proj_of_mem _ (of_mem_grading hx k a)]
    · simp [proj_of_mem_ne _ (of_mem_grading hx k a) h, component_of_ne hx h]
  exact congr($this m)

variable {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]

def lift (φ : ∀ n, A n →ₗ[R] N)
    (hφ : ∀ i n a, φ (n + 1) (x i n a) = (X i : MvPolynomial ι R) • φ n a) :
    GrSum hx →ₗ[MvPolynomial ι R] N where
  toFun := desc hx φ
  map_add' := map_add _
  map_smul' p m := by
    have hX (i : ι) : desc hx φ ∘ₗ mul (GrSum hx) (X i : MvPolynomial ι R) =
        mul N (X i : MvPolynomial ι R) ∘ₗ desc hx φ := lhom_ext hx fun n a => by simp [hφ]
    rw [RingHom.id_apply]
    induction p using MvPolynomial.induction_on generalizing m with
    | C a => rw [← MvPolynomial.algebraMap_eq, algebraMap_smul, algebraMap_smul, map_smul]
    | add p q hp hq => rw [add_smul, add_smul, map_add, hp, hq]
    | mul_X p i hp =>
      rw [mul_smul, mul_smul, hp]
      exact congrArg _ congr($(hX i) m)

@[simp]
theorem lift_of (φ : ∀ n, A n →ₗ[R] N) (hφ) (n : ℤ) (a : A n) :
    lift hx φ hφ (of hx n a) = φ n a := desc_of hx φ n a

theorem isGradedMap_lift (φ : ∀ n, A n →ₗ[R] N) (hφ) (𝒩 : ℤ → Submodule R N)
    (h : ∀ n a, φ n a ∈ 𝒩 n) : IsGradedMap (grading hx) 𝒩 (lift hx φ hφ) := by
  rintro n _ ⟨a, rfl⟩
  rw [lift_of]
  exact h n a

def map (φ : ∀ n, A n →ₗ[R] B n) (hφ : ∀ i n a, φ (n + 1) (x i n a) = y i n (φ n a)) :
    GrSum hx →ₗ[MvPolynomial ι R] GrSum hy :=
  lift hx (fun n => of hy n ∘ₗ φ n) fun i n a => by simp [hφ]

@[simp]
theorem map_of (φ : ∀ n, A n →ₗ[R] B n) (hφ) (n : ℤ) (a : A n) :
    map hx hy φ hφ (of hx n a) = of hy n (φ n a) := lift_of hx _ _ n a

theorem isGradedMap_map (φ : ∀ n, A n →ₗ[R] B n) (hφ) :
    IsGradedMap (grading hx) (grading hy) (map hx hy φ hφ) :=
  isGradedMap_lift hx _ _ _ fun n _ => of_mem_grading hy n _

end GrSum

end Family

end GlobalTheory
