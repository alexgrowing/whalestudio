import Mathlib
import GroundTheory.AutomorphicForms.L2LocalComponents.ArchPolar
import GroundTheory.AutomorphicForms.L2LocalComponents.ArchHaar
import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Matrix MeasureTheory Topology Filter
open scoped NumberField.AdeleRing ContDiff Manifold

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

section Unitary

variable {n : ℕ}

theorem dotProduct_mulVec_single_add {R : Type*} [CommRing R] [StarRing R] (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) (x y : R) :
    (Pi.single i x + Pi.single j y) ⬝ᵥ (A *ᵥ star (Pi.single i x + Pi.single j y)) =
      x * A i i * star x + x * A i j * star y + y * A j i * star x + y * A j j * star y := by
  classical
  simp only [star_add, Pi.star_single, mulVec_add, dotProduct_add, add_dotProduct, single_dotProduct]
  simp only [mulVec, dotProduct_single]
  ring

theorem eq_zero_of_forall_dotProduct_real {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᴴ = A)
    (h : ∀ z : Fin n → ℝ, z ⬝ᵥ (A *ᵥ star z) = 0) : A = 0 := by
  have hdiag : ∀ i, A i i = 0 := fun i => by
    have := h (Pi.single i 1 + Pi.single i 0)
    rw [dotProduct_mulVec_single_add] at this
    simpa using this
  have hsymm : ∀ i j, A j i = A i j := fun i j => by
    have := congrFun (congrFun hA i) j
    simpa [conjTranspose_apply] using this
  ext i j
  have h1 := h (Pi.single i 1 + Pi.single j 1)
  rw [dotProduct_mulVec_single_add, hdiag, hdiag, hsymm i j] at h1
  simp only [star_one, mul_one, one_mul, mul_zero, zero_add, add_zero] at h1
  show A i j = 0
  linarith

theorem eq_zero_of_forall_dotProduct_complex {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A)
    (h : ∀ z : Fin n → ℂ, z ⬝ᵥ (A *ᵥ star z) = 0) : A = 0 := by
  have hdiag : ∀ i, A i i = 0 := fun i => by
    have := h (Pi.single i 1 + Pi.single i 0)
    rw [dotProduct_mulVec_single_add] at this
    simpa using this
  have hherm : ∀ i j, A j i = starRingEnd ℂ (A i j) := fun i j => by
    have := congrFun (congrFun hA j) i
    simpa [conjTranspose_apply, Complex.star_def] using this.symm
  have key : ∀ i j, ∀ c : ℂ, A i j * starRingEnd ℂ c + c * A j i = 0 := by
    intro i j c
    have h1 := h (Pi.single i 1 + Pi.single j c)
    rw [dotProduct_mulVec_single_add, hdiag, hdiag] at h1
    simp only [star_one, mul_one, mul_zero, one_mul, zero_add, Complex.star_def] at h1
    linear_combination h1
  ext i j
  have h1 := key i j 1
  have h2 := key i j Complex.I
  rw [hherm i j, map_one, mul_one, one_mul] at h1
  rw [hherm i j, Complex.conj_I] at h2
  have h3 : starRingEnd ℂ (A i j) = A i j := by
    have : Complex.I * (starRingEnd ℂ (A i j) - A i j) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h Complex.I_ne_zero
    · exact sub_eq_zero.1 h
  rw [h3] at h1
  show A i j = 0
  linear_combination h1 / 2

theorem sum_norm_sq_eq_dotProduct {𝕜 : Type*} [RCLike 𝕜] (y : Fin n → 𝕜) :
    ((∑ i, ‖y i‖ ^ 2 : ℝ) : 𝕜) = y ⬝ᵥ star y := by
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.mul_conj]
  push_cast
  rfl

theorem mem_unitaryGroup_of_euclidNorm_real {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : ∀ z : Fin n → ℝ, Reduction.euclidNorm (z ᵥ* U) = Reduction.euclidNorm z) :
    U ∈ unitaryGroup (Fin n) ℝ := by
  rw [mem_unitaryGroup_iff]
  have hsq : ∀ z : Fin n → ℝ, ∑ j, ‖(z ᵥ* U) j‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := fun z => by
    have := congrArg (· ^ 2) (hU z)
    simp only [Reduction.euclidNorm] at this
    rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at this
  have h0 := eq_zero_of_forall_dotProduct_real (A := U * star U - 1)
    (by rw [conjTranspose_sub, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
      conjTranspose_one]) (fun z => by
      have e1 := sum_norm_sq_eq_dotProduct (𝕜 := ℝ) (z ᵥ* U)
      have e2 := sum_norm_sq_eq_dotProduct (𝕜 := ℝ) z
      rw [hsq z, e2, star_vecMul, dotProduct_mulVec, vecMul_vecMul] at e1
      rw [sub_mulVec, dotProduct_sub, one_mulVec, dotProduct_mulVec, star_eq_conjTranspose, ← e1]
      simp)
  exact sub_eq_zero.1 h0

theorem mem_unitaryGroup_of_euclidNorm_complex {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : ∀ z : Fin n → ℂ, Reduction.euclidNorm (z ᵥ* U) = Reduction.euclidNorm z) :
    U ∈ unitaryGroup (Fin n) ℂ := by
  rw [mem_unitaryGroup_iff]
  have hsq : ∀ z : Fin n → ℂ, ∑ j, ‖(z ᵥ* U) j‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := fun z => by
    have := congrArg (· ^ 2) (hU z)
    simp only [Reduction.euclidNorm] at this
    rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at this
  have h0 := eq_zero_of_forall_dotProduct_complex (A := U * star U - 1)
    (by rw [conjTranspose_sub, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
      conjTranspose_one]) (fun z => by
      have e1 := sum_norm_sq_eq_dotProduct (𝕜 := ℂ) (z ᵥ* U)
      have e2 := sum_norm_sq_eq_dotProduct (𝕜 := ℂ) z
      rw [hsq z, e2, star_vecMul, dotProduct_mulVec, vecMul_vecMul] at e1
      rw [sub_mulVec, dotProduct_sub, one_mulVec, dotProduct_mulVec, star_eq_conjTranspose, ← e1]
      simp)
  exact sub_eq_zero.1 h0

end Unitary

section Frob

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

def frobSq (M : Matrix (Fin n) (Fin n) 𝕜) : ℝ := ∑ i, ∑ j, ‖M i j‖ ^ 2

theorem frobSq_eq_trace (M : Matrix (Fin n) (Fin n) 𝕜) : (frobSq M : 𝕜) = Matrix.trace (Mᴴ * M) := by
  simp only [frobSq, Matrix.trace, diag, mul_apply, conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, RCLike.mul_conj]

theorem frobSq_conj {U : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ unitaryGroup (Fin n) 𝕜)
    (M : Matrix (Fin n) (Fin n) 𝕜) : frobSq (U * M * star U) = frobSq M := by
  apply RCLike.ofReal_injective (K := 𝕜)
  rw [frobSq_eq_trace, frobSq_eq_trace]
  have h1 : star U * U = 1 := mem_unitaryGroup_iff'.1 hU
  rw [star_eq_conjTranspose] at h1 ⊢
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  calc Matrix.trace (U * (Mᴴ * Uᴴ) * (U * M * Uᴴ)) =
        Matrix.trace (U * (Mᴴ * (Uᴴ * U) * M) * Uᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Mᴴ * M * (Uᴴ * U)) := by
        rw [h1, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul,
          Matrix.mul_one]
    _ = Matrix.trace (Mᴴ * M) := by rw [h1, Matrix.mul_one]

end Frob

namespace AutomorphicForm

open scoped Classical

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction in

theorem realCompM_mem_unitaryGroup {k : archGroup K n} (hk : k ∈ archCompact K n)
    (v : {w : InfinitePlace K // IsReal w}) :
    realCompM v ((k : (ArchMatrix K n)ˣ) : ArchMatrix K n) ∈ unitaryGroup (Fin n) ℝ := by
  apply mem_unitaryGroup_of_euclidNorm_real
  intro z
  obtain ⟨w, hw⟩ := v
  have hk' : infEmb K n k ∈ Reduction.maxCompact := hk
  set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hψ : ∀ x, ‖ψ x‖ = ‖x‖ := fun x =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) x
  set y : Fin n → w.Completion := fun i => ψ.symm (z i)
  have hy : (fun i => ψ (y i)) = z := funext fun i => ψ.apply_symm_apply (z i)
  have e : (fun i => ψ ((y ᵥ* (infAt w (infEmb K n k) : Matrix (Fin n) (Fin n) w.Completion)) i)) =
      z ᵥ* realCompM ⟨w, hw⟩ ((k : (ArchMatrix K n)ˣ) : ArchMatrix K n) := by
    rw [← hy]
    ext j
    simp only [vecMul, dotProduct, map_sum, map_mul, realCompM_apply, Matrix.map_apply, realComp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [infAt_infEmb_apply]
    congr 1
    exact extensionEmbeddingOfIsReal_symm _ hw
  rw [← e]
  calc euclidNorm (fun i => ψ ((y ᵥ* (infAt w (infEmb K n k) : Matrix (Fin n) (Fin n) w.Completion)) i))
      = euclidNorm (y ᵥ* (infAt w (infEmb K n k) : Matrix (Fin n) (Fin n) w.Completion)) :=
        euclidNorm_map ψ.toRingHom hψ _
    _ = euclidNorm y := hk'.1 w y
    _ = euclidNorm z := by rw [← hy]; exact (euclidNorm_map ψ.toRingHom hψ y).symm

open Reduction in

theorem complexCompM_mem_unitaryGroup {k : archGroup K n} (hk : k ∈ archCompact K n)
    (v : {w : InfinitePlace K // IsComplex w}) :
    complexCompM v ((k : (ArchMatrix K n)ˣ) : ArchMatrix K n) ∈ unitaryGroup (Fin n) ℂ := by
  apply mem_unitaryGroup_of_euclidNorm_complex
  intro z
  obtain ⟨w, hw⟩ := v
  have hk' : infEmb K n k ∈ Reduction.maxCompact := hk
  set ψ := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  have hψ : ∀ x, ‖ψ x‖ = ‖x‖ := fun x =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
  set y : Fin n → w.Completion := fun i => ψ.symm (z i)
  have hy : (fun i => ψ (y i)) = z := funext fun i => ψ.apply_symm_apply (z i)
  have e : (fun i => ψ ((y ᵥ* (infAt w (infEmb K n k) : Matrix (Fin n) (Fin n) w.Completion)) i)) =
      z ᵥ* complexCompM ⟨w, hw⟩ ((k : (ArchMatrix K n)ˣ) : ArchMatrix K n) := by
    rw [← hy]
    ext j
    simp only [vecMul, dotProduct, map_sum, map_mul, complexCompM_apply, Matrix.map_apply,
      complexComp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [infAt_infEmb_apply]
    congr 1
    exact extensionEmbedding_symm _ hw
  rw [← e]
  calc euclidNorm (fun i => ψ ((y ᵥ* (infAt w (infEmb K n k) : Matrix (Fin n) (Fin n) w.Completion)) i))
      = euclidNorm (y ᵥ* (infAt w (infEmb K n k) : Matrix (Fin n) (Fin n) w.Completion)) :=
        euclidNorm_map ψ.toRingHom hψ _
    _ = euclidNorm y := hk'.1 w y
    _ = euclidNorm z := by rw [← hy]; exact (euclidNorm_map ψ.toRingHom hψ y).symm

theorem realCompM_inv {k : archGroup K n} (hk : k ∈ archCompact K n)
    (v : {w : InfinitePlace K // IsReal w}) :
    realCompM v (((k⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) =
      star (realCompM v ((k : (ArchMatrix K n)ˣ) : ArchMatrix K n)) := by
  set U := realCompM v ((k : (ArchMatrix K n)ˣ) : ArchMatrix K n)
  set U' := realCompM v (((k⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n)
  have h1 : U * U' = 1 := by
    rw [← map_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one,
      map_one]
  have h2 : star U * U = 1 := mem_unitaryGroup_iff'.1 (realCompM_mem_unitaryGroup hk v)
  calc U' = star U * U * U' := by rw [h2, Matrix.one_mul]
    _ = star U := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem complexCompM_inv {k : archGroup K n} (hk : k ∈ archCompact K n)
    (v : {w : InfinitePlace K // IsComplex w}) :
    complexCompM v (((k⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) =
      star (complexCompM v ((k : (ArchMatrix K n)ˣ) : ArchMatrix K n)) := by
  set U := complexCompM v ((k : (ArchMatrix K n)ˣ) : ArchMatrix K n)
  set U' := complexCompM v (((k⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n)
  have h1 : U * U' = 1 := by
    rw [← map_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one,
      map_one]
  have h2 : star U * U = 1 := mem_unitaryGroup_iff'.1 (complexCompM_mem_unitaryGroup hk v)
  calc U' = star U * U * U' := by rw [h2, Matrix.one_mul]
    _ = star U := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

def archQuad (X : ArchMatrix K n) : ℝ :=
  ∑ v : {w : InfinitePlace K // IsReal w}, frobSq (realCompM v X) +
    ∑ v : {w : InfinitePlace K // IsComplex w}, frobSq (complexCompM v X)

theorem archQuad_nonneg (X : ArchMatrix K n) : 0 ≤ archQuad X :=
  add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    sq_nonneg _) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    sq_nonneg _)

@[simp] theorem archQuad_zero : archQuad (0 : ArchMatrix K n) = 0 := by
  simp [archQuad, frobSq]

theorem archQuad_conj {k : archGroup K n} (hk : k ∈ archCompact K n) (X : ArchMatrix K n) :
    archQuad (((k : (ArchMatrix K n)ˣ) : ArchMatrix K n) * X *
      (((k⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n)) = archQuad X := by
  simp only [archQuad, map_mul, realCompM_inv hk, complexCompM_inv hk,
    frobSq_conj (realCompM_mem_unitaryGroup hk _), frobSq_conj (complexCompM_mem_unitaryGroup hk _)]

theorem archQuad_eq_zero {X : ArchMatrix K n} (h : archQuad X = 0) : X = 0 := by
  have h1 := (add_eq_zero_iff_of_nonneg (Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 h
  have hr : ∀ v i j, (mat X i j).1 v = 0 := by
    intro v i j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 h1.1 v (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ =>
      sq_nonneg _)).1 h2 i (Finset.mem_univ _)
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h3 j (Finset.mem_univ _)
    have : ‖(realCompM v X) i j‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h4
    simpa using this
  have hc : ∀ v i j, (mat X i j).2 v = 0 := by
    intro v i j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 h1.2 v (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ =>
      sq_nonneg _)).1 h2 i (Finset.mem_univ _)
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h3 j (Finset.mem_univ _)
    have : ‖(complexCompM v X) i j‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h4
    simpa using this
  have he : ∀ i j, mat X i j = 0 := fun i j =>
    Prod.ext (funext fun v => by simpa using hr v i j) (funext fun v => by simpa using hc v i j)
  exact mat_injective (Matrix.ext fun i j => by rw [he]; rfl)

def entryReal (i j : Fin n) (v : {w : InfinitePlace K // IsReal w}) : ArchMatrix K n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (mat X i j).1 v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def entryComplex (i j : Fin n) (v : {w : InfinitePlace K // IsComplex w}) :
    ArchMatrix K n →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (mat X i j).2 v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem archQuad_eq (X : ArchMatrix K n) :
    archQuad X = ∑ v : {w : InfinitePlace K // IsReal w}, ∑ i, ∑ j, ‖entryReal i j v X‖ ^ 2 +
      ∑ v : {w : InfinitePlace K // IsComplex w}, ∑ i, ∑ j, ‖entryComplex i j v X‖ ^ 2 := rfl

theorem contDiff_archQuad : ContDiff ℝ ⊤ (archQuad : ArchMatrix K n → ℝ) := by
  have e : (archQuad : ArchMatrix K n → ℝ) = fun X =>
      ∑ v : {w : InfinitePlace K // IsReal w}, ∑ i, ∑ j, ‖entryReal i j v X‖ ^ 2 +
      ∑ v : {w : InfinitePlace K // IsComplex w}, ∑ i, ∑ j, ‖entryComplex i j v X‖ ^ 2 :=
    funext archQuad_eq
  rw [e]
  refine ContDiff.add ?_ ?_
  · exact ContDiff.sum fun v _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      (contDiff_norm_sq ℝ).comp (entryReal i j v).contDiff
  · exact ContDiff.sum fun v _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      (contDiff_norm_sq ℝ).comp (entryComplex i j v).contDiff

theorem archQuad_smul (t : ℝ) (X : ArchMatrix K n) : archQuad (t • X) = t ^ 2 * archQuad X := by
  rw [archQuad_eq, archQuad_eq, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, _root_.norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, _root_.norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem exists_archQuad_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℝ, 0 < m ∧ ∀ X : ArchMatrix K n, archQuad X < m → ‖X‖ < δ := by
  by_cases hX : ∃ X : ArchMatrix K n, X ≠ 0
  · have hS : IsCompact (Metric.sphere (0 : ArchMatrix K n) δ) := isCompact_sphere 0 δ
    obtain ⟨X₀, hX₀⟩ := hX
    have hne : (Metric.sphere (0 : ArchMatrix K n) δ).Nonempty :=
      ⟨(δ / ‖X₀‖) • X₀, by
        rw [mem_sphere_zero_iff_norm, _root_.norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hδ, abs_norm,
          div_mul_cancel₀ _ (norm_ne_zero_iff.2 hX₀)]⟩
    obtain ⟨Y, hY, hmin⟩ := hS.exists_isMinOn (f := archQuad) hne
      (contDiff_archQuad (K := K) (n := n)).continuous.continuousOn
    have hY0 : Y ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hY
      exact hδ.ne hY
    refine ⟨archQuad Y, lt_of_le_of_ne (archQuad_nonneg Y) (fun h => hY0 (archQuad_eq_zero h.symm)),
      fun X hXq => ?_⟩
    by_contra hXn
    push Not at hXn
    have hX0 : X ≠ 0 := by
      intro h; rw [h, norm_zero] at hXn; exact absurd hδ (not_lt.2 hXn)
    set t : ℝ := δ / ‖X‖
    have ht : 0 < t := div_pos hδ (norm_pos_iff.2 hX0)
    have ht1 : t ≤ 1 := (div_le_one (norm_pos_iff.2 hX0)).2 hXn
    have hmem : t • X ∈ Metric.sphere (0 : ArchMatrix K n) δ := by
      rw [mem_sphere_zero_iff_norm, _root_.norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        div_mul_cancel₀ _ (norm_ne_zero_iff.2 hX0)]
    have h1 : archQuad Y ≤ archQuad (t • X) := hmin hmem
    rw [archQuad_smul] at h1
    have h2 : t ^ 2 * archQuad X ≤ archQuad X := by
      have := archQuad_nonneg X
      have : t ^ 2 ≤ 1 := by nlinarith
      nlinarith
    linarith
  · push Not at hX
    exact ⟨1, one_pos, fun X _ => by rw [hX X, norm_zero]; exact hδ⟩

abbrev archVal (a : archGroup K n) : ArchMatrix K n := ((a : (ArchMatrix K n)ˣ) : ArchMatrix K n)

theorem continuous_archVal : Continuous (archVal : archGroup K n → ArchMatrix K n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_archVal_inv : Continuous (fun a : archGroup K n => archVal a⁻¹) :=
  continuous_archVal.comp continuous_inv

theorem isClosedEmbedding_archPair :
    Topology.IsClosedEmbedding (fun a : archGroup K n =>
      Units.embedProduct (ArchMatrix K n) (a : (ArchMatrix K n)ˣ)) := by
  have hcl : IsClosed ((archGroup K n : Subgroup (ArchMatrix K n)ˣ) : Set (ArchMatrix K n)ˣ) := by
    rw [show ((archGroup K n : Subgroup (ArchMatrix K n)ˣ) : Set (ArchMatrix K n)ˣ) = Set.univ from
      Subgroup.coe_top]
    exact isClosed_univ
  exact Units.isClosedEmbedding_embedProduct.comp hcl.isClosedEmbedding_subtypeVal

theorem archQuad_conj_sub {k : archGroup K n} (hk : k ∈ archCompact K n) (a : archGroup K n) :
    archQuad (archVal (k * a * k⁻¹) - 1) = archQuad (archVal a - 1) := by
  rw [← archQuad_conj hk (archVal a - 1)]
  congr 1
  have h1 : archVal k * archVal k⁻¹ = 1 := by
    rw [archVal, archVal, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Units.val_one]
  simp only [archVal, Subgroup.coe_mul, Units.val_mul] at h1 ⊢
  rw [mul_sub, sub_mul, mul_one, h1]

theorem exists_archBump (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {N : Set (archGroup K n)}
    (hN : N ∈ 𝓝 (1 : archGroup K n)) :
    ∃ ρ : archGroup K n → ℝ, (∀ a, 0 ≤ ρ a) ∧
      (isExpLieAlgebra K n).IsTestFunction (fun a => (ρ a : ℂ)) ∧ ∫ a, ρ a ∂ν = 1 ∧
      (∀ a, ρ a⁻¹ = ρ a) ∧ (∀ k ∈ archCompact K n, ∀ a, ρ (k * a * k⁻¹) = ρ a) ∧
      (∀ a, ρ a ≠ 0 → a ∈ N) ∧ (∀ a, ρ a ≠ 0 → ∃ X : archLie K n, a = (isExpLieAlgebra K n).expG X) := by
  set E := fun a : archGroup K n => Units.embedProduct (ArchMatrix K n) (a : (ArchMatrix K n)ˣ) with hEdef
  have hE := isClosedEmbedding_archPair (K := K) (n := n)

  obtain ⟨W, hW, hWN⟩ : ∃ W ∈ 𝓝 (E 1), E ⁻¹' W ⊆ N := by
    have := hE.isInducing.nhds_eq_comap (1 : archGroup K n)
    rw [this] at hN
    exact (Filter.mem_comap).1 hN
  obtain ⟨δ₁, hδ₁, hδ₁W⟩ := Metric.mem_nhds_iff.1 hW

  set T := (expPartialHomeomorph ℝ (ArchMatrix K n)).target
  have hT1 : (1 : ArchMatrix K n) ∈ T := by
    have := (expPartialHomeomorph ℝ (ArchMatrix K n)).map_source
      (zero_mem_expPartialHomeomorph_source ℝ (ArchMatrix K n))
    rwa [coe_expPartialHomeomorph, NormedSpace.exp_zero] at this
  obtain ⟨δ₀, hδ₀, hδ₀T⟩ := Metric.isOpen_iff.1 (expPartialHomeomorph ℝ (ArchMatrix K n)).open_target 1 hT1
  set δ := min δ₁ δ₀ with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hδ₀
  obtain ⟨m, hm, hmδ⟩ := exists_archQuad_lt (K := K) (n := n) hδ
  set β : ContDiffBump (0 : ℝ) := ⟨m / 2, m, half_pos hm, half_lt_self hm⟩
  have hβ0 : ∀ x : ℝ, β x ≠ 0 → x < m := by
    intro x hx
    have : x ∈ Function.support β := hx
    rw [β.support_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at this
    exact lt_of_le_of_lt (le_abs_self x) this
  set ρ₀ : archGroup K n → ℝ := fun a => β (archQuad (archVal a - 1)) * β (archQuad (archVal a⁻¹ - 1))
    with hρ₀def
  have hρ₀nn : ∀ a, 0 ≤ ρ₀ a := fun a => mul_nonneg β.nonneg β.nonneg
  have hρ₀1 : ρ₀ 1 = 1 := by
    have h0 : β 0 = 1 := β.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hm).le)
    simp only [hρ₀def, inv_one, archVal, OneMemClass.coe_one, Units.val_one, sub_self, archQuad_zero, h0,
      mul_one]
  have hsmall : ∀ a, ρ₀ a ≠ 0 → ‖archVal a - 1‖ < δ ∧ ‖archVal a⁻¹ - 1‖ < δ := by
    intro a ha
    have h1 : β (archQuad (archVal a - 1)) ≠ 0 := left_ne_zero_of_mul ha
    have h2 : β (archQuad (archVal a⁻¹ - 1)) ≠ 0 := right_ne_zero_of_mul ha
    exact ⟨hmδ _ (hβ0 _ h1), hmδ _ (hβ0 _ h2)⟩

  let _ := (isExpLieAlgebra K n).chartedSpace
  have hsm : ContMDiff 𝓘(ℝ, archLie K n) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) ρ₀ := by
    rw [(isExpLieAlgebra K n).contMDiff_iff_expG]
    intro g
    have e : (fun Y : archLie K n => ρ₀ (g * (isExpLieAlgebra K n).expG Y)) = fun Y : archLie K n =>
        β (archQuad (archVal g * NormedSpace.exp (Y : ArchMatrix K n) - 1)) *
          β (archQuad (NormedSpace.exp (-(Y : ArchMatrix K n)) * archVal g⁻¹ - 1)) := by
      funext Y
      simp only [hρ₀def, archVal, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul,
        ← IsExpLieAlgebra.expG_neg, IsExpLieAlgebra.coe_expG]
      rfl
    rw [e]
    have hY : ContDiff ℝ (⊤ : ℕ∞) (fun Y : archLie K n => (Y : ArchMatrix K n)) :=
      (Submodule.subtypeL (archLie K n)).contDiff
    have hexp : ContDiff ℝ (⊤ : ℕ∞) (NormedSpace.exp : ArchMatrix K n → ArchMatrix K n) :=
      contDiff_exp ℝ _
    have hq : ContDiff ℝ (⊤ : ℕ∞) (archQuad : ArchMatrix K n → ℝ) := contDiff_archQuad.of_le le_top
    refine ContDiff.mul ?_ ?_
    · exact β.contDiff.comp (hq.comp ((contDiff_const.mul (hexp.comp hY)).sub contDiff_const))
    · exact β.contDiff.comp (hq.comp (((hexp.comp hY.neg).mul contDiff_const).sub contDiff_const))
  have hcont : Continuous ρ₀ := hsm.continuous

  set C : Set (ArchMatrix K n × (ArchMatrix K n)ᵐᵒᵖ) :=
    Metric.closedBall 1 δ ×ˢ (MulOpposite.op '' Metric.closedBall 1 δ)
  have hC : IsCompact C := (isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).image MulOpposite.continuous_op)
  have hcs : HasCompactSupport ρ₀ := by
    refine HasCompactSupport.intro (hE.isCompact_preimage hC) fun a ha => ?_
    by_contra h0
    obtain ⟨h1, h2⟩ := hsmall a h0
    refine ha ⟨Metric.mem_closedBall.2 ?_, ⟨archVal a⁻¹, Metric.mem_closedBall.2 ?_, rfl⟩⟩
    · rw [dist_eq_norm]; exact h1.le
    · rw [dist_eq_norm]; exact h2.le

  set I := ∫ a, ρ₀ a ∂ν
  have hI : 0 < I := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hρ₀nn
    (x := 1) (by rw [hρ₀1]; exact one_ne_zero)
  refine ⟨fun a => ρ₀ a / I, fun a => div_nonneg (hρ₀nn a) hI.le, ⟨?_, ?_⟩, ?_, fun a => ?_,
    fun k hk a => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp_contMDiff (hsm.div_const I)
  · have hcs' : HasCompactSupport (fun a => ρ₀ a / I) := hcs.mono fun a ha => by
      simp only [Function.mem_support] at ha ⊢
      intro h
      exact ha (by rw [h, zero_div])
    exact hcs'.comp_left Complex.ofReal_zero
  · rw [integral_div, div_self hI.ne']
  · simp only [hρ₀def, inv_inv]
    rw [mul_comm]
  · have e1 := archQuad_conj_sub hk a
    have e2 := archQuad_conj_sub hk a⁻¹
    have e3 : (k * a * k⁻¹)⁻¹ = k * a⁻¹ * k⁻¹ := by group
    simp only [hρ₀def]
    rw [e3, e1, e2]
  · have ha' : ρ₀ a ≠ 0 := fun h => ha (by simp [h])
    obtain ⟨h1, h2⟩ := hsmall a ha'
    refine hWN (hδ₁W ?_)
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨?_, ?_⟩
    · show dist (archVal a) 1 < δ₁
      rw [dist_eq_norm]; exact lt_of_lt_of_le h1 (min_le_left _ _)
    · show dist (MulOpposite.op (archVal a⁻¹)) (MulOpposite.op 1) < δ₁
      rw [MulOpposite.dist_op, dist_eq_norm]; exact lt_of_lt_of_le h2 (min_le_left _ _)
  · have ha' : ρ₀ a ≠ 0 := fun h => ha (by simp [h])
    obtain ⟨h1, -⟩ := hsmall a ha'
    have hmem : archVal a ∈ T := hδ₀T (by
      rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le h1 (min_le_right _ _))
    refine ⟨⟨(expPartialHomeomorph ℝ (ArchMatrix K n)).symm (archVal a), Submodule.mem_top⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [IsExpLieAlgebra.coe_expG]
    show archVal a = NormedSpace.exp ((expPartialHomeomorph ℝ (ArchMatrix K n)).symm (archVal a))
    rw [← coe_expPartialHomeomorph ℝ (ArchMatrix K n),
      (expPartialHomeomorph ℝ (ArchMatrix K n)).right_inv hmem]

end AutomorphicForm

end

end GroundTheory.Automorphic
