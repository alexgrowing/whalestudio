import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight

set_option autoImplicit false

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp.EllCount

variable {ι : Type} [Fintype ι]

def bf (A : Matrix ι ι ℝ) (x y : ι → ℝ) : ℝ := ∑ i, ∑ j, A i j * x i * y j

theorem bf_eq (A : Matrix ι ι ℝ) (x y : ι → ℝ) : bf A x y = x ⬝ᵥ A *ᵥ y := by
  simp only [bf, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem bf_comm {A : Matrix ι ι ℝ} (hA : A.PosDef) (x y : ι → ℝ) : bf A x y = bf A y x := by
  unfold bf
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : A j i = A i j := by simpa using hA.1.apply i j
  rw [h]; ring

theorem bf_nonneg {A : Matrix ι ι ℝ} (hA : A.PosDef) (x : ι → ℝ) : 0 ≤ bf A x x := by
  rw [bf_eq]
  simpa using hA.posSemidef.dotProduct_mulVec_nonneg x

theorem bf_expand {A : Matrix ι ι ℝ} (hA : A.PosDef) (x y : ι → ℝ) (t : ℝ) :
    bf A (x + t • y) (x + t • y) = bf A y y * (t * t) + 2 * bf A x y * t + bf A x x := by
  have h := bf_comm hA y x
  simp only [bf_eq] at h ⊢
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, h]
  ring

theorem bf_sq_le {A : Matrix ι ι ℝ} (hA : A.PosDef) (x y : ι → ℝ) : bf A x y ^ 2 ≤ bf A x x * bf A y y := by
  have h := discrim_le_zero (a := bf A y y) (b := 2 * bf A x y) (c := bf A x x) fun t => by
    rw [← bf_expand hA]; exact bf_nonneg hA _
  unfold discrim at h
  nlinarith

theorem bf_add_le {A : Matrix ι ι ℝ} (hA : A.PosDef) {x y : ι → ℝ} {R s : ℝ} (hR : 0 ≤ R) (hs : 0 ≤ s)
    (hx : bf A x x ≤ R ^ 2) (hy : bf A y y ≤ s ^ 2) : bf A (x + y) (x + y) ≤ (R + s) ^ 2 := by
  have h := bf_expand hA x y 1
  rw [one_smul] at h
  have h2 : bf A x y ^ 2 ≤ (R * s) ^ 2 := by
    refine (bf_sq_le hA x y).trans ?_
    rw [mul_pow]
    exact mul_le_mul hx hy (bf_nonneg hA _) (sq_nonneg _)
  have h3 : bf A x y ≤ R * s := le_of_sq_le_sq h2 (mul_nonneg hR hs)
  nlinarith

theorem bf_neg (A : Matrix ι ι ℝ) (x : ι → ℝ) : bf A (-x) (-x) = bf A x x := by
  simp [bf]

theorem finite_pts [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.PosDef) (c : ℝ) :
    {z : ι → ℤ | bf A (fun i => (z i : ℝ)) (fun i => (z i : ℝ)) ≤ c}.Finite := by
  let y : ι → ι → ℝ := fun i => A⁻¹ *ᵥ Pi.single i 1
  have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hy : ∀ (x : ι → ℝ) i, bf A x (y i) = x i := fun x i => by
    rw [bf_eq, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec]
    simp
  let M : ι → ℤ := fun i => ⌈c * bf A (y i) (y i)⌉
  refine (Set.Finite.pi' (fun i => Set.finite_Icc (-M i) (M i))).subset fun z hz i => ?_
  have h1 := bf_sq_le hA (fun i => (z i : ℝ)) (y i)
  rw [hy] at h1
  have h2 : ((z i : ℝ)) ^ 2 ≤ (M i : ℝ) :=
    h1.trans ((mul_le_mul_of_nonneg_right hz (bf_nonneg hA _)).trans (Int.le_ceil _))
  have h3 : z i ^ 2 ≤ M i := by exact_mod_cast h2
  have h4 := Int.le_self_sq (z i)
  have h5 := Int.le_self_sq (-z i)
  rw [neg_sq] at h5
  constructor <;> omega

theorem volume_eq_lintegral (E : Set (ι → ℝ)) (hE : MeasurableSet E) :
    volume E = ∫⁻ x in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1),
      (({z : ι → ℤ | x + (fun i => (z i : ℝ)) ∈ E}.encard : ℕ∞) : ENNReal) := by
  set F : Set (ι → ℝ) := Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1) with hF
  have hFm : MeasurableSet F := MeasurableSet.univ_pi fun _ => measurableSet_Ico
  let c : (ι → ℤ) → (ι → ℝ) := fun z i => (z i : ℝ)
  let G : (ι → ℤ) → Set (ι → ℝ) := fun z => E ∩ (fun x => x - c z) ⁻¹' F
  have hGm : ∀ z, MeasurableSet (G z) := fun z => hE.inter (measurable_sub_const _ hFm)
  have hmem : ∀ z x, x - c z ∈ F ↔ z = fun i => ⌊x i⌋ := fun z x => by
    simp only [hF, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Ico, Pi.sub_apply, c, funext_iff]
    refine forall_congr' fun i => ?_
    rw [eq_comm, Int.floor_eq_iff]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hU : E = ⋃ z, G z := by
    ext x
    simp only [Set.mem_iUnion, G, Set.mem_inter_iff, Set.mem_preimage, hmem]
    simp
  have hd : Pairwise (Function.onFun Disjoint G) := fun z w hzw => by
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨-, h1⟩ ⟨-, h2⟩
    exact hzw (((hmem _ _).1 h1).trans ((hmem _ _).1 h2).symm)
  have hm : ∀ z, MeasurableSet ((fun x => x + c z) ⁻¹' E) := fun z => measurable_add_const _ hE
  have h1 : ∀ z, volume (G z) = ∫⁻ x in F, ((fun x => x + c z) ⁻¹' E).indicator 1 x := fun z => by
    rw [lintegral_indicator_one (hm z), Measure.restrict_apply (hm z), ← measure_preimage_add_right volume (c z) (G z)]
    congr 1
    ext x
    simp [G]
  conv_lhs => rw [hU, measure_iUnion hd hGm]
  simp_rw [h1]
  rw [← lintegral_tsum fun z => (measurable_one.indicator (hm z)).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.tsum_set_one, tsum_subtype _ (fun _ => (1 : ENNReal))]
  refine tsum_congr fun z => ?_
  by_cases h : x + c z ∈ E
  · rw [Set.indicator_of_mem (by exact h), Set.indicator_of_mem (by exact h)]; rfl
  · rw [Set.indicator_of_notMem (by exact h), Set.indicator_of_notMem (by exact h)]

theorem volume_cube : volume (Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1)) = 1 := by
  rw [Real.volume_pi_Ico]
  simp

theorem measurableSet_ell (A : Matrix ι ι ℝ) (c : ℝ) : MeasurableSet {x : ι → ℝ | bf A x x ≤ c} := by
  refine measurableSet_le ?_ measurable_const
  unfold bf
  fun_prop

end GlobalTheory.HSAmp.EllCount

namespace GlobalTheory.HSAmp

open EllCount

theorem ellCount_volume : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ s R : ℝ, 0 ≤ s → 0 ≤ R →
    (∀ x : ι → ℝ, ∃ z : ι → ℤ, ∑ i, ∑ j, A i j * (x i - z i) * (x j - z j) ≤ s ^ 2) →
    {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.Finite ∧
    volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ R ^ 2} ≤ (ellCount A (R + s) : ENNReal) ∧
    (ellCount A R : ENNReal) ≤ volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ (R + s) ^ 2} := by
  intro ι _ _ A hA s R hs hR hcov
  let c : (ι → ℤ) → (ι → ℝ) := fun z i => (z i : ℝ)
  have hcnt : ∀ r : ℝ, (ellCount A r : ENNReal) =
      (({z : ι → ℤ | bf A (c z) (c z) ≤ r ^ 2}.encard : ℕ∞) : ENNReal) := fun r => by
    rw [← (finite_pts hA (r ^ 2)).cast_ncard_eq]
    rfl
  have hcov' : ∀ x : ι → ℝ, ∃ z : ι → ℤ, bf A (x - c z) (x - c z) ≤ s ^ 2 := hcov
  refine ⟨finite_pts hA _, ?_, ?_⟩
  · change volume {x : ι → ℝ | bf A x x ≤ R ^ 2} ≤ _
    rw [volume_eq_lintegral _ (measurableSet_ell A _)]
    refine (lintegral_mono (g := fun _ => (ellCount A (R + s) : ENNReal)) fun x => ?_).trans ?_
    · obtain ⟨z₀, h₀⟩ := hcov' x
      rw [hcnt]
      refine ENat.toENNReal_le.2 (Set.encard_le_encard_of_injOn (f := fun z => z + z₀) (fun z hz => ?_)
        (add_left_injective z₀).injOn)
      rw [← bf_neg] at h₀
      have h := bf_add_le hA hR hs hz h₀
      have e : x + (fun i => (z i : ℝ)) + -(x - c z₀) = c (z + z₀) := by
        ext i; simp [c]; ring
      rw [e] at h
      exact h
    · rw [setLIntegral_const, volume_cube, mul_one]
  · change _ ≤ volume {x : ι → ℝ | bf A x x ≤ (R + s) ^ 2}
    rw [volume_eq_lintegral _ (measurableSet_ell A _)]
    refine le_trans ?_ (lintegral_mono (f := fun _ => (ellCount A R : ENNReal)) fun x => ?_)
    · rw [setLIntegral_const, volume_cube, mul_one]
    · obtain ⟨z₀, h₀⟩ := hcov' x
      rw [hcnt]
      refine ENat.toENNReal_le.2 (Set.encard_le_encard_of_injOn (f := fun z => z - z₀) (fun z hz => ?_)
        (sub_left_injective).injOn)
      have h := bf_add_le hA hR hs hz h₀
      have e : c z + (x - c z₀) = x + fun i => (((z - z₀) i : ℤ) : ℝ) := by
        ext i; simp [c]; ring
      rw [e] at h
      exact h

end GlobalTheory.HSAmp
