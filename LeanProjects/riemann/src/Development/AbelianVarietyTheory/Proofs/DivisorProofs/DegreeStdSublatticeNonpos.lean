import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeKernelAddImageStatement

open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

namespace GlobalTheory.StdLatDeg

variable {K : Type} [Field K] [NumberField K]

theorem fg_of_le_stdLat {n : ℕ} {W : Submodule (𝓞 K) (Fin n → K)} (hW : W ≤ stdLat K n) :
    W.FG := by
  have hFG : (stdLat K n).FG := Submodule.fg_span (Set.finite_range _)
  haveI : IsNoetherian (𝓞 K) (stdLat K n) := isNoetherian_of_fg_of_noetherian _ hFG
  have h2 := (IsNoetherian.noetherian (W.comap (stdLat K n).subtype)).map (stdLat K n).subtype
  rwa [Submodule.map_comap_eq_of_le (by simpa using hW)] at h2

theorem deg_le_zero_one (W : Submodule (𝓞 K) (Fin 1 → K)) (hW : W ≤ stdLat K 1) :
    deg (stdHerm K 1) W ≤ 0 := by
  rcases eq_or_ne W ⊥ with rfl | hne
  · rw [HadamardFrameExtension.deg_bot]
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hx00 : x 0 ≠ 0 := fun h => hx0 (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
  have hFG : (stdLat K 1).FG := Submodule.fg_span (Set.finite_range _)
  have hspan : (stdLat K 1 : Set (Fin 1 → K)) ⊆ Submodule.span K (W : Set (Fin 1 → K)) := by
    intro y _
    have : y = (y 0 / x 0) • x := by
      funext i
      rw [Subsingleton.elim i 0]
      simp [hx00]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
  rw [deg_of_le _ (fg_of_le_stdLat hW) hFG hW hspan, deg_stdLat, zero_sub, neg_nonpos]
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

def coord (K : Type) [Field K] {n : ℕ} (i : Fin n) : (Fin n → K) →ₗ[K] (Fin 1 → K) :=
  LinearMap.pi fun _ => LinearMap.proj i

omit [NumberField K] in
@[simp] theorem coord_apply {n : ℕ} (i : Fin n) (x : Fin n → K) (j : Fin 1) :
    coord K i x j = x i := rfl

theorem map_coord_le {n : ℕ} (i : Fin n) :
    (stdLat K n).map ((coord K i).restrictScalars (𝓞 K)) ≤ stdLat K 1 := by
  unfold stdLat
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  rcases eq_or_ne k i with rfl | h
  · refine Submodule.subset_span ⟨0, ?_⟩
    funext j
    rw [Subsingleton.elim j 0]
    simp
  · have : ((coord K i).restrictScalars (𝓞 K)) (Pi.single k 1 : Fin n → K) = 0 := by
      funext j
      simp [Pi.single_eq_of_ne h.symm]
    simp only [this]
    exact Submodule.zero_mem _

theorem gram_sub_posSemidef {n : ℕ} (i : Fin n) (σ : K →+* ℂ) {r : ℕ} (v : Fin r → Fin n → K) :
    ((stdHerm K n).gram σ v - (stdHerm K 1).gram σ (coord K i ∘ v)).PosSemidef := by
  classical
  let M : Matrix (Fin n) (Fin r) ℂ := Matrix.of fun k a => if k = i then 0 else σ (v a k)
  have h := Matrix.posSemidef_conjTranspose_mul_self M
  convert h using 1
  ext a b
  simp only [Matrix.sub_apply, HermFam.gram, stdHerm, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, M, Function.comp_apply, coord_apply, Finset.univ_unique,
    Finset.sum_singleton]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [if_true, mul_zero, zero_add, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [if_neg (Finset.ne_of_mem_erase hk), if_neg (Finset.ne_of_mem_erase hk)]
  rfl

theorem deg_le_zero_of_support {n : ℕ} (S : Finset (Fin n)) :
    ∀ W : Submodule (𝓞 K) (Fin n → K), W ≤ stdLat K n → (∀ x ∈ W, ∀ k, k ∉ S → x k = 0) →
      deg (stdHerm K n) W ≤ 0 := by
  classical
  induction S using Finset.induction with
  | empty =>
    intro W _ h
    have : W = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      funext k
      exact h x hx k (by simp)
    rw [this, HadamardFrameExtension.deg_bot]
  | insert i S _ ih =>
    intro W hW h
    have h1 := GlobalTheory.T.degree_le_kernel_add_image K n 1 (stdHerm K n) (stdHerm K 1) (coord K i) 1 one_pos W
      (fg_of_le_stdLat hW) (fun σ r v _ => by simpa using gram_sub_posSemidef i σ v)
    have h2 := ih (W ⊓ (LinearMap.ker (coord K i)).restrictScalars (𝓞 K)) (inf_le_left.trans hW)
      (by
        intro x hx k hk
        rcases eq_or_ne k i with rfl | hki
        · have := congrFun (LinearMap.mem_ker.mp hx.2) 0
          simpa using this
        · exact h x hx.1 k (by simp [hki, hk]))
    have h3 := deg_le_zero_one _ ((Submodule.map_mono hW).trans (map_coord_le (K := K) i))
    rw [Real.log_one, mul_zero] at h1
    linarith

theorem deg_le_zero_of_le_stdLat (K : Type) [Field K] [NumberField K] (n : ℕ)
    (W : Submodule (𝓞 K) (Fin n → K)) (hW : W ≤ stdLat K n) : deg (stdHerm K n) W ≤ 0 :=
  deg_le_zero_of_support Finset.univ W hW (fun _ _ k hk => absurd (Finset.mem_univ k) hk)

end GlobalTheory.StdLatDeg
