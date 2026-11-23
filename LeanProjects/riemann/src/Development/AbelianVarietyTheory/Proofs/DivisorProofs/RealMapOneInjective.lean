import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds

open Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open GlobalTheory.PELU
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj imForm imForm_apply herm_add_left herm_add_right
  herm_smul_left herm_smul_right herm_conj riemann_symm eq_zero_of_imForm det_ne_zero_of_pos colMat colMat_apply
  exists_finset_of_mem_nhds)

namespace GlobalTheory.PerCoordU

noncomputable section

variable {g : ℕ}

def Tsp {O : Type} [Ring O] (bar : O → O) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) :
    Submodule ℂ (Matrix (Fin g) (Fin g) ℂ) where
  carrier := {S | Sᵀ = S ∧ ∀ a, S * (ρ (bar a)).map star = (ρ a)ᴴ * S}
  zero_mem' := ⟨by simp, fun a => by simp⟩
  add_mem' := by
    rintro S T ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [transpose_add, h1, h3], fun a => by rw [Matrix.add_mul, Matrix.mul_add, h2, h4]⟩
  smul_mem' := by
    rintro c S ⟨h1, h2⟩
    exact ⟨by rw [transpose_smul, h1], fun a => by rw [Matrix.smul_mul, Matrix.mul_smul, h2]⟩

theorem star_mulVec_map (M : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : star (M *ᵥ z) = M.map star *ᵥ star z := by
  funext i; simp [mulVec, dotProduct]

theorem herm_mulVec_left (M A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M (A *ᵥ z) w = hermForm (Aᵀ * M) z w := by
  unfold hermForm
  rw [← mulVec_mulVec, dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]

theorem herm_mulVec_right (M A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M z (A *ᵥ w) = hermForm (M * A.map star) z w := by
  unfold hermForm
  rw [star_mulVec_map, mulVec_mulVec]

theorem herm_single (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (i j : Fin g) :
    hermForm M (Pi.single i c) (Pi.single j 1) = c * M i j := by
  simp [hermForm, ← Pi.single_star, mulVec_single]

theorem sesq_ext {N N' : Matrix (Fin g) (Fin g) ℂ} (h : ∀ z w, (hermForm N z w).im = (hermForm N' z w).im) : N = N' := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have h2 := h (Pi.single i Complex.I) (Pi.single j 1)
  simp only [herm_single] at h1 h2
  simp at h1 h2
  apply Complex.ext <;> linarith

variable {O : Type} [Ring O] {bar : O → O} {D : PLat O bar} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}

theorem ext_per {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ρ P) {W : Type} [AddCommGroup W] [Module ℝ W]
    {f f' : (Fin g → ℂ) →ₗ[ℝ] W} (h : ∀ x, f (P x) = f' (P x)) : f = f' :=
  LinearMap.ext_on_range hP.2.2.2.1 h

theorem relation_per {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P) (c : D.La →₀ ℝ)
    (hc : Finsupp.linearCombination ℝ P₀ c = 0) : Finsupp.linearCombination ℝ P c = 0 := by
  obtain ⟨M₀, -, -, h₀⟩ := hP₀.2.2.2.2
  obtain ⟨M, -, hpos, h⟩ := hP.2.2.2.2
  refine eq_zero_of_imForm hpos (ext_per hP fun y => ?_)
  have := congrArg (fun u => imForm M₀ u (P₀ y)) hc
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, imForm_apply, h, h₀, map_zero, LinearMap.zero_apply] at this ⊢
  exact this

theorem exists_colMat_per {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) :
    ∃ α β : Fin g → (D.La →₀ ℂ), ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D ρ P →
      ∀ x, P x = realMap (colMat α P) (colMat β P) (P₀ x) := by
  have hs : ∀ z : Fin g → ℂ, ∃ c : D.La →₀ ℝ, Finsupp.linearCombination ℝ P₀ c = z := fun z => by
    have : z ∈ Submodule.span ℝ (Set.range P₀) := by rw [hP₀.2.2.2.1]; trivial
    rwa [← Finsupp.range_linearCombination] at this
  choose r hr using fun j => hs (Pi.single j 1)
  choose r' hr' using fun j => hs (Pi.single j Complex.I)
  let k : (D.La →₀ ℝ) → (D.La →₀ ℂ) := Finsupp.mapRange (fun t => (t : ℂ)) (by simp)
  have hk : ∀ (f : D.La → Fin g → ℂ) c, Finsupp.linearCombination ℂ f (k c) = Finsupp.linearCombination ℝ f c :=
    fun f c => by
      simp only [Finsupp.linearCombination_apply, k]
      rw [Finsupp.sum_mapRange_index (by simp)]
      rfl
  refine ⟨fun j => (1 / 2 : ℂ) • k (r j) - (Complex.I / 2) • k (r' j),
    fun j => (1 / 2 : ℂ) • k (r j) + (Complex.I / 2) • k (r' j), fun P hP x => ?_⟩
  have := relation_per hP₀ hP (Finsupp.single x 1 - ∑ j, ((P₀ x j).re • r j + (P₀ x j).im • r' j)) (by
    simp only [map_sub, map_sum, map_add, map_smul, hr, hr', Finsupp.linearCombination_single, one_smul]
    funext i
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib])
  simp only [map_sub, map_sum, map_add, map_smul, Finsupp.linearCombination_single, one_smul, sub_eq_zero] at this
  rw [this]
  funext i
  simp only [realMap_apply, Pi.add_apply, mulVec, dotProduct, colMat_apply, map_sub, map_add, map_smul, hk,
    Finset.sum_apply, ← Finset.sum_add_distrib, Pi.smul_apply, Pi.sub_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  apply Complex.ext <;> simp <;> ring

theorem comm_realMap_per {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (a : O) :
    ρ a * A = A * ρ a ∧ ρ a * B = B * (ρ a).map star := by
  refine realMap_inj (ext_per hP₀ fun x => ?_)
  have := h (a • x)
  rw [hP.1, hP₀.1, h] at this
  simp only [realMap_apply, mulVec_add, mulVec_mulVec, star_mulVec_map] at this ⊢
  exact this

theorem comm_herm_per {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) {M : Matrix (Fin g) (Fin g) ℂ}
    (hM : ∀ x y, (hermForm M (P₀ x) (P₀ y)).im = D.EF x y) (a : O) :
    (ρ a)ᵀ * M = M * (ρ (bar a)).map star := by
  have key : (imForm M).compl₁₂ (realMap (ρ a) 0) LinearMap.id =
      (imForm M).compl₁₂ LinearMap.id (realMap (ρ (bar a)) 0) := by
    refine ext_per hP₀ fun x => ext_per hP₀ fun y => ?_
    simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
      ← hP₀.1, imForm_apply, hM, D.adj]
  refine sesq_ext fun z w => ?_
  have := LinearMap.congr_fun₂ key z w
  simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
    imForm_apply] at this
  rw [← herm_mulVec_left, ← herm_mulVec_right]
  exact this

theorem map_star_transpose (M : Matrix (Fin g) (Fin g) ℂ) : (M.map star)ᵀ = Mᴴ := rfl

theorem mem_Tsp_of_period {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P)
    {M₀ : Matrix (Fin g) (Fin g) ℂ} (hM₀ : ∀ x y, (hermForm M₀ (P₀ x) (P₀ y)).im = D.EF x y)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (hA : A.det ≠ 0) :
    (A⁻¹ * B)ᵀ * M₀ ∈ Tsp bar ρ := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨M, hM, -, hE⟩ := hP.2.2.2.2
    have key : (imForm M).compl₁₂ (realMap A B) (realMap A B) = imForm M₀ := by
      refine ext_per hP₀ fun x => ext_per hP₀ fun y => ?_
      simp only [LinearMap.compl₁₂_apply, ← h, imForm_apply, hE, hM₀]
    ext i j
    rw [transpose_apply]
    refine riemann_symm (M := Aᵀ * M * A.map star) ?_ (fun z w => ?_) j i
    · have := isHermitian_conjTranspose_mul_mul (A.map star) hM
      convert this using 3
      ext i j; simp
    · rw [GlobalTheory.PeriodConn.hermForm_conj_mul]
      simp only [mulVec_add, mulVec_mulVec, mul_nonsing_inv_cancel_left _ _ hu]
      exact LinearMap.congr_fun₂ key z w
  · obtain ⟨h1, h2⟩ := comm_realMap_per hP₀ hP h a
    have h3 : ρ a * (A⁻¹ * B) = A⁻¹ * B * (ρ a).map star := by
      rw [Matrix.mul_assoc, ← h2]
      have : A⁻¹ * (ρ a * A) * A⁻¹ = A⁻¹ * (A * ρ a) * A⁻¹ := by rw [h1]
      rw [nonsing_inv_mul_cancel_left _ _ hu, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hu] at this
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, this]
    rw [Matrix.mul_assoc, ← comm_herm_per hP₀ hM₀ a, ← Matrix.mul_assoc, ← transpose_mul, h3, transpose_mul,
      map_star_transpose, Matrix.mul_assoc]

theorem comm_of_mem_Tsp {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) {M₀ : Matrix (Fin g) (Fin g) ℂ}
    (hM₀ : ∀ x y, (hermForm M₀ (P₀ x) (P₀ y)).im = D.EF x y) (hdet : M₀.det ≠ 0) {C : Matrix (Fin g) (Fin g) ℂ}
    (hC : Cᵀ * M₀ ∈ Tsp bar ρ) (a : O) : ρ a * C = C * (ρ a).map star := by
  have hu : IsUnit M₀.det := isUnit_iff_ne_zero.mpr hdet
  have h := hC.2 a
  rw [Matrix.mul_assoc, ← comm_herm_per hP₀ hM₀ a, ← Matrix.mul_assoc, ← transpose_mul, ← map_star_transpose,
    ← Matrix.mul_assoc, ← transpose_mul] at h
  have := congrArg (· * M₀⁻¹) h
  simp only [mul_nonsing_inv_cancel_right _ _ hu] at this
  exact transpose_injective this

theorem realMap_one_injective {C : Matrix (Fin g) (Fin g) ℂ} (h : (1 - C * C.map star).det ≠ 0) :
    Function.Injective (realMap 1 C) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  rw [realMap_apply, one_mulVec] at hz
  have h1 : z = -(C *ᵥ star z) := eq_neg_of_add_eq_zero_left hz
  have h2 : star z = -(C.map star *ᵥ z) := by
    have := congrArg star hz
    rw [star_add, star_mulVec_map, star_star, star_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  refine eq_zero_of_mulVec_eq_zero h ?_
  rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, ← neg_neg (C.map star *ᵥ z), ← h2, mulVec_neg, ← h1, sub_self]

end

end GlobalTheory.PerCoordU
