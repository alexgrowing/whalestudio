import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.EichAlongSub

namespace ReciprocityTheory.ChartRestriction.G.SA

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}

variable (σ J) in

def hm (e f : ι → K) (M : Matrix (Fin 2) (Fin 2) K) : Matrix ι ι K :=
  1 + (M 0 0 - 1) • vecMulVec e (J *ᵥ (σ ∘ f)) + M 0 1 • vecMulVec e (J *ᵥ (σ ∘ e))
    + M 1 0 • vecMulVec f (J *ᵥ (σ ∘ f)) + (M 1 1 - 1) • vecMulVec f (J *ᵥ (σ ∘ e))

variable (σ J) in
theorem hm_mulVec (e f : ι → K) (M : Matrix (Fin 2) (Fin 2) K) (x : ι → K) :
    hm σ J e f M *ᵥ x = x + ((M 0 0 - 1) * hf σ J x f + M 0 1 * hf σ J x e) • e
      + (M 1 0 * hf σ J x f + (M 1 1 - 1) * hf σ J x e) • f := by
  have hfd : ∀ x y : ι → K, ∑ i, (J *ᵥ (σ ∘ y)) i * x i = hf σ J x y := by
    intro x y
    simp only [hf, Matrix.mulVec, dotProduct, Function.comp_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have key : ∀ u y : ι → K, vecMulVec u (J *ᵥ (σ ∘ y)) *ᵥ x = hf σ J x y • u := by
    intro u y
    ext i
    rw [← hfd x y, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    simp only [Matrix.mulVec, dotProduct, vecMulVec_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hs : ∀ (a : K) (A : Matrix ι ι K) (v : ι → K), (a • A) *ᵥ v = a • (A *ᵥ v) := by
    intro a A v
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
      Finset.mul_sum, mul_assoc]
  simp only [hm, Matrix.add_mulVec, Matrix.one_mulVec, hs, key]
  module

section
variable {e f : ι → K} (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef

theorem hm_mul (M M' : Matrix (Fin 2) (Fin 2) K) :
    hm σ J e f M * hm σ J e f M' = hm σ J e f (M * M') := by
  have matrix_eq_of_mulVec_eq_lemma_2 {ι : Type _} [Fintype ι] [DecidableEq ι] {K : Type _} [CommRing K] {A B : Matrix ι ι K} (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B := by
    first
      | exact Matrix.ext_of_mulVec_single fun i => h _
      | exact Matrix.toLin'.injective (LinearMap.ext fun x => by simpa using h x)
  have hfe : hf σ J f e = 1 := hf_fe hσ hJ he hff hef
  refine matrix_eq_of_mulVec_eq_lemma_2 fun x => ?_
  rw [← Matrix.mulVec_mulVec]
  simp only [hm_mulVec, hf_add_left, hf_smul_left, he, hff, hef, hfe,
    Matrix.mul_apply, Fin.sum_univ_two]
  module

theorem hm_det (M : Matrix (Fin 2) (Fin 2) K) : (hm σ J e f M).det = M.det := by
  have hfd : ∀ x y : ι → K, ∑ i, (J *ᵥ (σ ∘ y)) i * x i = hf σ J x y := by
    intro x y
    simp only [hf, Matrix.mulVec, dotProduct, Function.comp_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hfe : hf σ J f e = 1 := hf_fe hσ hJ he hff hef
  set U : Matrix ι (Fin 2) K := Matrix.of fun i a => ![e i, f i] a with hU
  set V : Matrix (Fin 2) ι K := Matrix.of ![J *ᵥ (σ ∘ f), J *ᵥ (σ ∘ e)] with hV
  have hVU : V * U = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [hV, hU, Matrix.mul_apply, hfd, he, hff, hef, hfe]
  have hform : hm σ J e f M = 1 + U * (M - 1) * V := by
    ext i j
    simp [hm, hU, hV, Matrix.mul_apply, Fin.sum_univ_two, vecMulVec_apply, Matrix.sub_apply,
      Matrix.one_apply]
    ring
  rw [hform, Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc, hVU, Matrix.one_mul,
    add_sub_cancel]

end

variable (σ J) in
theorem unitaryTransvection_zero_first (e f : ι → K) (c : K) : eich σ J e 0 c = hm σ J e f !![1, c; 0, 1] := by
  have h0 : (σ ∘ (0 : ι → K)) = 0 := by
    funext j
    simp
  ext i j
  simp [eich, hm, h0, vecMulVec_apply]
  try ring

variable (σ J) in
theorem unitaryTransvection_zero_second (e f : ι → K) (c : K) : eich σ J f 0 c = hm σ J e f !![1, 0; c, 1] := by
  have h0 : (σ ∘ (0 : ι → K)) = 0 := by
    funext j
    simp
  ext i j
  simp [eich, hm, h0, vecMulVec_apply]
  try ring

variable (σ J) in
theorem tor_hm (e f : ι → K) (l m : K) : tor σ J e f l m = hm σ J e f !![l, 0; 0, m] := by
  ext i j
  simp [tor, hm, vecMulVec_apply]
  try ring

variable (σ J) in
theorem tor_swap (e f : ι → K) (l m : K) : tor σ J e f l m = tor σ J f e m l := by
  have matrix_eq_of_mulVec_eq_lemma_2 {ι : Type _} [Fintype ι] [DecidableEq ι] {K : Type _} [CommRing K] {A B : Matrix ι ι K} (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B := by
    first
      | exact Matrix.ext_of_mulVec_single fun i => h _
      | exact Matrix.toLin'.injective (LinearMap.ext fun x => by simpa using h x)
  refine matrix_eq_of_mulVec_eq_lemma_2 fun x => ?_
  rw [tor_mulVec, tor_mulVec]
  abel

private theorem matrix_fin_two_eq_of_entries_eq {α : Type*} {p q r s p' q' r' s' : α} (h1 : p = p') (h2 : q = q')
    (h3 : r = r') (h4 : s = s') : !![p, q; r, s] = !![p', q'; r', s'] := by
  subst h1 h2 h3 h4; rfl

theorem w_eq {a ai : K} (h : a * ai = 1) :
    !![1, a; 0, 1] * !![1, 0; -ai, 1] * !![1, a; 0, 1] = !![(0 : K), a; -ai, 0] := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact matrix_fin_two_eq_of_entries_eq (by linear_combination -h) (by linear_combination -a * h) (by ring)
    (by linear_combination -h)

section
variable {e f : ι → K} (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef

theorem unitaryTransvection_zero_first_mem_closure {c : K} (hc : σ c = -c) : eich σ J e 0 c ∈ Submonoid.closure (eichSet σ J e f) := by
  refine Submonoid.subset_closure (Or.inl ⟨0, c, hf_zero_left σ J e, hf_zero_left σ J f, ?_, rfl⟩)
  rw [hc, hf_zero_left]
  ring

theorem unitaryTransvection_zero_second_mem_closure {c : K} (hc : σ c = -c) : eich σ J f 0 c ∈ Submonoid.closure (eichSet σ J e f) := by
  refine Submonoid.subset_closure (Or.inr ⟨0, c, hf_zero_left σ J f, hf_zero_left σ J e, ?_, rfl⟩)
  rw [hc, hf_zero_left]
  ring

theorem tor_mem_closure {δ di l li : K} (hσδ : σ δ = -δ) (hδ : δ * di = 1) (hl : σ l = l)
    (hli : l * li = 1) : tor σ J e f l li ∈ Submonoid.closure (eichSet σ J e f) := by
  have hmul : ∀ A B : Matrix (Fin 2) (Fin 2) K,
      hm σ J e f A ∈ Submonoid.closure (eichSet σ J e f) →
      hm σ J e f B ∈ Submonoid.closure (eichSet σ J e f) →
      hm σ J e f (A * B) ∈ Submonoid.closure (eichSet σ J e f) := by
    intro A B hA hB
    rw [← hm_mul hσ hJ he hff hef]
    exact Submonoid.mul_mem _ hA hB
  have hup : ∀ c : K, σ c = -c →
      hm σ J e f !![1, c; 0, 1] ∈ Submonoid.closure (eichSet σ J e f) := by
    intro c hc
    rw [← unitaryTransvection_zero_first σ J e f c]
    exact unitaryTransvection_zero_first_mem_closure hσ hJ he hff hef hc
  have hlow : ∀ c : K, σ c = -c →
      hm σ J e f !![1, 0; c, 1] ∈ Submonoid.closure (eichSet σ J e f) := by
    intro c hc
    rw [← unitaryTransvection_zero_second σ J e f c]
    exact unitaryTransvection_zero_second_mem_closure hσ hJ he hff hef hc
  have hw : ∀ a ai : K, σ a = -a → a * ai = 1 →
      hm σ J e f !![0, a; -ai, 0] ∈ Submonoid.closure (eichSet σ J e f) := by
    intro a ai ha h
    have h1 : σ a * σ ai = 1 := by rw [← map_mul, h, map_one]
    rw [ha] at h1
    have hs : σ ai = -ai := by linear_combination (-ai) * h1 - σ ai * h
    have hs' : σ (-ai) = -(-ai) := by rw [map_neg, hs]
    rw [← w_eq h]
    exact hmul _ _ (hmul _ _ (hup a ha) (hlow _ hs')) (hup a ha)
  have key : (!![l, 0; 0, li] : Matrix (Fin 2) (Fin 2) K) =
      !![0, l * δ; -(li * di), 0] * !![0, -δ; -(-di), 0] := by
    rw [Matrix.mul_fin_two]
    exact matrix_fin_two_eq_of_entries_eq (by linear_combination -l * hδ) (by ring) (by ring)
      (by linear_combination -li * hδ)
  rw [tor_hm, key]
  refine hmul _ _ (hw _ _ ?_ ?_) (hw _ _ ?_ ?_)
  · rw [map_mul, hl, hσδ]; ring
  · linear_combination (δ * di) * hli + hδ
  · rw [map_neg, hσδ]
  · linear_combination hδ

theorem tor_det (l m : K) : (tor σ J e f l m).det = l * m := by
  rw [tor_hm, hm_det hσ hJ he hff hef, Matrix.det_fin_two_of]
  ring

end

end ReciprocityTheory.ChartRestriction.G.SA
