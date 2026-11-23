import Formalism.SuccessiveMinima.DefsNP
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NewtonSlope

open Filter Topology Polynomial

noncomputable section

namespace Formalism.FN.WDiv

section General
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]

lemma term_eq (a b : ℕ → K) (r : ℝ) {n i : ℕ} (hi : i ≤ n) :
    ‖a i * b (n - i)‖ * r ^ n = (‖a i‖ * r ^ i) * (‖b (n - i)‖ * r ^ (n - i)) := by
  rw [norm_mul]
  have : r ^ n = r ^ i * r ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
  rw [this]; ring

lemma series_bound (u : ℕ → ℕ → K) {r : ℝ} (hr : 0 < r) (j : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖u i j‖ * r ^ j ≤ C) : ‖∑' i, u i j‖ * r ^ j ≤ C := by
  rw [← le_div_iff₀ (pow_pos hr j)]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
    fun i => (le_div_iff₀ (pow_pos hr j)).2 (h i)

variable [CompleteSpace K]

end General

end Formalism.FN.WDiv

namespace Formalism.FN.WDiv

section PolyDiv
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]

def cN (G : K[X]) (N : ℕ) (P : K[X]) : K := P.coeff N / G.coeff N

def QR (G : K[X]) (N : ℕ) : ℕ → K[X] × K[X]
  | 0 => (C (cN G N 1), 1 - C (cN G N 1) * G)
  | m + 1 => (X * (QR G N m).1 + C (cN G N (X * (QR G N m).2)),
      X * (QR G N m).2 - C (cN G N (X * (QR G N m).2)) * G)

variable (G : K[X]) (N : ℕ) {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
  (hGN : ‖G.coeff N‖ * r ^ N = M) (hGle : ∀ j, ‖G.coeff j‖ * r ^ j ≤ M)
  (hGhi : ∀ j, N < j → G.coeff j = 0)
include hr hM hGN hGle hGhi

end PolyDiv

end Formalism.FN.WDiv

namespace Formalism.FN.WDiv

section SeriesDiv
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

def Dq (G : K[X]) (N : ℕ) (f : ℕ → K) (j : ℕ) : K := ∑' m, f m * (QR G N m).1.coeff j

def DR (G : K[X]) (N : ℕ) (f : ℕ → K) (j : ℕ) : K := ∑' m, f m * (QR G N m).2.coeff j

variable (G : K[X]) (N : ℕ) {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
  (hGN : ‖G.coeff N‖ * r ^ N = M) (hGle : ∀ j, ‖G.coeff j‖ * r ^ j ≤ M)
  (hGhi : ∀ j, N < j → G.coeff j = 0)
include hr hM hGN hGle hGhi

end SeriesDiv

section Main
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

def iterF (G : K[X]) (N : ℕ) (H f : ℕ → K) : ℕ → ℕ → K
  | 0 => f
  | i + 1 => fun n => -(cmul (Dq G N (iterF G N H f i)) H n)

omit [CompleteSpace K] in
lemma exists_eps (g : ℕ → K) (r : ℝ) (hr : 0 < r) (hg : ConvOn g r) (hne : g ≠ 0) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ ∀ k, wdeg g r < k → ‖g k‖ * r ^ k ≤ ε * gNorm g r := by
  obtain ⟨-, hM⟩ := wdeg_spec g r hr hg hne
  have hle : ∀ k, ‖g k‖ * r ^ k ≤ gNorm g r := fun k => le_ciSup (gNorm_bdd_of_conv g r hg) k
  obtain ⟨K0, hK0⟩ := eventually_atTop.1
    ((hg : Tendsto _ atTop _).eventually (eventually_le_nhds (half_pos hM)))
  have hbdd : BddAbove {k : ℕ | ‖g k‖ * r ^ k = gNorm g r} := ⟨K0, fun k hk => by
    simp only [Set.mem_ofPred_eq] at hk
    by_contra h; push Not at h
    have := hK0 k h.le
    rw [hk] at this; linarith⟩
  have hlt : ∀ k, wdeg g r < k → ‖g k‖ * r ^ k < gNorm g r := by
    intro k hk
    refine lt_of_le_of_ne (hle k) fun h => ?_
    have : k ≤ wdeg g r := le_csSup hbdd h
    omega
  obtain ⟨k1, hk1T, hk1⟩ := Finset.exists_max_image (Finset.Icc (wdeg g r + 1) (max K0 (wdeg g r + 1)))
    (fun k => ‖g k‖ * r ^ k) ⟨wdeg g r + 1, by simp⟩
  have hk1lt : ‖g k1‖ * r ^ k1 < gNorm g r := hlt k1 (by simp at hk1T; omega)
  refine ⟨max (‖g k1‖ * r ^ k1 / gNorm g r) (1 / 2), le_max_of_le_right (by norm_num),
    max_lt ((div_lt_one hM).2 hk1lt) (by norm_num), fun k hk => ?_⟩
  rw [max_mul_of_nonneg _ _ hM.le]
  by_cases hkK : k ≤ max K0 (wdeg g r + 1)
  · have := hk1 k (by simp; omega)
    exact le_max_of_le_left (by rw [div_mul_cancel₀ _ hM.ne']; exact this)
  · exact le_max_of_le_right (by have := hK0 k (by omega); linarith)

end Main

end Formalism.FN.WDiv

namespace Formalism.FN

end Formalism.FN
