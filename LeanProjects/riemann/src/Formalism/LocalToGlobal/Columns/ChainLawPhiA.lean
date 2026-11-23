import Formalism.LocalToGlobal.Columns.ChainLawPhi
import Formalism.LocalToGlobal.Columns.StdBasisFlagSubmoduleOfBlockTriangular

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

section ClPfNat

variable {k₀ rS r t : ℕ}

theorem clPf_beta_lt_iff (hr : k₀ + rS < r) (p : ℕ) : betaExponentOfRanks k₀ rS r t p < r ↔ p < r := by
  unfold betaExponentOfRanks symIdx
  have h0 := Nat.zero_le ((p - r) / t)
  split_ifs <;> constructor <;> intro _ <;> omega

theorem clPf_beta_inj (hr : k₀ + rS < r) {p u : ℕ} (hp : p < r) (h : betaExponentOfRanks k₀ rS r t u = betaExponentOfRanks k₀ rS r t p) : u = p := by
  unfold betaExponentOfRanks symIdx at h
  have h0 := Nat.zero_le ((u - r) / t)
  split_ifs at h <;> omega

theorem clPf_beta_of_ge {p : ℕ} (hp : r ≤ p) : betaExponentOfRanks k₀ rS r t p = r + (p - r) / t := by
  unfold betaExponentOfRanks
  rw [if_neg (show ¬ p < r by omega)]

theorem clPf_beta_A (hr : k₀ + rS < r) (ht : 0 < t) {A J : ℕ} (hA : A = r + J * t) {p p' : ℕ} (hp' : p' < A)
    (h : betaExponentOfRanks k₀ rS r t p ≤ betaExponentOfRanks k₀ rS r t p') : p < A := by
  subst hA
  by_cases hp : p < r
  · omega
  have hpr : ¬ p' < r → (p' - r) / t < J := fun h' => (Nat.div_lt_iff_lt_mul ht).mpr (by omega)
  have h0 := Nat.zero_le ((p - r) / t)
  have h0' := Nat.zero_le ((p' - r) / t)
  have hp2 : (p - r) / t < J := by
    by_cases h' : p' < r
    · unfold betaExponentOfRanks symIdx at h
      split_ifs at h <;> omega
    · have h'' := hpr h'
      unfold betaExponentOfRanks symIdx at h
      split_ifs at h <;> omega
  have h3 := (Nat.div_lt_iff_lt_mul ht).mp hp2
  omega

theorem clPf_beta_lt_blk (hr : k₀ + rS < r) (ht : 0 < t) {J u : ℕ} (hu : u < r + J * t) :
    betaExponentOfRanks k₀ rS r t u < r + J := by
  unfold betaExponentOfRanks
  split_ifs with hu'
  · unfold symIdx
    split_ifs <;> omega
  · have h := (Nat.div_lt_iff_lt_mul ht).mpr (show u - r < J * t by omega)
    omega

theorem clPf_beta_eps (hr : k₀ + rS < r) {p u : ℕ} (hp : p < k₀) (h1 : betaExponentOfRanks k₀ rS r t p ≤ betaExponentOfRanks k₀ rS r t u)
    (h2 : betaExponentOfRanks k₀ rS r t u ≤ betaExponentOfRanks k₀ rS r t (k₀ + rS)) (hu : u ≠ k₀ + rS) : u < k₀ := by
  unfold betaExponentOfRanks symIdx at h1 h2
  have h0 := Nat.zero_le ((u - r) / t)
  have h0' := Nat.zero_le ((p - r) / t)
  have h0'' := Nat.zero_le ((k₀ + rS - r) / t)
  split_ifs at h1 h2 <;> omega

theorem clPf_beta_blk (hr : k₀ + rS < r) (ht : 0 < t) {i u : ℕ} (h : betaExponentOfRanks k₀ rS r t u = r + i) :
    r + i * t ≤ u ∧ u < r + i * t + t := by
  by_cases hu : u < r
  · exfalso
    unfold betaExponentOfRanks symIdx at h
    split_ifs at h <;> omega
  · rw [clPf_beta_of_ge (by omega)] at h
    have hd : (u - r) / t = i := by omega
    have h1 := Nat.div_add_mod (u - r) t
    rw [hd, Nat.mul_comm] at h1
    have h2 := Nat.mod_lt (u - r) ht
    omega

end ClPfNat

section ClPfCore

variable {k : Type} [CommRing k] {k₀ rS r t : ℕ}

def clPfPat (k₀ rS r t N A : ℕ) (X : ℕ → ℕ → k) : Prop :=
  (∀ p', p' < r → X p' p' = 1) ∧
    ∀ p p', p < N → p' < A → p ≠ p' → X p p' ≠ 0 →
      p < A ∧ betaExponentOfRanks k₀ rS r t p ≤ betaExponentOfRanks k₀ rS r t p' ∧ ¬ (p' = k₀ + rS ∧ p < k₀)

def clPfMul (N : ℕ) (X Y : ℕ → ℕ → k) : ℕ → ℕ → k := fun p p' => ∑ u ∈ Finset.range N, X p u * Y u p'

theorem clPf_exists_of_sum {N : ℕ} {X Y : ℕ → ℕ → k} {p p' : ℕ} (h : clPfMul N X Y p p' ≠ 0) :
    ∃ u, u < N ∧ X p u ≠ 0 ∧ Y u p' ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  unfold clPfMul
  apply Finset.sum_eq_zero
  intro u hu
  rw [Finset.mem_range] at hu
  by_cases hx : X p u = 0
  · rw [hx, zero_mul]
  · rw [hc u hu hx, mul_zero]

theorem clPf_diag_mul (hr : k₀ + rS < r) {N : ℕ} (hrN : r ≤ N) {X Y : ℕ → ℕ → k} {p' : ℕ}
    (hX1 : ∀ p', p' < r → X p' p' = 1) (hY1 : ∀ p', p' < r → Y p' p' = 1)
    (hX : ∀ u, u < N → u ≠ p' → X p' u ≠ 0 → betaExponentOfRanks k₀ rS r t p' ≤ betaExponentOfRanks k₀ rS r t u)
    (hY : ∀ u, u < N → u ≠ p' → Y u p' ≠ 0 → betaExponentOfRanks k₀ rS r t u ≤ betaExponentOfRanks k₀ rS r t p') (hp' : p' < r) :
    clPfMul N X Y p' p' = 1 := by
  unfold clPfMul
  rw [Finset.sum_eq_single p']
  · rw [hX1 p' hp', hY1 p' hp', mul_one]
  · intro u hu hne
    rw [Finset.mem_range] at hu
    by_contra h0
    have h0' : X p' u * Y u p' ≠ 0 := h0
    exact hne (clPf_beta_inj hr hp' (le_antisymm (hY u hu hne (right_ne_zero_of_mul h0'))
      (hX u hu hne (left_ne_zero_of_mul h0'))))
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem clPf_pat_mulL (hr : k₀ + rS < r) (ht : 0 < t) {N A J : ℕ} (hA : A = r + J * t) (hAN : A ≤ N)
    {G X : ℕ → ℕ → k} (hG : clPfPat k₀ rS r t N N G) (hX : clPfPat k₀ rS r t N A X) :
    clPfPat k₀ rS r t N A (clPfMul N G X) := by
  have hrA : r ≤ A := by rw [hA]; omega
  unfold clPfPat at hG hX ⊢
  refine ⟨fun p' hp' => ?_, fun p p' hp hp' hne hZ => ?_⟩
  · exact clPf_diag_mul hr (by omega : r ≤ N) hG.1 hX.1
      (fun u hu hne h => (hG.2 p' u (by omega) hu (Ne.symm hne) h).2.1)
      (fun u hu hne h => (hX.2 u p' hu (by omega) hne h).2.1) hp'
  · obtain ⟨u, hu, hg, hx⟩ := clPf_exists_of_sum hZ
    by_cases hup : u = p
    · subst hup
      exact hX.2 u p' hp hp' hne hx
    by_cases hup' : u = p'
    · subst hup'
      have g := hG.2 p u hp hu hne hg
      exact ⟨clPf_beta_A hr ht hA hp' g.2.1, g.2.1, g.2.2⟩
    have g := hG.2 p u hp hu (Ne.symm hup) hg
    have x := hX.2 u p' hu hp' hup' hx
    have hb : betaExponentOfRanks k₀ rS r t p ≤ betaExponentOfRanks k₀ rS r t p' := le_trans g.2.1 x.2.1
    refine ⟨clPf_beta_A hr ht hA hp' hb, hb, ?_⟩
    rintro ⟨h1, h2⟩
    subst h1
    have hu0 : u ≠ k₀ + rS := fun h => g.2.2 ⟨h, h2⟩
    exact x.2.2 ⟨rfl, clPf_beta_eps hr h2 g.2.1 x.2.1 hu0⟩

theorem clPf_pat_mulR (hr : k₀ + rS < r) {N A : ℕ} (hrA : r ≤ A) (hAN : A ≤ N)
    {X K : ℕ → ℕ → k} (hX : clPfPat k₀ rS r t N A X) (hK : clPfPat k₀ rS r t A A K) :
    clPfPat k₀ rS r t N A (clPfMul A X K) := by
  unfold clPfPat at hX hK ⊢
  refine ⟨fun p' hp' => ?_, fun p p' hp hp' hne hZ => ?_⟩
  · exact clPf_diag_mul hr hrA hX.1 hK.1
      (fun u hu hne h => (hX.2 p' u (by omega) hu (Ne.symm hne) h).2.1)
      (fun u hu hne h => (hK.2 u p' hu (by omega) hne h).2.1) hp'
  · obtain ⟨u, hu, hx, hk⟩ := clPf_exists_of_sum hZ
    by_cases hup : u = p
    · subst hup
      exact hK.2 u p' hu hp' hne hk
    by_cases hup' : u = p'
    · subst hup'
      exact hX.2 p u hp hp' hne hx
    have x := hX.2 p u hp hu (Ne.symm hup) hx
    have y := hK.2 u p' hu hp' hup' hk
    have hb : betaExponentOfRanks k₀ rS r t p ≤ betaExponentOfRanks k₀ rS r t p' := le_trans x.2.1 y.2.1
    refine ⟨x.1, hb, ?_⟩
    rintro ⟨h1, h2⟩
    subst h1
    have hu0 : u ≠ k₀ + rS := fun h => x.2.2 ⟨h, h2⟩
    exact y.2.2 ⟨rfl, clPf_beta_eps hr h2 x.2.1 y.2.1 hu0⟩

private theorem ob2Beta_consecutive_no_between (hr : k₀ + rS < r) {p u : ℕ} (hp1 : p + 1 < r)
    (hcons : symIdx k₀ rS (p + 1) = symIdx k₀ rS p + 1 ∨ p + 1 = k₀ + rS)
    (h1 : betaExponentOfRanks k₀ rS r t p ≤ betaExponentOfRanks k₀ rS r t u) (h3 : ¬ (p + 1 = k₀ + rS ∧ u < k₀))
    (h2 : betaExponentOfRanks k₀ rS r t u ≤ betaExponentOfRanks k₀ rS r t (p + 1)) (hu1 : u ≠ p) (hu2 : u ≠ p + 1) : False := by
  have h0 := Nat.zero_le ((u - r) / t)
  have h0' := Nat.zero_le ((p - r) / t)
  have h0'' := Nat.zero_le ((p + 1 - r) / t)
  unfold betaExponentOfRanks at h1 h2
  rcases hcons with hc | hc
  · unfold symIdx at h1 h2 hc
    split_ifs at h1 h2 hc <;> omega
  · unfold symIdx at h1 h2
    split_ifs at h1 h2 <;> omega

theorem clPf_consec_mulL (hr : k₀ + rS < r) {N A : ℕ} (hrA : r ≤ A) (hAN : A ≤ N) {G X : ℕ → ℕ → k}
    (hG : clPfPat k₀ rS r t N N G) (hX : clPfPat k₀ rS r t N A X) {p : ℕ} (hp1 : p + 1 < r)
    (hcons : symIdx k₀ rS (p + 1) = symIdx k₀ rS p + 1 ∨ p + 1 = k₀ + rS) :
    clPfMul N G X p (p + 1) = G p (p + 1) + X p (p + 1) := by
  unfold clPfPat at hG hX
  unfold clPfMul
  have hpN : p < N := by omega
  have hp1N : p + 1 < N := by omega
  rw [Finset.sum_eq_add_of_mem p (p + 1) (Finset.mem_range.mpr hpN) (Finset.mem_range.mpr hp1N) (by omega)]
  · rw [hG.1 p (by omega), hX.1 (p + 1) hp1]
    ring
  · intro u hu hne
    rw [Finset.mem_range] at hu
    by_contra h0
    have h0' : G p u * X u (p + 1) ≠ 0 := h0
    have a1 := hG.2 p u hpN hu (Ne.symm hne.1) (left_ne_zero_of_mul h0')
    have a2 := hX.2 u (p + 1) hu (by omega) hne.2 (right_ne_zero_of_mul h0')
    exact ob2Beta_consecutive_no_between hr hp1 hcons a1.2.1 a2.2.2 a2.2.1 hne.1 hne.2

theorem clPf_consec_mulR (hr : k₀ + rS < r) {N A : ℕ} (hrA : r ≤ A) (hAN : A ≤ N) {X K : ℕ → ℕ → k}
    (hX : clPfPat k₀ rS r t N A X) (hK : clPfPat k₀ rS r t A A K) {p : ℕ} (hp1 : p + 1 < r)
    (hcons : symIdx k₀ rS (p + 1) = symIdx k₀ rS p + 1 ∨ p + 1 = k₀ + rS) :
    clPfMul A X K p (p + 1) = X p (p + 1) + K p (p + 1) := by
  unfold clPfPat at hX hK
  unfold clPfMul
  have hpA : p < A := by omega
  have hp1A : p + 1 < A := by omega
  rw [Finset.sum_eq_add_of_mem p (p + 1) (Finset.mem_range.mpr hpA) (Finset.mem_range.mpr hp1A) (by omega)]
  · rw [hX.1 p (by omega), hK.1 (p + 1) hp1]
    ring
  · intro u hu hne
    rw [Finset.mem_range] at hu
    by_contra h0
    have h0' : X p u * K u (p + 1) ≠ 0 := h0
    have a1 := hX.2 p u (by omega) hu (Ne.symm hne.1) (left_ne_zero_of_mul h0')
    have a2 := hK.2 u (p + 1) hu hp1A hne.2 (right_ne_zero_of_mul h0')
    exact ob2Beta_consecutive_no_between hr hp1 hcons a1.2.1 a2.2.2 a2.2.1 hne.1 hne.2

def clPfS (k₀ r : ℕ) (X : ℕ → ℕ → k) : k :=
  ∑ i ∈ Finset.range (k₀ - 1), X i (i + 1) + ∑ i ∈ Finset.range (r - k₀ - 1), X (k₀ + i) (k₀ + i + 1)

theorem clPf_cons_eps {i : ℕ} (hi : i + 1 < k₀) : symIdx k₀ rS (i + 1) = symIdx k₀ rS i + 1 ∨ i + 1 = k₀ + rS := by
  left
  unfold symIdx
  split_ifs <;> omega

theorem clPf_cons_k {i : ℕ} : symIdx k₀ rS (k₀ + i + 1) = symIdx k₀ rS (k₀ + i) + 1 ∨ k₀ + i + 1 = k₀ + rS := by
  by_cases h : k₀ + i + 1 = k₀ + rS
  · right
    exact h
  · left
    unfold symIdx
    split_ifs <;> omega

theorem clPf_S_mulL (hr : k₀ + rS < r) {N A : ℕ} (hrA : r ≤ A) (hAN : A ≤ N) {G X : ℕ → ℕ → k}
    (hG : clPfPat k₀ rS r t N N G) (hX : clPfPat k₀ rS r t N A X) :
    clPfS k₀ r (clPfMul N G X) = clPfS k₀ r G + clPfS k₀ r X := by
  unfold clPfS
  have e1 : ∑ i ∈ Finset.range (k₀ - 1), clPfMul N G X i (i + 1) =
      ∑ i ∈ Finset.range (k₀ - 1), (G i (i + 1) + X i (i + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    exact clPf_consec_mulL hr hrA hAN hG hX (by omega) (clPf_cons_eps (by omega))
  have e2 : ∑ i ∈ Finset.range (r - k₀ - 1), clPfMul N G X (k₀ + i) (k₀ + i + 1) =
      ∑ i ∈ Finset.range (r - k₀ - 1), (G (k₀ + i) (k₀ + i + 1) + X (k₀ + i) (k₀ + i + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    exact clPf_consec_mulL hr hrA hAN hG hX (by omega) clPf_cons_k
  rw [e1, e2, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

theorem clPf_S_mulR (hr : k₀ + rS < r) {N A : ℕ} (hrA : r ≤ A) (hAN : A ≤ N) {X K : ℕ → ℕ → k}
    (hX : clPfPat k₀ rS r t N A X) (hK : clPfPat k₀ rS r t A A K) :
    clPfS k₀ r (clPfMul A X K) = clPfS k₀ r X + clPfS k₀ r K := by
  unfold clPfS
  have e1 : ∑ i ∈ Finset.range (k₀ - 1), clPfMul A X K i (i + 1) =
      ∑ i ∈ Finset.range (k₀ - 1), (X i (i + 1) + K i (i + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    exact clPf_consec_mulR hr hrA hAN hX hK (by omega) (clPf_cons_eps (by omega))
  have e2 : ∑ i ∈ Finset.range (r - k₀ - 1), clPfMul A X K (k₀ + i) (k₀ + i + 1) =
      ∑ i ∈ Finset.range (r - k₀ - 1), (X (k₀ + i) (k₀ + i + 1) + K (k₀ + i) (k₀ + i + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    exact clPf_consec_mulR hr hrA hAN hX hK (by omega) clPf_cons_k
  rw [e1, e2, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

def diagonalBlockMatrix (r t i : ℕ) (X : ℕ → ℕ → k) : Matrix (Fin t) (Fin t) k := Matrix.of fun s s' => X (r + i * t + s.1) (r + i * t + s'.1)

theorem clPf_sum_blk {M : Type} [AddCommMonoid M] (b t : ℕ) (f : ℕ → M) :
    ∑ v : Fin t, f (b + v.1) = ∑ u ∈ Finset.Ico b (b + t), f u := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  exact Fin.sum_univ_eq_sum_range (fun v => f (b + v)) t

private theorem ob2Beta_block_eq (ht : 0 < t) {i s : ℕ} (hs : s < t) :
    betaExponentOfRanks k₀ rS r t (r + i * t + s) = r + i := by
  unfold betaExponentOfRanks
  rw [if_neg (show ¬ (r + i * t + s < r) by omega),
    show r + i * t + s - r = s + t * i by rw [Nat.mul_comm]; omega,
    Nat.add_mul_div_left s i ht, Nat.div_eq_of_lt hs, Nat.zero_add]

theorem clPf_blk_mulL (hr : k₀ + rS < r) (ht : 0 < t) {N A : ℕ} (hAN : A ≤ N) {G X : ℕ → ℕ → k}
    (hG : clPfPat k₀ rS r t N N G) (hX : clPfPat k₀ rS r t N A X) {i : ℕ} (hi : r + i * t + t ≤ A) :
    diagonalBlockMatrix r t i (clPfMul N G X) = diagonalBlockMatrix r t i G * diagonalBlockMatrix r t i X := by
  unfold clPfPat at hG hX
  ext s s'
  simp only [diagonalBlockMatrix, clPfMul, Matrix.of_apply, Matrix.mul_apply]
  rw [clPf_sum_blk (r + i * t) t (fun u => G (r + i * t + s) u * X u (r + i * t + s'))]
  symm
  apply Finset.sum_subset
  · intro u hu
    rw [Finset.mem_Ico] at hu
    rw [Finset.mem_range]
    omega
  · intro u hu hnot
    rw [Finset.mem_range] at hu
    by_contra h0
    have h0' : G (r + i * t + s) u * X u (r + i * t + s') ≠ 0 := h0
    have hs := s.2
    have hs' := s'.2
    have hu' : u ≠ r + i * t + s' := fun h => hnot (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    have hus : r + i * t + s ≠ u := fun h => hnot (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    have g := hG.2 (r + i * t + s) u (by omega) hu hus (left_ne_zero_of_mul h0')
    have x := hX.2 u (r + i * t + s') hu (by omega) hu' (right_ne_zero_of_mul h0')
    have e1 : betaExponentOfRanks k₀ rS r t (r + i * t + s) = r + i := ob2Beta_block_eq ht s.2
    have e2 : betaExponentOfRanks k₀ rS r t (r + i * t + s') = r + i := ob2Beta_block_eq ht s'.2
    have g1 := g.2.1
    have x1 := x.2.1
    rw [e1] at g1
    rw [e2] at x1
    have hb := clPf_beta_blk hr ht (le_antisymm x1 g1)
    exact hnot (Finset.mem_Ico.mpr hb)

theorem clPf_blk_mulR (hr : k₀ + rS < r) (ht : 0 < t) {N A : ℕ} (hAN : A ≤ N) {X K : ℕ → ℕ → k}
    (hX : clPfPat k₀ rS r t N A X) (hK : clPfPat k₀ rS r t A A K) {i : ℕ} (hi : r + i * t + t ≤ A) :
    diagonalBlockMatrix r t i (clPfMul A X K) = diagonalBlockMatrix r t i X * diagonalBlockMatrix r t i K := by
  unfold clPfPat at hX hK
  ext s s'
  simp only [diagonalBlockMatrix, clPfMul, Matrix.of_apply, Matrix.mul_apply]
  rw [clPf_sum_blk (r + i * t) t (fun u => X (r + i * t + s) u * K u (r + i * t + s'))]
  symm
  apply Finset.sum_subset
  · intro u hu
    rw [Finset.mem_Ico] at hu
    rw [Finset.mem_range]
    omega
  · intro u hu hnot
    rw [Finset.mem_range] at hu
    by_contra h0
    have h0' : X (r + i * t + s) u * K u (r + i * t + s') ≠ 0 := h0
    have hs := s.2
    have hs' := s'.2
    have hu' : u ≠ r + i * t + s' := fun h => hnot (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    have hus : r + i * t + s ≠ u := fun h => hnot (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    have g := hX.2 (r + i * t + s) u (by omega) hu hus (left_ne_zero_of_mul h0')
    have x := hK.2 u (r + i * t + s') hu (by omega) hu' (right_ne_zero_of_mul h0')
    have e1 : betaExponentOfRanks k₀ rS r t (r + i * t + s) = r + i := ob2Beta_block_eq ht s.2
    have e2 : betaExponentOfRanks k₀ rS r t (r + i * t + s') = r + i := ob2Beta_block_eq ht s'.2
    have g1 := g.2.1
    have x1 := x.2.1
    rw [e1] at g1
    rw [e2] at x1
    have hb := clPf_beta_blk hr ht (le_antisymm x1 g1)
    exact hnot (Finset.mem_Ico.mpr hb)

theorem clPf_top_mulL {N A : ℕ} (hAN : A ≤ N) {G X : ℕ → ℕ → k} (hX : clPfPat k₀ rS r t N A X) {p p' : ℕ} (hp' : p' < A) :
    clPfMul N G X p p' = clPfMul A G X p p' := by
  unfold clPfPat at hX
  unfold clPfMul
  symm
  apply Finset.sum_subset
  · intro u hu
    rw [Finset.mem_range] at hu ⊢
    omega
  · intro u hu hnot
    rw [Finset.mem_range] at hu hnot
    by_contra h0
    have h0' : G p u * X u p' ≠ 0 := h0
    have h1 := (hX.2 u p' hu hp' (by omega) (right_ne_zero_of_mul h0')).1
    omega

def clPfTop (A : ℕ) (X : ℕ → ℕ → k) : Matrix (Fin A) (Fin A) k := Matrix.of fun s s' => X s.1 s'.1

theorem clPf_top_mul (A : ℕ) (X Y : ℕ → ℕ → k) : clPfTop A (clPfMul A X Y) = clPfTop A X * clPfTop A Y := by
  ext s s'
  simp only [clPfTop, clPfMul, Matrix.of_apply, Matrix.mul_apply]
  exact (Fin.sum_univ_eq_sum_range (fun u => X s u * Y u s') A).symm

theorem clPf_det_split (hr : k₀ + rS < r) (ht : 0 < t) {A J : ℕ} (hA : A = r + J * t) {G : ℕ → ℕ → k}
    (hG : clPfPat k₀ rS r t (A + t) (A + t) G) :
    (clPfTop (A + t) G).det = (clPfTop A G).det * (diagonalBlockMatrix r t J G).det := by
  subst hA
  unfold clPfPat at hG
  have hz : ∀ (a : Fin t) (b : Fin (r + J * t)), G (r + J * t + ↑a) ↑b = 0 := by
    intro a b
    by_contra h0
    have ha := a.2
    have hb := b.2
    have g := (hG.2 (r + J * t + a) b (by omega) (by omega) (by omega) h0).2.1
    have h1 : betaExponentOfRanks k₀ rS r t b < r + J := clPf_beta_lt_blk hr ht hb
    have h2 : betaExponentOfRanks k₀ rS r t (r + J * t + a) = r + J := ob2Beta_block_eq ht a.2
    omega
  have key : (clPfTop (r + J * t + t) G).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (clPfTop (r + J * t) G) (Matrix.of fun (i : Fin (r + J * t)) (j : Fin t) => G i (r + J * t + j)) 0 (diagonalBlockMatrix r t J G) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [clPfTop, diagonalBlockMatrix, hz]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv (clPfTop (r + J * t + t) G), key,
    Matrix.det_fromBlocks_zero₂₁]

def clPfUV {K : Type} [Field K] (χ : kˣ →* Kˣ) (a : k) : K := by
  classical
  exact if h : IsUnit a then ((χ h.unit : Kˣ) : K) else 0

theorem clPfUV_mul {K : Type} [Field K] (χ : kˣ →* Kˣ) (a b : k) : clPfUV χ (a * b) = clPfUV χ a * clPfUV χ b := by
  unfold clPfUV
  by_cases ha : IsUnit a
  · by_cases hb : IsUnit b
    · have hab : IsUnit (a * b) := ha.mul hb
      rw [dif_pos hab, dif_pos ha, dif_pos hb]
      have e : hab.unit = ha.unit * hb.unit := Units.ext (by simp)
      rw [e, map_mul, Units.val_mul]
    · have hab : ¬ IsUnit (a * b) := fun h => hb (IsUnit.mul_iff.mp h).2
      rw [dif_neg hab, dif_neg hb, mul_zero]
  · have hab : ¬ IsUnit (a * b) := fun h => ha (IsUnit.mul_iff.mp h).1
    rw [dif_neg hab, dif_neg ha, zero_mul]

theorem clPfUV_ne {K : Type} [Field K] (χ : kˣ →* Kˣ) {a : k} (h : IsUnit a) : clPfUV χ a ≠ 0 := by
  unfold clPfUV
  rw [dif_pos h]
  exact Units.ne_zero _

def clPfLam {K : Type} [Field K] (ψ₀ : AddChar k K) (χ : ℕ → kˣ →* Kˣ) (k₀ r t J : ℕ) (X : ℕ → ℕ → k) : K :=
  ψ₀ (clPfS k₀ r X) * ∏ i ∈ Finset.range J, clPfUV (χ i) (diagonalBlockMatrix r t i X).det

theorem clPf_alg {K : Type} [Field K] (a b c pg px pc tg tx tc u : K) (hu : u ≠ 0) :
    a * b * c * (pg * px * pc) * (tg * tx * tc)⁻¹ = a * (pg * u) * (tg * u)⁻¹ * (c * pc * tc⁻¹) * (b * px * tx⁻¹) := by
  linear_combination (-(a * b * c * pg * px * pc * tg⁻¹ * tx⁻¹ * tc⁻¹)) * (mul_inv_cancel₀ hu)

theorem clPf_core (hr : k₀ + rS < r) (ht : 0 < t) {A J : ℕ} (hA : A = r + J * t) {K : Type} [Field K] (ψ₀ : AddChar k K)
    (χ : ℕ → kˣ →* Kˣ) {G X C : ℕ → ℕ → k} (hG : clPfPat k₀ rS r t (A + t) (A + t) G) (hX : clPfPat k₀ rS r t (A + t) A X)
    (hC : clPfPat k₀ rS r t A A C) (hGu : IsUnit (clPfTop (A + t) G).det) :
    clPfPat k₀ rS r t (A + t) A (clPfMul A (clPfMul (A + t) G X) C) ∧
      clPfLam ψ₀ χ k₀ r t J (clPfMul A (clPfMul (A + t) G X) C) * (clPfUV (χ J) (clPfTop A (clPfMul A (clPfMul (A + t) G X) C)).det)⁻¹ =
        clPfLam ψ₀ χ k₀ r t (J + 1) G * (clPfUV (χ J) (clPfTop (A + t) G).det)⁻¹ *
          (clPfLam ψ₀ χ k₀ r t J C * (clPfUV (χ J) (clPfTop A C).det)⁻¹) *
            (clPfLam ψ₀ χ k₀ r t J X * (clPfUV (χ J) (clPfTop A X).det)⁻¹) := by
  have hrA : r ≤ A := by rw [hA]; exact Nat.le_add_right _ _
  have hAN : A ≤ A + t := Nat.le_add_right _ _
  have hGX := clPf_pat_mulL hr ht hA hAN hG hX
  refine ⟨clPf_pat_mulR hr hrA hAN hGX hC, ?_⟩
  have hS : clPfS k₀ r (clPfMul A (clPfMul (A + t) G X) C) = clPfS k₀ r G + clPfS k₀ r X + clPfS k₀ r C := by
    rw [clPf_S_mulR hr hrA hAN hGX hC, clPf_S_mulL hr hrA hAN hG hX]
  have hB : ∀ i ∈ Finset.range J, clPfUV (χ i) (diagonalBlockMatrix r t i (clPfMul A (clPfMul (A + t) G X) C)).det =
      clPfUV (χ i) (diagonalBlockMatrix r t i G).det * clPfUV (χ i) (diagonalBlockMatrix r t i X).det * clPfUV (χ i) (diagonalBlockMatrix r t i C).det := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hit : r + i * t + t ≤ A := by
      rw [hA]
      have : (i + 1) * t ≤ J * t := Nat.mul_le_mul_right t hi'
      rw [Nat.add_mul, one_mul] at this
      omega
    rw [clPf_blk_mulR hr ht hAN hGX hC hit, clPf_blk_mulL hr ht hAN hG hX hit, Matrix.det_mul, Matrix.det_mul, clPfUV_mul,
      clPfUV_mul]
  have hT : clPfTop A (clPfMul A (clPfMul (A + t) G X) C) = clPfTop A G * clPfTop A X * clPfTop A C := by
    rw [clPf_top_mul]
    congr 1
    have : clPfTop A (clPfMul (A + t) G X) = clPfTop A (clPfMul A G X) := by
      ext s s'
      exact clPf_top_mulL hAN hX s'.2
    rw [this, clPf_top_mul]
  have hD := clPf_det_split hr ht hA hG
  have hBu : IsUnit (diagonalBlockMatrix r t J G).det := by
    rw [hD] at hGu
    exact isUnit_of_mul_isUnit_right hGu
  have hBn := clPfUV_ne (χ J) hBu
  have e1 : clPfLam ψ₀ χ k₀ r t J (clPfMul A (clPfMul (A + t) G X) C) =
      ψ₀ (clPfS k₀ r G) * ψ₀ (clPfS k₀ r X) * ψ₀ (clPfS k₀ r C) *
        ((∏ i ∈ Finset.range J, clPfUV (χ i) (diagonalBlockMatrix r t i G).det) * (∏ i ∈ Finset.range J, clPfUV (χ i) (diagonalBlockMatrix r t i X).det) *
          ∏ i ∈ Finset.range J, clPfUV (χ i) (diagonalBlockMatrix r t i C).det) := by
    unfold clPfLam
    rw [hS, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, Finset.prod_congr rfl hB, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have e2 : clPfUV (χ J) (clPfTop A (clPfMul A (clPfMul (A + t) G X) C)).det =
      clPfUV (χ J) (clPfTop A G).det * clPfUV (χ J) (clPfTop A X).det * clPfUV (χ J) (clPfTop A C).det := by
    rw [hT, Matrix.det_mul, Matrix.det_mul, clPfUV_mul, clPfUV_mul]
  have e3 : clPfLam ψ₀ χ k₀ r t (J + 1) G =
      ψ₀ (clPfS k₀ r G) * ((∏ i ∈ Finset.range J, clPfUV (χ i) (diagonalBlockMatrix r t i G).det) * clPfUV (χ J) (diagonalBlockMatrix r t J G).det) := by
    unfold clPfLam
    rw [Finset.prod_range_succ]
  have e4 : clPfUV (χ J) (clPfTop (A + t) G).det = clPfUV (χ J) (clPfTop A G).det * clPfUV (χ J) (diagonalBlockMatrix r t J G).det := by
    rw [hD, clPfUV_mul]
  rw [e1, e2, e3, e4]
  unfold clPfLam
  exact clPf_alg _ _ _ _ _ _ _ _ _ _ hBn

end ClPfCore

end Formalism.L2.Col
