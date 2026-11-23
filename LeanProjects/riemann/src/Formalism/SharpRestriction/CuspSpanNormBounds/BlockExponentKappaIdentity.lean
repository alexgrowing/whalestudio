import Formalism.SharpRestriction.CuspSpanNormBounds.RatioInvLeFrameFactor

open MeasureTheory Matrix Finset

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

section Weight

variable {k r : ℕ} {κ τ : ℝ}

def Wbig (k r : ℕ) (κ τ : ℝ) : ℝ := ∏ a : Fin (r + 1), tF r κ τ a ^ (4 * (2 * (r - a.val) + k - 1))

def frameBlockSum (g : ℕ → ℕ → ℕ) : ℕ → List (ℂ × ℕ) → ℕ
  | _, [] => 0
  | acc, (_, s) :: bs => g acc s + frameBlockSum g (acc + s) bs

def frGN (k r acc s : ℕ) : ℕ := 2 * s * (Ml k r (acc + s) + s - 3)

def frGE (r acc s : ℕ) : ℕ := 2 * (r + 1 - (acc + s)) + (s - 1)

def frTri (d : ℕ) : ℕ := ∑ j ∈ range d, (d - j)

theorem ptWeightFrom_scale (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    ptWeightFrom k r (τ ^ 2 * T) (τ ^ 2 * T') acc (scaleBlocks κ τ r acc bs) =
      τ ^ frameBlockSum (fun a s => 2 * frGN k r a s) acc bs *
        κ ^ frameBlockSum (fun a s => frGE r a s * frGN k r a s) acc bs * ptWeightFrom k r T T' acc bs := by
  induction bs generalizing acc with
  | nil => simp [ptWeightFrom, scaleBlocks, frameBlockSum]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [scaleBlocks, ptWeightFrom, frameBlockSum]
    rw [ih (acc + s)]
    by_cases h : s = 1 ∧ acc + 1 = r + 1
    · rw [if_pos h, if_pos h]
      obtain ⟨rfl, h2⟩ := h
      have e1 : 2 * (r + 1 - (acc + 1)) + (1 - 1) = 0 := by omega
      have e2 : frGE r acc 1 = 0 := by unfold frGE; omega
      have e3 : 2 * frGN k r acc 1 = 4 * (k - 1) := by unfold frGN Ml; omega
      have hbase : Complex.normSq (((τ ^ 2 * κ ^ 0 : ℝ) : ℂ) * t) - τ ^ 2 * T * (τ ^ 2 * T') =
          τ ^ 4 * (Complex.normSq t - T * T') := by
        rw [Complex.normSq_mul, Complex.normSq_ofReal]; ring
      rw [e1, hbase, e2, e3, mul_pow]
      ring
    · rw [if_neg h, if_neg h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      unfold frGE frGN
      ring

theorem sum_pos_blocks (f : ℕ → ℕ → ℕ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    ∑ p ∈ range (bs.map Prod.snd).sum, f (acc + p) (p - frStart bs p) =
      frameBlockSum (fun a s => ∑ i ∈ range s, f (a + i) i) acc bs := by
  induction bs generalizing acc with
  | nil => simp [frameBlockSum]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_range_add, frameBlockSum, ← ih (acc + s)]
    congr 1
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p < s := Finset.mem_range.mp hp
      simp only [frStart, if_pos hp', Nat.sub_zero]
    · refine Finset.sum_congr rfl fun p _ => ?_
      simp only [frStart]
      rw [if_neg (show ¬ (s + p < s) by omega), show s + p - s = p by omega,
        show acc + (s + p) = acc + s + p by omega,
        show s + p - (s + frStart bs p) = p - frStart bs p by omega]

theorem sum_rootPat_diff (γ : Point ℂ (r + 1)) :
    ∑ p ∈ rootPat γ, (p.2.val - p.1.val) = frameBlockSum (fun a s => ∑ i ∈ range s, frTri i) 0 γ.1 := by
  have h1 := sum_rootPat (fun a b => b - a) γ
  have h2 := sum_pos_blocks (fun _ d => frTri d) 0 γ.1
  rw [γ.2.2] at h2
  rw [h1, ← h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_Ico_eq_sum_range]
  unfold frTri
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.mp hj
  have := frStart_le γ.1 b
  omega

theorem Wbig_eq : Wbig k r κ τ = τ ^ (∑ a ∈ range (r + 1), 4 * (2 * (r - a) + k - 1)) *
    κ ^ (∑ a ∈ range (r + 1), (r - a) * (4 * (2 * (r - a) + k - 1))) := by
  unfold Wbig
  rw [Fin.prod_univ_eq_prod_range (fun a => tF r κ τ a ^ (4 * (2 * (r - a) + k - 1)))]
  simp_rw [tF, mul_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

theorem alphaPt_sq_mul (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) :
    alphaPt κ τ γ ^ 2 * κ ^ (4 * ∑ p ∈ rootPat γ, (p.2.val - p.1.val)) = κ ^ (2 * (rootPat γ).card) := by
  have h1 : ∀ p ∈ rootPat γ,
      (tF r κ τ p.2.val / tF r κ τ p.1.val) ^ 2 * κ ^ (2 * (p.2.val - p.1.val)) = 1 := by
    intro p hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2.1
    have hlt' : p.1.val < p.2.val := hlt
    have hle : p.2.val ≤ r := Nat.lt_succ_iff.mp p.2.isLt
    have e : tF r κ τ p.1.val = tF r κ τ p.2.val * κ ^ (p.2.val - p.1.val) := by
      unfold tF; rw [mul_assoc, ← pow_add]; congr 2; omega
    have h2 := tF_pos (r := r) hκ hτ p.2.val
    have h3 : 0 < κ ^ (p.2.val - p.1.val) := pow_pos hκ _
    have h4 : tF r κ τ p.2.val / (tF r κ τ p.2.val * κ ^ (p.2.val - p.1.val)) * κ ^ (p.2.val - p.1.val) = 1 := by
      field_simp
    rw [e, pow_mul', ← mul_pow, h4, one_pow]
  set P := ∏ p ∈ rootPat γ, (tF r κ τ p.2.val / tF r κ τ p.1.val) ^ 2 with hP
  set S := ∑ p ∈ rootPat γ, (p.2.val - p.1.val) with hS
  have hPS : P * κ ^ (2 * S) = 1 := by
    rw [hS, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, hP, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one h1
  unfold alphaPt
  rw [← hP, show (κ ^ (rootPat γ).card * P) ^ 2 * κ ^ (4 * S) =
    κ ^ (2 * (rootPat γ).card) * (P * κ ^ (2 * S)) ^ 2 by ring, hPS]
  ring

theorem frTri_succ (d : ℕ) : frTri (d + 1) = frTri d + (d + 1) := by
  unfold frTri
  rw [Finset.sum_range_succ']
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by omega

theorem two_mul_frTri (d : ℕ) : 2 * frTri d = d * (d + 1) := by
  induction d with
  | zero => simp [frTri]
  | succ n ih => rw [frTri_succ, mul_add, ih]; ring

theorem block_exponent_tau_identity (m k' s' : ℕ) :
    2 * (2 * (s' + 1) * (2 * m + k' + s')) = ∑ i ∈ range (s' + 1), 4 * (2 * (m + i) + k') := by
  induction s' with
  | zero => simp only [zero_add, add_zero, Finset.sum_range_one]; ring
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; ring

theorem block_exponent_kappa_identity (m k' s' : ℕ) :
    (2 * m + s') * (2 * (s' + 1) * (2 * m + k' + s')) + 4 * ∑ i ∈ range (s' + 1), frTri i =
      ∑ i ∈ range (s' + 1), (m + i) * (4 * (2 * (m + i) + k')) := by
  induction s' with
  | zero =>
    simp only [zero_add, add_zero, Finset.sum_range_one, frTri, Finset.range_zero, Finset.sum_empty, mul_zero]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ frTri (n + 1),
      Finset.sum_range_succ (fun i => (m + i) * (4 * (2 * (m + i) + k'))) (n + 1), ← ih]
    have h := two_mul_frTri (n + 1)
    nlinarith [h]

theorem blk_tau (hk : 1 ≤ k) (a s : ℕ) (h : a + s ≤ r + 1) :
    2 * frGN k r a s = ∑ i ∈ range s, 4 * (2 * (r - (a + i)) + k - 1) := by
  rcases s with _ | s'
  · simp [frGN]
  obtain ⟨m, hm⟩ : ∃ m, m = r + 1 - (a + (s' + 1)) := ⟨_, rfl⟩
  have hN : frGN k r a (s' + 1) = 2 * (s' + 1) * (2 * m + (k - 1) + s') := by
    unfold frGN Ml; congr 1; omega
  rw [hN, block_exponent_tau_identity m (k - 1) s',
    ← Finset.sum_range_reflect (fun i => 4 * (2 * (r - (a + i)) + k - 1)) (s' + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  try dsimp only
  omega

theorem blk_kappa (hk : 1 ≤ k) (a s : ℕ) (h : a + s ≤ r + 1) :
    frGE r a s * frGN k r a s + 4 * ∑ i ∈ range s, frTri i =
      ∑ i ∈ range s, (r - (a + i)) * (4 * (2 * (r - (a + i)) + k - 1)) := by
  rcases s with _ | s'
  · simp [frGN]
  obtain ⟨m, hm⟩ : ∃ m, m = r + 1 - (a + (s' + 1)) := ⟨_, rfl⟩
  have hN : frGN k r a (s' + 1) = 2 * (s' + 1) * (2 * m + (k - 1) + s') := by
    unfold frGN Ml; congr 1; omega
  have hE : frGE r a (s' + 1) = 2 * m + s' := by unfold frGE; omega
  rw [hN, hE, block_exponent_kappa_identity m (k - 1) s',
    ← Finset.sum_range_reflect (fun i => (r - (a + i)) * (4 * (2 * (r - (a + i)) + k - 1))) (s' + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  try dsimp only
  have e1 : r - (a + (s' + 1 - 1 - i)) = m + i := by omega
  have e2 : 2 * (m + i) + k - 1 = 2 * (m + i) + (k - 1) := by omega
  rw [e1, e2]

theorem frame_block_sum_congr {g₁ g₂ : ℕ → ℕ → ℕ} {R : ℕ} (h : ∀ a s, a + s ≤ R → g₁ a s = g₂ a s) (acc : ℕ)
    (bs : List (ℂ × ℕ)) (hb : acc + (bs.map Prod.snd).sum ≤ R) : frameBlockSum g₁ acc bs = frameBlockSum g₂ acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at hb
    simp only [frameBlockSum]
    rw [h acc s (by omega), ih (acc + s) (by omega)]

theorem frame_block_sum_add (g₁ g₂ : ℕ → ℕ → ℕ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    frameBlockSum (fun a s => g₁ a s + g₂ a s) acc bs = frameBlockSum g₁ acc bs + frameBlockSum g₂ acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [frameBlockSum]
    rw [ih (acc + s)]; ring

theorem frame_block_sum_mul (c : ℕ) (g : ℕ → ℕ → ℕ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    frameBlockSum (fun a s => c * g a s) acc bs = c * frameBlockSum g acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [frameBlockSum]
    rw [ih (acc + s)]; ring

theorem ptWeight_ptTr (hk : 1 ≤ k) (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (γ : Point ℂ (r + 1)) :
    ptWeight k r (τ ^ 2 * T) (τ ^ 2 * T') (ptTr κ τ hκ hτ γ) * κ ^ (2 * (rootPat γ).card) =
      Wbig k r κ τ * alphaPt κ τ γ ^ 2 * ptWeight k r T T' γ := by
  have hsum : 0 + (γ.1.map Prod.snd).sum ≤ r + 1 := by rw [γ.2.2]; omega
  have hU := sum_pos_blocks (fun p _ => 4 * (2 * (r - p) + k - 1)) 0 γ.1
  have hV := sum_pos_blocks (fun p _ => (r - p) * (4 * (2 * (r - p) + k - 1))) 0 γ.1
  rw [γ.2.2] at hU hV
  simp only [zero_add] at hU hV
  have hA : frameBlockSum (fun a s => 2 * frGN k r a s) 0 γ.1 = ∑ a ∈ range (r + 1), 4 * (2 * (r - a) + k - 1) := by
    rw [hU]
    refine frame_block_sum_congr ?_ 0 γ.1 hsum
    intro a s h; exact blk_tau hk a s h
  have hB : frameBlockSum (fun a s => frGE r a s * frGN k r a s) 0 γ.1 + 4 * ∑ p ∈ rootPat γ, (p.2.val - p.1.val) =
      ∑ a ∈ range (r + 1), (r - a) * (4 * (2 * (r - a) + k - 1)) := by
    rw [hV, sum_rootPat_diff, ← frame_block_sum_mul, ← frame_block_sum_add]
    refine frame_block_sum_congr ?_ 0 γ.1 hsum
    intro a s h; exact blk_kappa hk a s h
  have hα := alphaPt_sq_mul hκ hτ γ
  unfold ptWeight
  rw [ptTr_val, ptWeightFrom_scale hκ hτ, Wbig_eq, hA, ← hB, ← hα, pow_add]
  ring

end Weight

end Formalism.MainNotions.FrameBoundFromBesselTorus
