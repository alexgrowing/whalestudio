import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.FormalDegreeBessel.StatementDS
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.NqMovedExample

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

noncomputable def PStar {n : ℕ} (lam : Fin n → ℝ) (c y : ℝ) : ℝ := ∏ s, (|y + lam s| + c)

def NQ (P : M.Par) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ₀ : ℝ) : Prop :=
  ∀ y ∈ Y, nn y * nn (y + 1) ≤ Λ₀ ^ 2 * (M.qC P (y : ℂ)).re

noncomputable def lamN {n : ℕ} (lam : Fin n → ℝ) (s : ℕ) : ℝ := if h : s - 1 < n then lam ⟨s - 1, h⟩ else 0

theorem lamN_succ {n : ℕ} (lam : Fin n → ℝ) (s : Fin n) : lamN lam (s + 1) = lam s := by
  simp [lamN]

theorem Pst_lamN (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (c y : ℝ) : Pst k r (lamN lam) c y = PStar lam c y := by
  unfold Pst PStar
  symm
  refine Finset.prod_bij (fun s _ => (s : ℕ) + 1) (fun s _ => ?_) (fun s _ t _ h => ?_) (fun t ht => ?_)
    (fun s _ => ?_)
  · have := s.2
    exact mem_Icc.2 ⟨by omega, by omega⟩
  · exact Fin.ext (by omega)
  · obtain ⟨h1, h2⟩ := mem_Icc.1 ht
    exact ⟨⟨t - 1, by omega⟩, mem_univ _, by simp only; omega⟩
  · rw [lamN_succ]

theorem PStar_pos {n : ℕ} (lam : Fin n → ℝ) {c : ℝ} (hc : 0 < c) (y : ℝ) : 0 < PStar lam c y :=
  Finset.prod_pos fun _ _ => add_pos_of_nonneg_of_pos (abs_nonneg _) hc

structure HypLam (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (c g b : ℝ) : Prop where
  hc : Formalism.QuantumDeterminants.IsHCParam lam
  lam_le : ∀ s, |lam s| ≤ b
  c_ge : 1 ≤ c
  b_ge_three : 3 ≤ b
  b_ge_k : Real.exp 1 * k ≤ b
  b_ge_c : c + 2 ≤ b
  g_ge : 2 * c ≤ g
  gap : ∀ s t : Fin (2 * r + k + 1), (t : ℕ) = s + 1 → lam t + g ≤ lam s

structure HypType (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b : ℝ) : Prop where
  half : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, u i - ((k : ℝ) - 1) / 2 = m
  inter : C7.LamInterlaces k r u fun s => lam (s.cast (by ring))
  u_le : ∀ i, 1 ≤ i → i ≤ k → |u i| ≤ b

theorem half_le_of_pos {x : ℝ} (m : ℤ) (hx : x = m + 1 / 2) (h : 0 < x) : 1 / 2 ≤ x := by
  have h1 : (-1 : ℝ) < m := by linarith
  have h2 : (0 : ℤ) ≤ m := by
    have : (-1 : ℤ) < m := by exact_mod_cast h1
    omega
  have h3 : (0 : ℝ) ≤ m := by exact_mod_cast h2
  linarith

theorem inter_half {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} (hc : Formalism.QuantumDeterminants.IsHCParam lam) {u : ℕ → ℝ} {b : ℝ}
    (hu : HypType k r lam u b) (s : ℕ) (hs1 : 1 ≤ s) (hsk : s ≤ k - 1) :
    lamN lam s + 1 / 2 ≤ u s ∧ u (s + 1) ≤ lamN lam s - 1 / 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have ht : t < 2 * r + k + 1 := by omega
  have e : lamN lam (t + 1) = lam ⟨t, ht⟩ := lamN_succ lam ⟨t, ht⟩
  obtain ⟨h1, h2⟩ := hu.inter.2 ⟨t, by omega⟩
  have h1' : lam ⟨t, ht⟩ < u (t + 1) := h1 (by simp only; omega)
  have h2' : u (t + 2) < lam ⟨t, ht⟩ := h2 (by simp only; omega)
  obtain ⟨a, ha⟩ := hc.2 ⟨t, ht⟩
  obtain ⟨m1, hm1⟩ := hu.half (t + 1) (by omega) (by omega)
  obtain ⟨m2, hm2⟩ := hu.half (t + 2) (by omega) (by omega)
  push_cast at ha
  rw [e]
  have k1 := half_le_of_pos (x := u (t + 1) - lam ⟨t, ht⟩) (m1 - a - r - 1) (by push_cast; linarith) (by linarith)
  have k2 := half_le_of_pos (x := lam ⟨t, ht⟩ - u (t + 2)) (a + r - m2) (by push_cast; linarith) (by linarith)
  constructor <;> linarith

section data

variable {P : M.Par} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {c g b : ℝ}

theorem HypLam.k_le (h : HypLam P.k P.r lam c g b) : (P.k : ℝ) ≤ b := by
  have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have h2 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  nlinarith [h.b_ge_k]

theorem HypLam.lamN_le (h : HypLam P.k P.r lam c g b) :
    ∀ s, 1 ≤ s → s ≤ P.k + 2 * P.r + 1 → |lamN lam s| ≤ b := by
  intro s hs1 hs
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [show lamN lam (t + 1) = lam ⟨t, by omega⟩ from lamN_succ lam ⟨t, by omega⟩]
  exact h.lam_le _

theorem HypLam.lamN_gap (h : HypLam P.k P.r lam c g b) :
    ∀ s, 1 ≤ s → s + 1 ≤ P.k - 1 → lamN lam (s + 1) + g ≤ lamN lam s := by
  intro s hs1 hs
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [show lamN lam (t + 1) = lam ⟨t, by omega⟩ from lamN_succ lam ⟨t, by omega⟩,
    show lamN lam (t + 1 + 1) = lam ⟨t + 1, by omega⟩ from lamN_succ lam ⟨t + 1, by omega⟩]
  exact h.gap _ _ rfl

theorem lamData_of_hyp (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b)
    (hu' : HypType P.k P.r lam P.u' b) : LamData P (lamN lam) c g b where
  c_pos := by linarith [h.c_ge]
  g_ge := by linarith [h.c_ge, h.g_ge]
  b_ge_three := h.b_ge_three
  b_ge_k := h.k_le
  b_ge_c := h.b_ge_c
  lam_le := h.lamN_le
  gap := h.lamN_gap
  inter := fun s h1 h2 => ⟨inter_half h.hc hu s h1 h2, inter_half h.hc hu' s h1 h2⟩
  u_le := fun i h1 h2 => ⟨hu.u_le i h1 h2, hu'.u_le i h1 h2⟩

theorem movedData_of_hyp (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b) {l : ℕ} (hl1 : 1 ≤ l)
    (hlk : l ≤ P.k) (hmv : ∀ i, i ≠ l → P.u' i = P.u i) (hl : |P.u' l| ≤ b) : MovedData P l (lamN lam) c g b where
  c_pos := by linarith [h.c_ge]
  g_ge := by linarith [h.c_ge, h.g_ge]
  b_ge_three := h.b_ge_three
  b_ge_k := h.k_le
  b_ge_c := h.b_ge_c
  lam_le := h.lamN_le
  gap := h.lamN_gap
  inter := fun s h1 h2 => inter_half h.hc hu s h1 h2
  moved := hmv
  ul_le := ⟨hu.u_le l hl1 hlk, hl⟩

end data

noncomputable def nqΛ (P : M.Par) (b : ℝ) : ℝ := Real.sqrt (b ^ (8 * P.r + 20) / (P.T * P.T'))

theorem nq_PStar (P : M.Par) (hOK : P.OK) (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (hk : 2 ≤ P.k)
    (lam : Fin (2 * P.r + P.k + 1) → ℝ) (c g b : ℝ) (hL : PairData P l (lamN lam) c g b) (Y : Finset ℝ)
    (hY : ∀ y ∈ Y, I.OnCut P.u P.u' l y) : NQ P (PStar lam c) Y (nqΛ P b) := by
  intro y hy
  have h := (nq_onCut_pair P hOK l hl1 hlk hk (lamN lam) c g b hL y (hY y hy)).2
  rw [Pst_lamN, Pst_lamN] at h
  have hb : 0 ≤ b := by linarith [hL.b_ge_three]
  have hTT : 0 < P.T * P.T' := mul_pos hOK.T_pos hOK.T'_pos
  rw [nqΛ, Real.sq_sqrt (by positivity)]
  exact h

theorem nqΛ_le (P : M.Par) (b CT : ℝ) (hb : 1 ≤ b) (hCT : 0 ≤ CT)
    (hTT : b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T') :
    nqΛ P b ≤ b ^ ((5 + CT) * ((2 * P.r + 2 : ℕ) : ℝ)) := by
  set m : ℝ := ((2 * P.r + 2 : ℕ) : ℝ) with hm
  have hmr : m = 2 * (P.r : ℝ) + 2 := by rw [hm]; push_cast; ring
  have hb0 : (0 : ℝ) < b := by linarith
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hm0 : 0 ≤ m := by rw [hmr]; positivity
  have h2 : b ^ (8 * P.r + 20) = b ^ (8 * (P.r : ℝ) + 20) := by
    rw [← Real.rpow_natCast]; push_cast; ring_nf
  have h3 : (P.T * P.T')⁻¹ ≤ b ^ (CT * m) := by
    rw [Real.rpow_neg hb0.le] at hTT
    have hpos : 0 < (b ^ (CT * m))⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos hb0 _)
    calc (P.T * P.T')⁻¹ ≤ ((b ^ (CT * m))⁻¹)⁻¹ := inv_anti₀ hpos hTT
      _ = b ^ (CT * m) := inv_inv _
  have hX : b ^ (8 * P.r + 20) / (P.T * P.T') ≤ (b ^ ((5 + CT) * m)) ^ 2 := by
    calc b ^ (8 * P.r + 20) / (P.T * P.T') ≤ b ^ (8 * (P.r : ℝ) + 20) * b ^ (CT * m) := by
          rw [div_eq_mul_inv, h2]
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = b ^ ((8 * (P.r : ℝ) + 20) + CT * m) := by rw [Real.rpow_add hb0 (8 * (P.r : ℝ) + 20)]
      _ ≤ b ^ ((5 + CT) * m + (5 + CT) * m) := by
          apply Real.rpow_le_rpow_of_exponent_le hb
          have hCTm : 0 ≤ CT * m := mul_nonneg hCT hm0
          have e : (5 + CT) * m + (5 + CT) * m = 10 * m + 2 * (CT * m) := by ring
          rw [e]
          linarith
      _ = (b ^ ((5 + CT) * m)) ^ 2 := by rw [Real.rpow_add hb0, sq]
  exact (Real.sqrt_le_left (Real.rpow_nonneg hb0.le _)).mpr hX

theorem nq_text_moved (P : M.Par) (hOK : P.OK) (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (hk : 2 ≤ P.k)
    (lam : Fin (2 * P.r + P.k + 1) → ℝ) (c g b : ℝ) (h : HypLam P.k P.r lam c g b)
    (hu : HypType P.k P.r lam P.u b) (hmv : ∀ i, i ≠ l → P.u' i = P.u i) (hl : |P.u' l| ≤ b) (Y : Finset ℝ)
    (hY : ∀ y ∈ Y, I.OnCut P.u P.u' l y) : NQ P (PStar lam c) Y (nqΛ P b) :=
  nq_PStar P hOK l hl1 hlk hk lam c g b (movedData_of_hyp h hu hl1 hlk hmv hl).toPair Y hY

noncomputable def P₂ : M.Par where
  k := 2
  r := 0
  T := 1
  T' := 1
  u := fun i => if i = 1 then 41 / 2 else 1 / 2
  u' := fun i => if i = 1 then 81 / 2 else 1 / 2

noncomputable def lam₂ : Fin (2 * P₂.r + P₂.k + 1) → ℝ := fun s => 10 - 20 * ((s : ℕ) : ℝ)

theorem P₂_OK : P₂.OK where
  k_pos := by show 1 ≤ 2; norm_num
  T_pos := by show (0 : ℝ) < 1; norm_num
  T'_pos := by show (0 : ℝ) < 1; norm_num
  int_u := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
    have h2' : i ≤ 2 := h2
    interval_cases i
    · exact ⟨0, by simp [P₂]⟩
    · exact ⟨-20, by simp [P₂]; norm_num⟩
  int_u' := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
    have h2' : i ≤ 2 := h2
    interval_cases i
    · exact ⟨20, by simp [P₂]; norm_num⟩
    · exact ⟨-20, by simp [P₂]; norm_num⟩
  gap := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
    have h2' : i ≤ 1 := h2
    interval_cases i
    simp only [M.Par.lo, M.Par.hi, P₂]
    norm_num

theorem lam₂_anti : StrictAnti lam₂ := by
  intro s t hst
  have : ((s : ℕ) : ℝ) < ((t : ℕ) : ℝ) := by exact_mod_cast hst
  simp only [lam₂]
  linarith

theorem hypLam₂ : HypLam P₂.k P₂.r lam₂ 10 20 41 where
  hc := ⟨lam₂_anti, fun s => ⟨9 - 20 * (s : ℕ), by simp only [lam₂, P₂]; push_cast; ring⟩⟩
  lam_le := by
    intro s
    have hs : (s : ℕ) < 3 := s.2
    have h1 : ((s : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : (s : ℕ) ≤ 2)
    have h0 : (0 : ℝ) ≤ ((s : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [lam₂]
    rw [abs_le]
    constructor <;> linarith
  c_ge := by norm_num
  b_ge_three := by norm_num
  b_ge_k := by
    have := Real.exp_one_lt_d9
    show Real.exp 1 * ((2 : ℕ) : ℝ) ≤ 41
    push_cast
    linarith
  b_ge_c := by norm_num
  g_ge := by norm_num
  gap := by
    intro s t h
    simp only [lam₂, h]
    push_cast
    linarith

theorem hypType₂ (a : ℤ) (ha : 10 ≤ a) (ha' : a ≤ 40) :
    HypType P₂.k P₂.r lam₂ (fun i => if i = 1 then (a : ℝ) + 1 / 2 else 1 / 2) 41 where
  half := by
    intro i _ _
    by_cases h : i = 1
    · exact ⟨a, by simp [h, P₂]; norm_num⟩
    · exact ⟨0, by simp [h, P₂]; norm_num⟩
  inter := by
    have haR : (10 : ℝ) ≤ a := by exact_mod_cast ha
    refine ⟨fun s t hst => lam₂_anti (by simpa using hst), fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
    · have hs' : (s : ℕ) + 1 ≤ 2 := hs
      simp only [lam₂, Fin.val_cast]
      split_ifs with h
      · have : (s : ℕ) = 0 := by omega
        rw [this]; push_cast; linarith
      · have : (s : ℕ) = 1 := by omega
        rw [this]; norm_num
    · have hs' : (s : ℕ) + 2 ≤ 2 := hs
      have : (s : ℕ) = 0 := by omega
      simp only [lam₂, Fin.val_cast, this]
      norm_num
  u_le := by
    intro i _ _
    have haR : (10 : ℝ) ≤ a := by exact_mod_cast ha
    have haR' : (a : ℝ) ≤ 40 := by exact_mod_cast ha'
    rw [abs_le]
    split_ifs <;> constructor <;> linarith

theorem hypType₂_u : HypType P₂.k P₂.r lam₂ P₂.u 41 := by
  convert hypType₂ 20 (by norm_num) (by norm_num) using 1
  funext i
  simp only [P₂]
  split_ifs <;> norm_num

theorem hypType₂_u' : HypType P₂.k P₂.r lam₂ P₂.u' 41 := by
  convert hypType₂ 40 (by norm_num) (by norm_num) using 1
  funext i
  simp only [P₂]
  split_ifs <;> norm_num

end CompanionTheory.WaveGrid
