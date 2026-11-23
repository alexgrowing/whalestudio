import CompanionTheory.AutomorphicTheory.BesselWaveGrids.PStarTie
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.CfgTie

namespace CompanionTheory.WaveGrid.Inhab

open Formalism.FourierDecayAlt Finset CompanionTheory.WaveGrid GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

theorem int_of_half {k : ℕ} {u v : ℕ → ℝ} (hk : 1 ≤ k)
    (hu : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, u i - ((k : ℝ) - 1) / 2 = m)
    (hv : ∀ i, 1 ≤ i → i ≤ k → ∃ m : ℤ, v i - ((k : ℝ) - 1) / 2 = m) :
    ∀ i ∈ Icc 1 k, ∃ n : ℤ, v i - u 1 = n := by
  intro i hi
  obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
  obtain ⟨m1, hm1⟩ := hu 1 le_rfl hk
  obtain ⟨m2, hm2⟩ := hv i hi1 hik
  exact ⟨m2 - m1, by push_cast; linarith⟩

theorem ok_diff (P : M.Par) (hk : 1 ≤ P.k) (hT : 0 < P.T) (hT' : 0 < P.T') (lam : Fin (2 * P.r + P.k + 1) → ℝ)
    (b : ℝ) (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hu : HypType P.k P.r lam P.u b) (hu' : HypType P.k P.r lam P.u' b) :
    P.OK := by
  refine ⟨hk, hT, hT', int_of_half hk hu.half hu.half, int_of_half hk hu.half hu'.half, ?_⟩
  intro i hi
  obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
  obtain ⟨a1, a2⟩ := inter_half hc hu i hi1 hik
  obtain ⟨b1, b2⟩ := inter_half hc hu' i hi1 hik
  simp only [M.Par.lo, M.Par.hi]
  have hmax := max_le a2 b2
  have hmin := le_min a1 b1
  linarith

def uP (u : ℕ → ℝ) (l n₀ : ℕ) : ℕ → ℝ := fun i => if i = l + 1 then u i + n₀ else u i
def uM (u : ℕ → ℝ) (l n₀ : ℕ) : ℕ → ℝ := fun i => if i = l then u i - n₀ else u i

theorem ok_plus (k r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b : ℝ) (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hu : HypType k r lam u b) (l n₀ : ℕ) (hl1 : 1 ≤ l) (hlk : l < k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ u l - u (l + 1)) : (⟨k, r, T, T', u, uP u l n₀⟩ : M.Par).OK := by
  have hk : 1 ≤ k := by omega
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨hk, hT, hT', int_of_half hk hu.half hu.half, ?_, ?_⟩
  · intro i hi
    obtain ⟨n, hn⟩ := int_of_half hk hu.half hu.half i hi
    by_cases h : i = l + 1
    · refine ⟨n + n₀, ?_⟩
      simp only [uP, if_pos h]
      push_cast
      linarith
    · refine ⟨n, ?_⟩
      simp only [uP, if_neg h]
      exact hn
  · intro i hi
    obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
    obtain ⟨a1, a2⟩ := inter_half hc hu i hi1 hik
    simp only [M.Par.lo, M.Par.hi, uP]
    by_cases h1 : i + 1 = l + 1
    · have hil : i = l := by omega
      subst hil
      have h2 : ¬ (i = i + 1) := by omega
      rw [if_pos h1, if_neg h2, min_self, max_eq_right (by linarith)]
      linarith
    · by_cases h2 : i = l + 1
      · rw [if_neg h1, if_pos h2, max_self, min_eq_left (by linarith)]
        linarith
      · rw [if_neg h1, if_neg h2, max_self, min_self]
        linarith

theorem ok_minus (k r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b : ℝ) (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hu : HypType k r lam u b) (l n₀ : ℕ) (hl1 : 1 ≤ l) (hlk : l < k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ u l - u (l + 1)) : (⟨k, r, T, T', u, uM u l n₀⟩ : M.Par).OK := by
  have hk : 1 ≤ k := by omega
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨hk, hT, hT', int_of_half hk hu.half hu.half, ?_, ?_⟩
  · intro i hi
    obtain ⟨n, hn⟩ := int_of_half hk hu.half hu.half i hi
    by_cases h : i = l
    · refine ⟨n - n₀, ?_⟩
      simp only [uM, if_pos h]
      push_cast
      linarith
    · refine ⟨n, ?_⟩
      simp only [uM, if_neg h]
      exact hn
  · intro i hi
    obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
    obtain ⟨a1, a2⟩ := inter_half hc hu i hi1 hik
    simp only [M.Par.lo, M.Par.hi, uM]
    by_cases h2 : i = l
    · subst h2
      have h1 : ¬ (i + 1 = i) := by omega
      rw [if_neg h1, if_pos rfl, max_self, min_eq_right (by linarith)]
      linarith
    · by_cases h1 : i + 1 = l
      · rw [if_pos h1, if_neg h2, max_eq_left (by linarith), min_self]
        linarith
      · rw [if_neg h1, if_neg h2, max_self, min_self]
        linarith

theorem nq_plus (k r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (c g b : ℝ) (h : HypLam k r lam c g b) (hu : HypType k r lam u b) (l n₀ : ℕ) (hl1 : 1 ≤ l) (hlk : l < k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ u l - u (l + 1)) (Y : Finset ℝ)
    (hY : ∀ y ∈ Y, u (l + 1) + 2 ≤ -y ∧ -y ≤ u (l + 1) + n₀ - 2) :
    NQ ⟨k, r, T, T', u, uP u l n₀⟩ (PStar lam c) Y (nqΛ ⟨k, r, T, T', u, uP u l n₀⟩ b) := by
  have hk2 : 2 ≤ k := by omega
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine nq_text_moved ⟨k, r, T, T', u, uP u l n₀⟩
    (ok_plus k r T T' hT hT' lam u b h.hc hu l n₀ hl1 hlk hposition) (l + 1) (by omega)
    (show l + 1 ≤ k by omega) hk2 lam c g b h hu ?_ ?_ Y ?_
  · intro i hi
    show uP u l n₀ i = u i
    simp only [uP, if_neg hi]
  · have e1 : uP u l n₀ (l + 1) = u (l + 1) + n₀ := if_pos rfl
    show |uP u l n₀ (l + 1)| ≤ b
    rw [e1]
    have hul := hu.u_le l hl1 hlk.le
    have hul1 := hu.u_le (l + 1) (by omega) (by omega)
    rw [abs_le] at hul hul1 ⊢
    constructor <;> linarith [hul.1, hul.2, hul1.1, hul1.2]
  · intro y hy
    obtain ⟨h1, h2⟩ := hY y hy
    left
    have e1 : uP u l n₀ (l + 1) = u (l + 1) + n₀ := if_pos rfl
    show u (l + 1) + 2 ≤ -y ∧ -y ≤ uP u l n₀ (l + 1) - 2
    rw [e1]
    exact ⟨h1, by linarith⟩

theorem nq_minus (k r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (c g b : ℝ) (h : HypLam k r lam c g b) (hu : HypType k r lam u b) (l n₀ : ℕ) (hl1 : 1 ≤ l) (hlk : l < k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ u l - u (l + 1)) (Y : Finset ℝ)
    (hY : ∀ y ∈ Y, u l - n₀ + 2 ≤ -y ∧ -y ≤ u l - 2) :
    NQ ⟨k, r, T, T', u, uM u l n₀⟩ (PStar lam c) Y (nqΛ ⟨k, r, T, T', u, uM u l n₀⟩ b) := by
  have hk2 : 2 ≤ k := by omega
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine nq_text_moved ⟨k, r, T, T', u, uM u l n₀⟩
    (ok_minus k r T T' hT hT' lam u b h.hc hu l n₀ hl1 hlk hposition) l hl1
    (show l ≤ k by omega) hk2 lam c g b h hu ?_ ?_ Y ?_
  · intro i hi
    show uM u l n₀ i = u i
    simp only [uM, if_neg hi]
  · have e1 : uM u l n₀ l = u l - n₀ := if_pos rfl
    show |uM u l n₀ l| ≤ b
    rw [e1]
    have hul := hu.u_le l hl1 hlk.le
    have hul1 := hu.u_le (l + 1) (by omega) (by omega)
    rw [abs_le] at hul hul1 ⊢
    constructor <;> linarith [hul.1, hul.2, hul1.1, hul1.2]
  · intro y hy
    obtain ⟨h1, h2⟩ := hY y hy
    right
    have e1 : uM u l n₀ l = u l - n₀ := if_pos rfl
    show uM u l n₀ l + 2 ≤ -y ∧ -y ≤ u l - 2
    rw [e1]
    exact ⟨by linarith, h2⟩

noncomputable def lamX (x : ℤ) : Fin (2 * 0 + 3 + 1) → ℝ := ![(x : ℝ) + 1 / 2, -79 / 2, -119 / 2, -159 / 2]
noncomputable def uX : ℕ → ℝ := fun i => if i = 1 then 80 else if i = 2 then 0 else -50

theorem lamX_anti (x : ℤ) (hx : 0 ≤ x) : StrictAnti (lamX x) := by
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  fin_cases i <;> simp [lamX] <;> norm_num <;> linarith

theorem hypLamX (x : ℤ) (hx : 0 ≤ x) (hx' : x ≤ 79) : HypLam 3 0 (lamX x) 10 20 80 := by
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hx1 : (x : ℝ) ≤ 79 := by exact_mod_cast hx'
  refine ⟨⟨lamX_anti x hx, ?_⟩, ?_, by norm_num, by norm_num, ?_, by norm_num, by norm_num, ?_⟩
  · intro a
    fin_cases a
    · exact ⟨x - 1, by simp [lamX]; push_cast; ring⟩
    · exact ⟨-41, by simp [lamX]; norm_num⟩
    · exact ⟨-61, by simp [lamX]; norm_num⟩
    · exact ⟨-81, by simp [lamX]; norm_num⟩
  · intro s
    rw [abs_le]
    fin_cases s <;> simp [lamX] <;> constructor <;> linarith
  · have he := Real.exp_one_lt_d9
    push_cast
    linarith
  · intro s t hst
    fin_cases s <;> fin_cases t <;> simp at hst <;> simp [lamX] <;> linarith

theorem hypTypeX (x : ℤ) (hx : 0 ≤ x) (hx' : x ≤ 79) : HypType 3 0 (lamX x) uX 80 := by
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hx1 : (x : ℝ) ≤ 79 := by exact_mod_cast hx'
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro i h1 h3
    interval_cases i
    · exact ⟨79, by simp [uX]; norm_num⟩
    · exact ⟨-1, by simp [uX]; norm_num⟩
    · exact ⟨-51, by simp [uX]; norm_num⟩
  · intro a b hab
    apply lamX_anti x hx
    rw [Fin.lt_def] at hab ⊢
    simpa using hab
  · intro i
    fin_cases i <;> simp [lamX, uX] <;> norm_num <;> first | (refine ⟨?_, ?_⟩ <;> linarith) | linarith
  · intro i h1 h3
    interval_cases i <;> simp [uX] <;> norm_num

theorem ex_plus : NQ ⟨3, 0, 1, 1, uX, uP uX 1 36⟩ (PStar (lamX 20) 10) {-3, -20, -21, -34}
    (nqΛ ⟨3, 0, 1, 1, uX, uP uX 1 36⟩ 80) := by
  refine nq_plus 3 0 1 1 one_pos one_pos (lamX 20) uX 10 20 80 (hypLamX 20 (by norm_num) (by norm_num))
    (hypTypeX 20 (by norm_num) (by norm_num)) 1 36 le_rfl (by norm_num) (by norm_num [uX]) _ ?_
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl <;> norm_num [uX]

theorem ex_minus : NQ ⟨3, 0, 1, 1, uX, uM uX 1 36⟩ (PStar (lamX 60) 10) {-47, -60, -61, -78}
    (nqΛ ⟨3, 0, 1, 1, uX, uM uX 1 36⟩ 80) := by
  refine nq_minus 3 0 1 1 one_pos one_pos (lamX 60) uX 10 20 80 (hypLamX 60 (by norm_num) (by norm_num))
    (hypTypeX 60 (by norm_num) (by norm_num)) 1 36 le_rfl (by norm_num) (by norm_num [uX]) _ ?_
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl <;> norm_num [uX]

theorem nq_of_lamData (P : M.Par) (hOK : P.OK) (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (hk : 2 ≤ P.k) (lam : ℕ → ℝ)
    (c g b : ℝ) (hL : LamData P lam c g b) (Y : Finset ℝ) (hY : ∀ y ∈ Y, I.OnCut P.u P.u' l y) :
    NQ P (PStar (fun s : Fin (2 * P.r + P.k + 1) => lam (s + 1)) c) Y (nqΛ P b) := by
  intro y hy
  obtain ⟨_, hle⟩ := nq_onCut P hOK l hl1 hlk hk lam c g b hL y (hY y hy)
  have e : ∀ z, PStar (fun s : Fin (2 * P.r + P.k + 1) => lam (s + 1)) c z = Pst P.k P.r lam c z := by
    intro z
    rw [← Pst_lamN P.k P.r]
    unfold Pst
    refine Finset.prod_congr rfl fun s hs => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hs
    simp only [lamN]
    rw [dif_pos (by omega)]
    simp only [Fin.val_mk, Nat.sub_add_cancel h1]
  have hb : (0 : ℝ) ≤ b ^ (8 * P.r + 20) / (P.T * P.T') :=
    div_nonneg (pow_nonneg (by linarith [hL.b_ge_three]) _) (mul_pos hOK.T_pos hOK.T'_pos).le
  rw [e, e, nqΛ, Real.sq_sqrt hb]
  exact hle

noncomputable def cfg₁ : Sz.Cfg := { cfg₀ with a := 801 / 2 }

theorem cfg₁_ok : cfg₁.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [cfg₁, cfg₀, Sz.Cfg.v] <;> norm_num

noncomputable def Pc : M.Par := cfgPar cfg₁ 0 1 1 (fun _ => 0) (fun i => if i = 1 then 1 else 0)

theorem lamData_c : LamData Pc cfg₁.lam 10 (4 * cfg₁.Del) 401 := by
  refine lamData_cfg cfg₁ 0 rfl cfg₁_ok 1 1 (fun _ => 0) (fun i => if i = 1 then 1 else 0) (fun _ => Or.inl rfl)
    (fun i => by by_cases h : i = 1 <;> simp [h]) 10 401 (by norm_num) (by norm_num [cfg₁, cfg₀])
    (by norm_num [cfg₁, cfg₀]) ?_
  intro j _ hj2
  simp [cfg₁, cfg₀] at hj2 ⊢
  have : (j : ℝ) ≤ 2 := by exact_mod_cast hj2
  linarith

theorem Pc_OK : Pc.OK := by
  refine ⟨by norm_num [Pc, cfgPar, cfg₁, cfg₀], by norm_num [Pc, cfgPar], by norm_num [Pc, cfgPar], ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i ∈ Finset.Icc 1 4 := hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi'
    interval_cases i
    · exact ⟨0, by simp⟩
    · exact ⟨-281, by simp [Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀]; norm_num⟩
    · exact ⟨-341, by simp [Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀]; norm_num⟩
    · exact ⟨-401, by simp [Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀]; norm_num⟩
  · intro i hi
    have hi' : i ∈ Finset.Icc 1 4 := hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi'
    interval_cases i
    · exact ⟨0, by simp [Pc, cfgPar, Sz.Cfg.u]⟩
    · exact ⟨-296, by simp [Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀]; norm_num⟩
    · exact ⟨-341, by simp [Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀]; norm_num⟩
    · exact ⟨-401, by simp [Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀]; norm_num⟩
  · intro i hi
    have hi' : i ∈ Finset.Icc 1 3 := hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi'
    interval_cases i <;>
      simp [M.Par.lo, M.Par.hi, Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀] <;> norm_num

theorem ex_cfg : NQ Pc (PStar (fun s : Fin (2 * Pc.r + Pc.k + 1) => cfg₁.lam (s + 1)) 10) {-107, -112, -117}
    (nqΛ Pc 401) := by
  refine nq_of_lamData Pc Pc_OK 2 (by norm_num) (by show 2 ≤ 4; norm_num) (by show 2 ≤ 4; norm_num)
    cfg₁.lam 10 (4 * cfg₁.Del) 401 lamData_c _ ?_
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  right
  rcases hy with rfl | rfl | rfl <;>
    simp [Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀] <;> norm_num

end CompanionTheory.WaveGrid.Inhab
