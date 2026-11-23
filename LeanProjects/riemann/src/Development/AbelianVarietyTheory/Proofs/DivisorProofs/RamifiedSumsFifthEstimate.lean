import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.TreeLeafParameterArithmeticOfBounds

open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cloud_mem_Icc_Sc {D : D7} (L : SizeData₂ D) (τ i : ℕ) :
    0 ≤ cloud D τ i ∧ (cloud D τ i : ℝ) ≤ L.Sc := by
  unfold cloud
  split_ifs with h
  · dsimp only [GlobalTheory.SignedHC.GridData.ofHCParam]
    unfold GlobalTheory.SignedHC.GridData.extend
    split_ifs with h2
    · obtain ⟨h0, h1⟩ := L.cloud_v ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩) ⟨i - 2, h2⟩
      refine ⟨Int.floor_nonneg.mpr (by exact_mod_cast h0), ?_⟩
      have hf := Int.floor_le ((D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩)
      have hf' : (((⌊(D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩⌋ : ℤ) : ℚ) : ℝ) ≤
          (((D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩ : ℚ) : ℝ) := by exact_mod_cast hf
      push_cast at hf' ⊢
      linarith
    · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩
  · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩

theorem Lc_le_of_cloud_le {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (O : FunData K Df) (S : ℝ) (h0 : 0 ≤ S) (hcl : ∀ τ i, 0 ≤ O.cl τ i ∧ (O.cl τ i : ℝ) ≤ S) :
    (O.Lc : ℝ) ≤ S := by
  have hL : O.Lc ≤ ⌊S⌋₊ := by
    unfold FunData.Lc
    refine Finset.sup_le fun τ _ => ?_
    rw [Nat.le_floor_iff h0]
    obtain ⟨a0, a1⟩ := hcl τ 2
    obtain ⟨b0, -⟩ := hcl τ O.k
    have h : ((O.cl τ 2 - O.cl τ O.k).toNat : ℤ) ≤ O.cl τ 2 := by omega
    have h' : (((O.cl τ 2 - O.cl τ O.k).toNat : ℤ) : ℝ) ≤ ((O.cl τ 2 : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  calc (O.Lc : ℝ) ≤ (⌊S⌋₊ : ℝ) := by exact_mod_cast hL
    _ ≤ S := Nat.floor_le h0

theorem Sc_le_scale_b {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : L.Sc ≤ L.sc.b := by
  have hk := P.kS_le
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hn : (1 : ℝ) ≤ D.R.n := by
    unfold Ranks.n
    exact_mod_cast D.R.ord_pos
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hw : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w'' Scale.b' Scale.a
    rw [div_le_iff₀ (by positivity)]
    calc L.sc.x * L.sc.b / L.sc.X' ≤ L.sc.x * L.sc.b := div_le_self (by positivity) hX
      _ ≤ L.sc.b * (L.sc.x * D.R.n) := by nlinarith [mul_nonneg (mul_pos hx hb).le (sub_nonneg.2 hn)]
  have hS := L.Sc_pos
  nlinarith

theorem mul_pow_le_exp_rpow {eps : ℝ} (heps : 0 < eps) (a : ℕ) (A : ℝ) :
    ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x, x0 ≤ x → A * x ^ a ≤ Real.exp (x ^ eps) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((a : ℝ) + 1) ≤ eps * n := ⟨⌈((a : ℝ) + 1) / eps⌉₊, by
    have := Nat.le_ceil (((a : ℝ) + 1) / eps)
    rw [div_le_iff₀ heps] at this
    linarith⟩
  refine ⟨max 1 (|A| * n.factorial), le_max_left _ _, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hy : 0 ≤ x ^ eps := Real.rpow_nonneg hx0 _
  have h1 := Real.pow_div_factorial_le_exp (x ^ eps) hy n
  have h2 : (x ^ eps) ^ n = x ^ (eps * n) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
  have h3 : x ^ (((a + 1 : ℕ)) : ℝ) ≤ x ^ (eps * n) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  rw [Real.rpow_natCast] at h3
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hAx : |A| * n.factorial ≤ x := (le_max_right _ _).trans hx
  have hxa : 0 ≤ x ^ a := pow_nonneg hx0 a
  have e2 : |A| * x ^ a * n.factorial ≤ x ^ (a + 1) :=
    calc |A| * x ^ a * n.factorial = x ^ a * (|A| * n.factorial) := by ring
      _ ≤ x ^ a * x := mul_le_mul_of_nonneg_left hAx hxa
      _ = x ^ (a + 1) := (pow_succ x a).symm
  have e3 : |A| * x ^ a ≤ x ^ (a + 1) / n.factorial := by rw [le_div_iff₀ hf]; exact e2
  rw [h2] at h1
  calc A * x ^ a ≤ |A| * x ^ a := mul_le_mul_of_nonneg_right (le_abs_self A) hxa
    _ ≤ x ^ (a + 1) / n.factorial := e3
    _ ≤ x ^ (eps * n) / n.factorial := by gcongr
    _ ≤ _ := h1

theorem design_lines_of_ranks (x eps B : ℝ) (c k m f t : ℕ) (hx : 20480 ≤ x) (heps : eps ≤ 1)
    (hm : 2 ≤ m) (hmf : m ≤ f) (hfk : f ≤ k) (hkt : k + m + 4 ≤ t)
    (ht : (t : ℝ) ≤ x ^ c) (hto : x ^ 377 ≤ (t : ℝ)) (hk : (k : ℝ) ≤ 2 * x ^ (9 / 2 + 10 * eps))
    (hB : 25 * x ^ (6 * c) ≤ B) :
    (m : ℝ) * f * (((k + m * (t + (k + m + 5) + 1) : ℕ) : ℝ)) ^ 2 ≤ B ∧
      80 * ((k : ℝ) + m - 1) ^ 4 ≤ (((k + m * (t + (k + m + 5) + 1) : ℕ) : ℝ)) := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  constructor
  · have hN : k + m * (t + (k + m + 5) + 1) ≤ 5 * t ^ 2 := by
      have h1 : t + (k + m + 5) + 1 ≤ 4 * t := by omega
      have h2 : m * (t + (k + m + 5) + 1) ≤ t * (4 * t) := Nat.mul_le_mul (by omega) h1
      nlinarith
    have hP : m * f * (k + m * (t + (k + m + 5) + 1)) ^ 2 ≤ 25 * t ^ 6 := by
      have h1 : m * f ≤ t * t := Nat.mul_le_mul (by omega) (by omega)
      have h2 : (k + m * (t + (k + m + 5) + 1)) ^ 2 ≤ (5 * t ^ 2) ^ 2 := Nat.pow_le_pow_left hN 2
      calc m * f * (k + m * (t + (k + m + 5) + 1)) ^ 2 ≤ (t * t) * (5 * t ^ 2) ^ 2 := Nat.mul_le_mul h1 h2
        _ = 25 * t ^ 6 := by ring
    have hP' : ((m * f * (k + m * (t + (k + m + 5) + 1)) ^ 2 : ℕ) : ℝ) ≤ ((25 * t ^ 6 : ℕ) : ℝ) := by
      exact_mod_cast hP
    push_cast at hP'
    have ht6 : (t : ℝ) ^ 6 ≤ (x ^ c) ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) ht 6
    rw [← pow_mul, mul_comm c 6] at ht6
    push_cast
    linarith
  · have hkr : (k : ℝ) ≤ 2 * x ^ 15 := by
      have e : x ^ (9 / 2 + 10 * eps) ≤ x ^ ((15 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
      rw [Real.rpow_natCast] at e
      linarith
    have hmk : (m : ℝ) ≤ k := by exact_mod_cast (le_trans hmf hfk)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hr0 : 0 ≤ (k : ℝ) + m - 1 := by linarith
    have hr : (k : ℝ) + m - 1 ≤ 4 * x ^ 15 := by linarith
    have hr4 : ((k : ℝ) + m - 1) ^ 4 ≤ (4 * x ^ 15) ^ 4 := pow_le_pow_left₀ hr0 hr 4
    have e1 : (4 * x ^ 15) ^ 4 = 256 * x ^ 60 := by ring
    have e2 : 20480 * x ^ 60 ≤ x ^ 377 := by
      have a1 : 20480 * x ^ 60 ≤ x * x ^ 60 := mul_le_mul_of_nonneg_right hx (pow_nonneg hx0 _)
      have a2 : x * x ^ 60 = x ^ 61 := by ring
      have a3 : x ^ 61 ≤ x ^ 377 := pow_le_pow_right₀ hx1 (by norm_num)
      linarith
    have e3 : (t : ℝ) ≤ (((k + m * (t + (k + m + 5) + 1) : ℕ) : ℝ)) := by
      have : t ≤ k + m * (t + (k + m + 5) + 1) := by nlinarith
      exact_mod_cast this
    nlinarith

end GlobalTheory.BigTop.Fun

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ramified_sums_fifth_bound : RankGapBound := by
  refine ⟨0, fun CF _ => ⟨1, one_pos, fun eps heps heps1 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm CH hF _ => ?_⟩⟩⟩
  intro _
  refine ⟨1, fun C hC => ?_⟩
  obtain ⟨-, heP, hcTO, -, -, -, -, -, hfix⟩ := hF.1
  have hW : PageWin Fm := hF.2.1
  obtain ⟨x2, hx21, hx2⟩ := mul_pow_le_exp_rpow heps (6 * (⌈|Fm.Ct|⌉₊ + 1)) 25
  refine ⟨max (max (Fm.x1 + 1) ((8 : ℝ) ^ (1 / eps))) (max (max x2 20480) ((2 * C) ^ 2)),
    fun x hx hx0 i p _ d _ => ?_⟩
  have hxa : Fm.x1 + 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
  have hx8 : (8 : ℝ) ^ (1 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
  have hxb : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx0
  have hxc : 20480 ≤ x := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hx0
  have hxC : (2 * C) ^ 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx0
  have hx1 : 1 < x := by linarith
  have hx0' : (0 : ℝ) < x := by linarith

  have h8 : (8 : ℝ) ≤ x ^ (8 * eps) := by
    have e1 : (8 : ℝ) = ((8 : ℝ) ^ (1 / eps)) ^ eps := by
      rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ heps.ne', Real.rpow_one]
    have e2 : ((8 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps :=
      Real.rpow_le_rpow (by positivity) hx8 heps.le
    have e3 : x ^ eps ≤ x ^ (8 * eps) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    linarith
  obtain ⟨⟨hn, -⟩, ⟨-, hm⟩, ⟨-, hk⟩⟩ := hW x hx i
  have hδ : (Fm.L x i).sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos (Fm.L x i).sc.one_lt_alt.le
      (by linarith [(Fm.L x i).sc.eps_pos])
  have hδ0 : 0 ≤ (Fm.L x i).sc.delta1 := by
    unfold Scale.delta1
    exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _
  have hm4 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ (((Fm.D x i).R.f : ℕ) : ℝ) := by
    have hs := Real.sq_sqrt (mul_nonneg hx0'.le hδ0)
    have hs0 := Real.sqrt_nonneg (x * (Fm.L x i).sc.delta1)
    have hm0 : (0 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by positivity
    have hm2 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 2 ≤ 4 * x := by nlinarith
    have hm4' : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ 16 * x ^ 2 := by nlinarith
    have hpow : x ^ ((2 : ℝ) + 8 * eps) = x ^ 2 * x ^ (8 * eps) := by
      rw [Real.rpow_add hx0', Real.rpow_two]
    have hf : (((Fm.D x i).R.f : ℕ) : ℝ) = 2 * ((Fm.D x i).R.n : ℝ) := by
      unfold Ranks.f
      push_cast
      ring
    rw [hf]
    have hx2' : 0 ≤ x ^ 2 := by positivity
    nlinarith
  have hH1 : leafHypothesesConst d.O := ⟨(Fm.D x i).R.two_le_m, (Fm.D x i).R.m_add_three_le_k, by exact_mod_cast hm4,
    (Fm.D x i).R.f_le_k⟩

  have hH7 : LatticeConstantBound d.O p.Z.b := by
    show (FunData.Lc d.O : ℝ) ≤ (Fm.L x i).sc.b
    exact (Lc_le_of_cloud_le d.O (Fm.L x i).Sc (Fm.L x i).Sc_pos.le
      (fun τ j => cloud_mem_Icc_Sc (Fm.L x i) τ j)).trans (Sc_le_scale_b (Fm.params x hx i))

  have hb : p.Z.b = Real.exp (x ^ eps) := by
    show Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) = _
    rw [Fm.L_x x i hx, Fm.L_eps x i]

  have hT : (Fm.parT x hx i).TO ≤ (Fm.D x i).R.t := by
    have a1 := (Fm.parT x hx i).split
    have a2 := (Fm.parT x hx i).nP_eq
    have a3 := (Fm.parT x hx i).nW_lo.1
    have hf : 1 ≤ (Fm.D x i).R.f := by
      have : 0 < (Fm.D x i).R.ord := (Fm.D x i).R.ord_pos
      unfold Ranks.f Ranks.n; omega
    have hr : 1 ≤ (Fm.D x i).R.r := by
      have := (Fm.D x i).R.m_add_three_le_k
      unfold Ranks.r; omega
    have a4 : 1 ≤ (Fm.parT x hx i).nWn :=
      le_trans (Nat.mul_pos (Nat.mul_pos hf hr) (Nat.succ_pos _)) a3
    have a5 : (Fm.parT x hx i).TO * 1 ≤ (Fm.parT x hx i).TO * (Fm.parT x hx i).nWn := Nat.mul_le_mul_left _ a4
    have a6 : 1 * (Fm.D x i).R.r ≤ 8 * (Fm.D x i).R.f * (Fm.D x i).R.r := Nat.mul_le_mul_right _ (by omega)
    omega
  have hto : x ^ 377 ≤ ((Fm.D x i).R.t : ℝ) := by
    have e1 : Fm.cTO = ((377 : ℕ) : ℝ) := by rw [hcTO, heP]; norm_num
    have e2 := (hfix x hx i).2.2.2.2.2.2.2
    have e3 : x ^ Fm.cTO ≤ ((Fm.parT x hx i).TO : ℝ) := by rw [e2]; exact Nat.le_ceil _
    rw [e1, Real.rpow_natCast] at e3
    exact e3.trans (by exact_mod_cast hT)
  have htc : ((Fm.D x i).R.t : ℝ) ≤ x ^ (⌈|Fm.Ct|⌉₊ + 1) := by
    have e1 := (Fm.L x i).t_win.2
    rw [Fm.Ct_eq x i, Fm.L_x x i hx] at e1
    refine e1.trans ?_
    have e2 : x ^ Fm.Ct ≤ x ^ (((⌈|Fm.Ct|⌉₊ + 1 : ℕ)) : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le hx1.le ?_
      push_cast
      linarith [le_abs_self Fm.Ct, Nat.le_ceil |Fm.Ct|]
    rwa [Real.rpow_natCast] at e2
  have hmf : (Fm.D x i).R.m ≤ (Fm.D x i).R.f := by
    have := (Fm.D x i).R.m_le_f
    unfold Ranks.f Ranks.n; omega
  have hkt : (Fm.D x i).R.k + (Fm.D x i).R.m + 4 ≤ (Fm.D x i).R.t := by
    have := (Fm.D x i).R.rank_add_five_le
    have := (Fm.D x i).R.m_add_three_le_k
    omega
  have hB := hx2 x hxb
  obtain ⟨l1, l2⟩ := design_lines_of_ranks x eps (Real.exp (x ^ eps)) (⌈|Fm.Ct|⌉₊ + 1) (Fm.D x i).R.k (Fm.D x i).R.m
    (Fm.D x i).R.f (Fm.D x i).R.t hxc heps1 (Fm.D x i).R.two_le_m hmf (Fm.D x i).R.f_le_k hkt htc hto hk hB

  have hL : 2 * Real.log (2 * C) ≤ Real.log p.Z.b := by
    rw [hb, Real.log_exp]
    have e1 : x ≤ x ^ (6 * (⌈|Fm.Ct|⌉₊ + 1)) := le_self_pow₀ hx1.le (by omega)
    have e2 : x ≤ Real.exp (x ^ eps) := by
      have : 0 ≤ x ^ (6 * (⌈|Fm.Ct|⌉₊ + 1)) := by positivity
      linarith
    have e3 : Real.log x ≤ x ^ eps := by
      rw [Real.log_le_iff_le_exp hx0']; exact e2
    have e4 : 2 * Real.log (2 * C) = Real.log ((2 * C) ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    have e5 : Real.log ((2 * C) ^ 2) ≤ Real.log x := Real.log_le_log (by positivity) hxC
    linarith
  refine GlobalTheory.SizeLeafCheck.tree_leaf_parameter_arithmetic_of_bounds d.O C p.Z.b hC hH1 hH7 ?_ ?_ hL
  · rw [hb]
    exact l1
  · exact l2

end GlobalTheory.BigTop.Fun
