import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.FormalDegreeBessel.FinalG
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ParabolicSumAdmissibleOfParabolic
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.AbsPointwiseMonoConstant

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.FourierDecayAlt Finset
open scoped ENNReal

theorem superfactorial_pos (j : ℕ) : 0 < superfactorial j := Finset.prod_pos (fun i _ => by positivity)

theorem unitary_group_volume_formula (j : ℕ) : UnitaryVolumeMass.volU j = (2 * Real.pi) ^ triangularNumber j / superfactorial j := by
  unfold UnitaryVolumeMass.volU triangularNumber superfactorial
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]

theorem triangular_number_succ_alt (j : ℕ) : triangularNumber (j + 1) = triangularNumber j + (j + 1) := by
  unfold triangularNumber; rw [Finset.sum_range_succ]

theorem superfactorial_succ (j : ℕ) : superfactorial (j + 1) = superfactorial j * (j.factorial : ℝ) := by
  unfold superfactorial; rw [Finset.prod_range_succ]

theorem triangular_number_add (k N : ℕ) : 2 * triangularNumber (k + N) = 2 * triangularNumber k + 2 * N * k + N * (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [← add_assoc, triangular_number_succ_alt, mul_add, ih]; ring

theorem triangular_number_top (k r : ℕ) :
    triangularNumber (k + 2 * r + 1) = triangularNumber k + ((2 * r + 1) * k + (r + 1) * (2 * r + 1)) := by
  have h := triangular_number_add k (2 * r + 1)
  apply Nat.eq_of_mul_eq_mul_left (two_pos)
  rw [show k + 2 * r + 1 = k + (2 * r + 1) by ring, h]; ring

theorem exp_mul_pow_le_succ_pow (k : ℕ) : Real.exp 1 * (k : ℝ) ^ (k + 1) ≤ ((k : ℝ) + 1) ^ (k + 1) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : (k : ℝ) / ((k : ℝ) + 1) ≤ Real.exp (-(1 / ((k : ℝ) + 1))) := by
    have := Real.add_one_le_exp (-(1 / ((k : ℝ) + 1)))
    have e : -(1 / ((k : ℝ) + 1)) + 1 = (k : ℝ) / ((k : ℝ) + 1) := by field_simp; ring
    rwa [e] at this
  have h2 : ((k : ℝ) / ((k : ℝ) + 1)) ^ (k + 1) ≤ Real.exp (-1) := by
    have := pow_le_pow_left₀ (by positivity) h1 (k + 1)
    rw [← Real.exp_nat_mul] at this
    have e : ((k + 1 : ℕ) : ℝ) * -(1 / ((k : ℝ) + 1)) = -1 := by push_cast; field_simp
    rwa [e] at this
  rw [div_pow, div_le_iff₀ (by positivity), Real.exp_neg] at h2
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  calc Real.exp 1 * (k : ℝ) ^ (k + 1) ≤ Real.exp 1 * ((Real.exp 1)⁻¹ * ((k : ℝ) + 1) ^ (k + 1)) := by gcongr
    _ = ((k : ℝ) + 1) ^ (k + 1) := by field_simp

theorem factorial_exp_pow_le (j : ℕ) :
    (j.factorial : ℝ) * Real.exp 1 ^ (j + 1) ≤ Real.exp 1 * ((j : ℝ) + 1) ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have h := exp_mul_pow_le_succ_pow (j + 1)
    push_cast at h ⊢
    rw [Nat.factorial_succ]
    push_cast
    calc ((j : ℝ) + 1) * (j.factorial : ℝ) * Real.exp 1 ^ (j + 1 + 1)
        = ((j : ℝ) + 1) * Real.exp 1 * ((j.factorial : ℝ) * Real.exp 1 ^ (j + 1)) := by ring
      _ ≤ ((j : ℝ) + 1) * Real.exp 1 * (Real.exp 1 * ((j : ℝ) + 1) ^ (j + 1)) := by gcongr
      _ = Real.exp 1 * (Real.exp 1 * ((j : ℝ) + 1) ^ (j + 1 + 1)) := by ring
      _ ≤ Real.exp 1 * ((j : ℝ) + 1 + 1) ^ (j + 1 + 1) := by gcongr

theorem exp_pow_factorial_le_exp (j : ℕ) :
    (Real.exp 1 / ((j : ℝ) + 1)) ^ (j + 1) * (j.factorial : ℝ) ≤ Real.exp 1 := by
  have h := factorial_exp_pow_le j
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

theorem volume_constant_main_estimate (k r m n : ℕ) (hm : m = 2 * r + 2) (hn : n = k + 2 * r + 1) (hk : 1 ≤ k)
    (v g T T' dp Vu ds B1 B2 : ℝ) (hv : 0 < v) (hg : 0 < g) (hT : 0 < T) (hT' : 0 < T') (hdp : 0 ≤ dp)
    (hVu : 0 < Vu) (hds : 0 < ds)
    (hfin : Real.exp 1 * (2 * v * g) ^ ((r + 1) * (2 * r + 1)) * B1 ≤
      T * T' * (2 * v) ^ (((m : ℝ) - 1) / 2) * B2) (hB1 : 0 ≤ B1) :
    (Real.exp 1 * Real.pi * (g ^ m)⁻¹ / (T * k * v)) ^ k *
      ((T * T') ^ (k - 1) * (dp * (Vu / superfactorial k) * UnitaryVolumeMass.volU n * UnitaryVolumeMass.volU (k - 1) /
        (ds * UnitaryVolumeMass.volU k ^ 2 * (2 * v) ^ (2 * r * k))) * B1) ≤
    dp * (Sz.TcritPow k m (Real.pi / v) (2 * v) g (ds * superfactorial n) Vu / T' ^ k)⁻¹ * B2 := by
  subst hm hn
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  have e2 : (2 * r + 2) * (2 * r + 1) / 2 = (r + 1) * (2 * r + 1) := by
    rw [show (2 * r + 2) * (2 * r + 1) = 2 * ((r + 1) * (2 * r + 1)) by ring]; simp
  unfold Sz.TcritPow
  rw [e1, e2, Real.rpow_neg (by positivity)]
  simp only [Nat.add_sub_cancel]
  set rp : ℝ := (2 * v) ^ ((((2 * r + 2 : ℕ) : ℝ) - 1) / 2) with hrp
  have hrp0 : 0 < rp := by positivity
  rw [unitary_group_volume_formula (j + 1 + 2 * r + 1), unitary_group_volume_formula (j + 1), unitary_group_volume_formula j, triangular_number_top, triangular_number_succ_alt, superfactorial_succ j]
  set q : ℕ := (r + 1) * (2 * r + 1) with hq
  set Fn : ℝ := superfactorial (j + 1 + 2 * r + 1) with hFn
  set Fj : ℝ := superfactorial j with hFj
  have hFn0 : 0 < Fn := superfactorial_pos _
  have hFj0 : 0 < Fj := superfactorial_pos _
  have hjf : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hj1 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  set Z : ℝ := dp * Vu * (2 * Real.pi) ^ ((2 * r + 1) * (j + 1) + q) * T' ^ (j + 1) /
    ((2 * v) ^ ((2 * r + 1) * (j + 1) + q) * g ^ ((j + 1) * (2 * r + 2) + q) * ds * Fn) with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hL : (Real.exp 1 * Real.pi * (g ^ (2 * r + 2))⁻¹ / (T * ((j + 1 : ℕ) : ℝ) * v)) ^ (j + 1) *
      ((T * T') ^ j * (dp * (Vu / (Fj * (j.factorial : ℝ))) *
          ((2 * Real.pi) ^ (triangularNumber j + (j + 1) + ((2 * r + 1) * (j + 1) + q)) / Fn) *
          ((2 * Real.pi) ^ triangularNumber j / Fj) /
        (ds * ((2 * Real.pi) ^ (triangularNumber j + (j + 1)) / (Fj * (j.factorial : ℝ))) ^ 2 *
          (2 * v) ^ (2 * r * (j + 1)))) * B1) =
      Z / (T * T') * ((Real.exp 1 / ((j : ℝ) + 1)) ^ (j + 1) * (j.factorial : ℝ) * (2 * v * g) ^ q * B1) := by
    rw [hZ]
    push_cast
    simp only [div_pow, mul_pow, inv_pow]
    field_simp
    ring
  have hR : dp * (((Real.pi / v) ^ ((2 * r + 1) * (j + 1) + q))⁻¹ * rp⁻¹ * g ^ ((j + 1) * (2 * r + 2) + q) *
      (ds * Fn) / Vu / T' ^ (j + 1))⁻¹ * B2 = Z / (T * T') * (T * T' * rp * B2) := by
    rw [hZ]
    simp only [div_pow, mul_pow]
    field_simp
  rw [hL, hR]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hs := exp_pow_factorial_le_exp j
  calc (Real.exp 1 / ((j : ℝ) + 1)) ^ (j + 1) * (j.factorial : ℝ) * (2 * v * g) ^ q * B1
      ≤ Real.exp 1 * (2 * v * g) ^ q * B1 := by gcongr
    _ ≤ T * T' * rp * B2 := hfin

theorem numerical_constant_clause_bound (r m : ℕ) (hm : m = 2 * r + 2) (b L V g T T' Cl Cg CS C : ℝ) (hb : b = Real.exp L) (hL : 1 ≤ L)
    (hV1 : 1 ≤ V) (hV : Real.log V ≤ L / Cl) (hg1 : 1 ≤ g) (hg : g ≤ b ^ (2 * Cg)) (hT : 1 ≤ T) (hT' : 1 ≤ T')
    (hC : CS + 1 + (1 / Cl + 2 * Cg) / 2 ≤ C) :
    Real.exp 1 * (V * g) ^ ((r + 1) * (2 * r + 1)) * b ^ (CS * (m : ℝ) ^ 2) ≤
      T * T' * V ^ (((m : ℝ) - 1) / 2) * b ^ (C * (m : ℝ) ^ 2) := by
  have hb1 : 1 < b := by rw [hb]; exact Real.one_lt_exp_iff.2 (by linarith)
  have hb0 : 0 < b := by linarith
  have hV0 : 0 < V := by linarith
  have hVb : V ≤ b ^ (1 / Cl) := by
    rw [hb, ← Real.exp_mul, ← Real.exp_log hV0]
    apply Real.exp_le_exp.2
    calc Real.log V ≤ L / Cl := hV
      _ = L * (1 / Cl) := by ring
  set E : ℝ := 1 / Cl + 2 * Cg with hE
  have hVg : V * g ≤ b ^ E := by
    rw [hE, Real.rpow_add hb0]
    exact mul_le_mul hVb hg (by linarith) (by positivity)
  have hVg1 : 1 ≤ V * g := by nlinarith
  have hE0 : 0 ≤ E := by
    by_contra h
    have := Real.rpow_lt_one_of_one_lt_of_neg hb1 (not_le.1 h)
    linarith
  have hmR : (m : ℝ) = 2 * (r : ℝ) + 2 := by rw [hm]; push_cast; ring
  have hq : (((r + 1) * (2 * r + 1) : ℕ) : ℝ) ≤ (m : ℝ) ^ 2 / 2 := by
    rw [hmR]; push_cast
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
    rw [hmR]
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith
  have h1 : (V * g) ^ ((r + 1) * (2 * r + 1)) ≤ b ^ (E * ((m : ℝ) ^ 2 / 2)) := by
    calc (V * g) ^ ((r + 1) * (2 * r + 1)) ≤ (b ^ E) ^ ((r + 1) * (2 * r + 1)) :=
          pow_le_pow_left₀ (by linarith) hVg _
      _ = b ^ (E * (((r + 1) * (2 * r + 1) : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
      _ ≤ b ^ (E * ((m : ℝ) ^ 2 / 2)) :=
          Real.rpow_le_rpow_of_exponent_le hb1.le (mul_le_mul_of_nonneg_left hq hE0)
  have h2 : Real.exp 1 ≤ b ^ ((m : ℝ) ^ 2) := by
    calc Real.exp 1 ≤ b := by rw [hb]; exact Real.exp_le_exp.2 hL
      _ = b ^ (1 : ℝ) := (Real.rpow_one b).symm
      _ ≤ b ^ ((m : ℝ) ^ 2) := Real.rpow_le_rpow_of_exponent_le hb1.le hm1
  have h3 : 1 ≤ V ^ (((m : ℝ) - 1) / 2) := by
    apply Real.one_le_rpow hV1
    rw [hmR]
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have h4 : b ^ ((m : ℝ) ^ 2) * b ^ (E * ((m : ℝ) ^ 2 / 2)) * b ^ (CS * (m : ℝ) ^ 2) ≤ b ^ (C * (m : ℝ) ^ 2) := by
    rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]
    apply Real.rpow_le_rpow_of_exponent_le hb1.le
    have : (CS + 1 + E / 2) * (m : ℝ) ^ 2 ≤ C * (m : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hC (by positivity)
    linarith
  have hB : 0 < b ^ (C * (m : ℝ) ^ 2) := by positivity
  calc Real.exp 1 * (V * g) ^ ((r + 1) * (2 * r + 1)) * b ^ (CS * (m : ℝ) ^ 2)
      ≤ b ^ ((m : ℝ) ^ 2) * b ^ (E * ((m : ℝ) ^ 2 / 2)) * b ^ (CS * (m : ℝ) ^ 2) := by gcongr
    _ ≤ b ^ (C * (m : ℝ) ^ 2) := h4
    _ = 1 * 1 * 1 * b ^ (C * (m : ℝ) ^ 2) := by ring
    _ ≤ T * T' * V ^ (((m : ℝ) - 1) / 2) * b ^ (C * (m : ℝ) ^ 2) := by gcongr

theorem constant_clause_schur_weyl (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 CS C : ℝ)
    (hC : CS + 1 + (1 / Cl + 2 * Cg) / 2 ≤ C) : VanishingOnXAndXPlusBranching.IntegralityFromMetric D large₂ C' Cl Cg cb Cu cT CT C0 C1 CS C := by
  intro hS hW hH τ w w' hTT θ hθ W hGW A hGS hdeg μsec hsec
  have h1 := hS hH τ w w' hTT θ hθ W hGW A hGS μsec hsec
  have hq : (Module.finrank ℂ W.Wq : ℝ) = vand (uS D w' τ) / superfactorial D.R.k := hW τ w' W.Wq W.z' W.π' hGW.2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h11, _, h13, _, h15, _, _, _, h19, _, _, _, _, _, h25⟩ := hH.1
  have hv0 : 0 < D.host.v := by linarith
  have hka : 0 < D.host.ka := by unfold Host.ka; exact div_pos Real.pi_pos hv0
  have hg0 : (1 : ℝ) ≤ (D.host.g 0 : ℝ) := by exact_mod_cast (D.host.g_prime 0).one_lt.le
  have hg1 : (1 : ℝ) ≤ (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).one_lt.le
  have hgg1 : 1 ≤ gg D := by unfold gg; nlinarith
  have hgg0 : 0 < gg D := by linarith
  have hb0 : 0 < large₂.sc.b := lt_trans one_pos (one_lt_b large₂)
  have hggb : gg D ≤ large₂.sc.b ^ (2 * Cg) := by
    unfold gg
    rw [two_mul, Real.rpow_add hb0]
    exact mul_le_mul h13 h15 (by linarith) (by positivity)
  have hT : (1 : ℝ) ≤ Tr D w := by
    unfold Tr; exact_mod_cast le_trans (by norm_num) hTT.2.2.1
  have hT' : (1 : ℝ) ≤ Tr D w' := by
    unfold Tr; exact_mod_cast le_trans (by norm_num) hTT.2.2.2.1
  have hk : 1 ≤ D.R.k := le_trans (by norm_num) (five_le_k D)
  have hn : D.R.r = D.R.k + 2 * D.R.rS + 1 := by have := dimS_eq D.R; omega
  have hdp : (0 : ℝ) ≤ (Module.finrank ℂ W.Wp : ℝ) := Nat.cast_nonneg _
  have hnV0 : 0 ≤ normalizedLocalScale D w := by unfold normalizedLocalScale; positivity
  have hVnn : 0 ≤ vand (uS D w' τ) := by
    have h : 0 ≤ vand (uS D w' τ) / superfactorial D.R.k := by rw [← hq]; exact Nat.cast_nonneg _
    have := mul_nonneg h (superfactorial_pos D.R.k).le
    rwa [div_mul_cancel₀ _ (superfactorial_pos D.R.k).ne'] at this
  refine le_trans (mul_le_mul' le_rfl h1) ?_
  rw [← ENNReal.ofReal_mul hnV0]
  apply ENNReal.ofReal_le_ofReal
  rw [hq, hdeg]
  rcases hVnn.eq_or_lt with h0 | hVpos
  · rw [← h0]
    simp only [zero_div, mul_zero, zero_mul]
    have : 0 ≤ tvPr D τ w' ^ D.R.k := D.R.k_even.pow_nonneg _
    positivity
  · have hfin := numerical_constant_clause_bound D.R.rS D.R.m (m_eq D) large₂.sc.b large₂.sc.L (2 * D.host.v) (gg D) (Tr D w) (Tr D w') Cl Cg CS C
      rfl (one_le_L large₂) (by linarith) (by rw [← rdE_eq]; exact h11) hgg1 hggb hT hT' hC
    have hmain := volume_constant_main_estimate D.R.k D.R.rS D.R.m D.R.r (m_eq D) hn hk D.host.v (gg D) (Tr D w) (Tr D w')
      (Module.finrank ℂ W.Wp : ℝ) (vand (uS D w' τ)) (D.dsig τ) (large₂.sc.b ^ (CS * (D.R.m : ℝ) ^ 2))
      (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2)) hv0 hgg0 (by linarith) (by linarith) hdp hVpos (D.dsig_pos τ) hfin
      (by positivity)
    have hX : 0 ≤ Sz.TcritPow D.R.k D.R.m D.host.ka D.host.rdE (gg D) (VV D τ) (vand (uS D w' τ)) := by
      have hrd : 0 < D.host.rdE := by rw [rdE_eq]; linarith
      have hVV : 0 < VV D τ := by
        unfold VV
        exact mul_pos (D.dsig_pos τ) (superfactorial_pos D.R.r)
      unfold Sz.TcritPow
      positivity
    have htv : tvPr D τ w' ^ D.R.k =
        Sz.TcritPow D.R.k D.R.m (Real.pi / D.host.v) (2 * D.host.v) (gg D) (D.dsig τ * superfactorial D.R.r)
          (vand (uS D w' τ)) / Tr D w' ^ D.R.k := by
      unfold tvPr
      rw [div_pow, ← Tcrit_eq D w' τ hka.le]
      unfold Sz.Tcrit
      rw [one_div, Real.rpow_inv_natCast_pow hX (by omega), rdE_eq]
      rfl
    have hn0 : normalizedLocalScale D w = (Real.exp 1 * Real.pi * (gg D ^ D.R.m)⁻¹ / (Tr D w * D.R.k * D.host.v)) ^ D.R.k := by
      unfold normalizedLocalScale
      rw [Real.rpow_neg hgg0.le, Real.rpow_natCast]
    rw [htv, hn0]
    exact hmain

end Formalism.MainNotions.BridgeLemma

end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Cnt MeasureTheory
open scoped ENNReal

theorem list_map_prod_le (f g : ℕ → ℝ) (h : ∀ a, 0 ≤ f a ∧ f a ≤ g a) :
    ∀ l : List ℕ, 0 ≤ (l.map f).prod ∧ (l.map f).prod ≤ (l.map g).prod := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact ⟨mul_nonneg (h a).1 ih.1, mul_le_mul (h a).2 ih.2 ih.1 (le_trans (h a).1 (h a).2)⟩

theorem one_le_max_self_inv {t : ℝ} (ht : 0 < t) : 1 ≤ max t t⁻¹ := by
  rcases le_total 1 t with h | h
  · exact le_trans h (le_max_left _ _)
  · exact le_trans ((one_le_inv₀ ht).2 h) (le_max_right _ _)

theorem max_inv_pow_le_rpow (t : ℝ) (ht : 0 ≤ t) (m : ℕ) (hm : 2 ≤ m) (C : ℝ) (hC : 6 ≤ C) :
    0 ≤ (max t t⁻¹) ^ (2 * (m + 4)) ∧ (max t t⁻¹) ^ (2 * (m + 4)) ≤ (max t t⁻¹) ^ (C * (m : ℝ)) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    have hm' : (m : ℝ) ≠ 0 := by positivity
    have : C * (m : ℝ) ≠ 0 := mul_ne_zero (by linarith) hm'
    simp only [inv_zero, max_self, Real.zero_rpow this, zero_pow (by omega : 2 * (m + 4) ≠ 0), le_refl, and_self]
  · have h1 := one_le_max_self_inv h
    refine ⟨by positivity, ?_⟩
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le h1
    push_cast
    nlinarith

theorem one_le_scale_base {D : D7} (large₂ : SizeData₂ D) : 1 ≤ large₂.sc.b := by
  unfold Scale.b Scale.L
  apply Real.one_le_exp
  exact Real.rpow_nonneg (le_of_lt (lt_trans one_pos large₂.sc.one_lt_alt)) _

theorem loss_factor_le_rpow {k r : ℕ} (b CPT Cc C : ℝ) (m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r)
    (p : Point ℂ (r + 1)) (hb : 1 ≤ b) (hm : 2 ≤ m) (hPT : 0 ≤ CPT) (hCc : 0 ≤ Cc) (hC : CPT + Cc + 6 ≤ C)
    (hG : 0 < Gf k r z z' γ) :
    b ^ (CPT * (m : ℝ) ^ 4) * (max 1 (Gf k r z z' γ)⁻¹) ^ (CPT * (m : ℝ) ^ 2) *
        (max (Gf k r z z' γ) (Gf k r z z' γ)⁻¹ *
          ((ptBlockEnds p).map fun l => (max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹) ^ (2 * (m + 4))).prod) *
        b ^ (Cc * (m : ℝ) ^ 2) ≤ lossV b C m z z' γ p := by
  set G := Gf k r z z' γ with hGdef
  set y := max G G⁻¹ with hy
  have hy1 : 1 ≤ y := one_le_max_self_inv hG
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ hm1
  have hm4 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hb0 : 0 < b := by linarith
  have hP := list_map_prod_le (fun l => (max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹) ^ (2 * (m + 4)))
    (fun l => (max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹) ^ (C * (m : ℝ)))
    (fun l => max_inv_pow_le_rpow _ (norm_nonneg _) m hm C (by linarith)) (ptBlockEnds p)
  have e1 : b ^ (CPT * (m : ℝ) ^ 4) * b ^ (Cc * (m : ℝ) ^ 2) ≤ b ^ (C * (m : ℝ) ^ 4) := by
    rw [← Real.rpow_add hb0]
    apply Real.rpow_le_rpow_of_exponent_le hb
    have h4 : (0 : ℝ) ≤ (m : ℝ) ^ 4 := by positivity
    nlinarith
  have e2 : (max 1 G⁻¹) ^ (CPT * (m : ℝ) ^ 2) * y ≤ y ^ (C * (m : ℝ) ^ 2) := by
    have h1 : max 1 G⁻¹ ≤ y := max_le hy1 (le_max_right _ _)
    have h2 : (max 1 G⁻¹) ^ (CPT * (m : ℝ) ^ 2) ≤ y ^ (CPT * (m : ℝ) ^ 2) :=
      Real.rpow_le_rpow (le_trans zero_le_one (le_max_left _ _)) h1 (by positivity)
    calc (max 1 G⁻¹) ^ (CPT * (m : ℝ) ^ 2) * y ≤ y ^ (CPT * (m : ℝ) ^ 2) * y :=
          mul_le_mul_of_nonneg_right h2 (by linarith)
      _ = y ^ (CPT * (m : ℝ) ^ 2 + 1) := by rw [Real.rpow_add_one (by linarith)]
      _ ≤ y ^ (C * (m : ℝ) ^ 2) := by
          apply Real.rpow_le_rpow_of_exponent_le hy1
          nlinarith
  unfold lossV
  have n1 : 0 ≤ (max 1 G⁻¹) ^ (CPT * (m : ℝ) ^ 2) * y :=
    mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (by linarith)
  have n2 : 0 ≤ b ^ (C * (m : ℝ) ^ 4) := Real.rpow_nonneg hb0.le _
  calc _ = (b ^ (CPT * (m : ℝ) ^ 4) * b ^ (Cc * (m : ℝ) ^ 2)) * ((max 1 G⁻¹) ^ (CPT * (m : ℝ) ^ 2) * y) *
        ((ptBlockEnds p).map fun l => (max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹) ^ (2 * (m + 4))).prod := by ring
    _ ≤ b ^ (C * (m : ℝ) ^ 4) * y ^ (C * (m : ℝ) ^ 2) *
        ((ptBlockEnds p).map fun l => (max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹) ^ (C * (m : ℝ))).prod := by
      apply mul_le_mul (mul_le_mul e1 e2 n1 n2) hP.2 hP.1
      exact mul_nonneg n2 (Real.rpow_nonneg (by linarith) _)

theorem weightStatement_of_section (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A Cn C1 CPT Cc C : ℝ)
    (hW : CellWeightBound D) (hS : Formalism.QuantumDeterminants.SectionExists) (hCn : 0 ≤ Cn) (hPT : 0 ≤ CPT) (hCc : 0 ≤ Cc)
    (hC : CPT + Cc + 6 ≤ C) : VanishingOnXAndXPlusBranching.HodgeTateFromSandwich D large₂ C' Cl Cg cb Cu cT CT C0 A Cn C1 CPT Cc C := by
  intro hA1 hP1 τ w w' hTT θ hθ W hGW S hGS hdeg γ p hRel θ' hθ' νR hν hHyp
  have hH0 : Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 := hHyp.1
  have hGW2 := hGW
  obtain ⟨_, _, hz, hz', hTz, hTz', _⟩ := hGW2
  have hT : 0 < Tr D w := by
    unfold Tr; exact_mod_cast hTT.1.pos
  have hT' : 0 < Tr D w' := by
    unfold Tr; exact_mod_cast hTT.2.1.pos
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hm1 : 2 ≤ D.R.m := D.R.two_le_m
  obtain ⟨μsec, hμ⟩ := hS D.R.k D.R.rS W.z W.z' hk1 hz hz' (by rw [hTz]; exact hT) (by rw [hTz']; exact hT')
  have hl : l1dist (lamD D τ) (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := by
    unfold l1dist; simp; positivity
  have h1 := hA1 hH0 τ w w' hTT θ hθ W hGW (lamD D τ) hl S hGS μsec hμ γ p hRel θ' hθ' νR hν
  have h2 := hP1 hH0 τ w w' hTT θ hθ W hGW S hGS hdeg μsec hμ
  have hG : 0 < Gf D.R.k D.R.rS W.z W.z' γ :=
    cell_G_pos D hRel hz hz' (by rw [hTz]; exact hT) (by rw [hTz']; exact hT')
  obtain ⟨hw0, hw1⟩ := hW W.z W.z' γ p hz hz' (by rw [hTz]; exact hT) (by rw [hTz']; exact hT') hRel
  rw [hTz, hTz'] at hw0 hw1
  set G := Gf D.R.k D.R.rS W.z W.z' γ with hGd
  set X := hsNormSq (S.J νR γ) with hX
  set wt := ptWeight D.R.k D.R.rS (Tr D w) (Tr D w') p with hwt
  set n0 := normalizedLocalScale D w with hn0
  set dim : ℝ := (Module.finrank ℂ W.Wp : ℝ) with hdim
  set ti := (tvPr D τ w' ^ D.R.k)⁻¹ with hti
  set B1 := large₂.sc.b ^ (CPT * (D.R.m : ℝ) ^ 4) * (max 1 G⁻¹) ^ (CPT * (D.R.m : ℝ) ^ 2) with hB1
  set Mx := max G G⁻¹ * ((ptBlockEnds p).map fun l => (max ‖DminN W.z W.z' γ l‖ ‖DminN W.z W.z' γ l‖⁻¹) ^ (2 * (D.R.m + 4))).prod
    with hMx
  have hb := one_le_scale_base large₂
  have hX0 : 0 ≤ X := Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_nonneg _
  have hn00 : 0 ≤ n0 := by rw [hn0]; unfold normalizedLocalScale; exact D.R.k_even.pow_nonneg _
  have hti0 : 0 ≤ ti := inv_nonneg.2 (D.R.k_even.pow_nonneg _)
  have hdim0 : 0 ≤ dim := Nat.cast_nonneg _
  have hB10 : 0 ≤ B1 := mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hbc0 : 0 ≤ large₂.sc.b ^ (Cc * (D.R.m : ℝ) ^ 2) := Real.rpow_nonneg (by linarith) _
  have hMx0 : 0 ≤ Mx := by
    apply mul_nonneg (le_trans hG.le (le_max_left _ _))
    exact (list_map_prod_le _ _ (fun l => ⟨by positivity, le_rfl⟩) _).1
  have key : n0 * (wt * X) ≤ B1 * (dim * ti * large₂.sc.b ^ (Cc * (D.R.m : ℝ) ^ 2)) := by
    rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB10 (mul_nonneg (mul_nonneg hdim0 hti0) hbc0)),
      ENNReal.ofReal_mul hn00, ENNReal.ofReal_mul hB10]
    calc ENNReal.ofReal n0 * ENNReal.ofReal (wt * X)
        ≤ ENNReal.ofReal n0 * (ENNReal.ofReal B1 * MMv D w w' S μsec) := by gcongr
      _ = ENNReal.ofReal B1 * (ENNReal.ofReal n0 * MMv D w w' S μsec) := by ring
      _ ≤ ENNReal.ofReal B1 * ENNReal.ofReal (dim * ti * large₂.sc.b ^ (Cc * (D.R.m : ℝ) ^ 2)) := by gcongr
  have hloss := loss_factor_le_rpow large₂.sc.b CPT Cc C D.R.m W.z W.z' γ p hb hm1 hPT hCc hC hG
  have hloss0 : 0 ≤ lossV large₂.sc.b C D.R.m W.z W.z' γ p := le_trans
    (mul_nonneg (mul_nonneg hB10 hMx0) hbc0) hloss
  rcases eq_or_lt_of_le hdim0 with hd | hd
  · rw [← hd, div_zero]; exact mul_nonneg hloss0 hti0
  · rw [div_le_iff₀ hd]
    calc n0 * G ^ D.R.k * X ≤ n0 * (wt * Mx) * X := by gcongr
      _ = n0 * (wt * X) * Mx := by ring
      _ ≤ B1 * (dim * ti * large₂.sc.b ^ (Cc * (D.R.m : ℝ) ^ 2)) * Mx := by gcongr
      _ = (B1 * Mx * large₂.sc.b ^ (Cc * (D.R.m : ℝ) ^ 2)) * ti * dim := by ring
      _ ≤ lossV large₂.sc.b C D.R.m W.z W.z' γ p * ti * dim := by gcongr

theorem scanl_partial_sums_eq_ends : ∀ (bs : List (ℂ × ℕ)) (a : ℕ),
    (bs.map Prod.snd).scanl (· + ·) a = a :: blockEndsFrom a bs := by
  intro bs
  induction bs with
  | nil => intro a; simp [blockEndsFrom]
  | cons b bs ih =>
    intro a
    obtain ⟨t, s⟩ := b
    rw [List.map_cons, List.scanl_cons, ih (a + s)]
    rfl

theorem block_ends_eq_partial_ends {i : ℕ} (p : Point ℂ i) : ptBlockEnds p = blockEndsFrom 0 p.1 := by
  unfold ptBlockEnds
  rw [scanl_partial_sums_eq_ends]
  rfl

theorem pow_le_max_inv_pow {t : ℝ} (ht : 0 < t) (n : ℕ) : t ^ n ≤ (max t t⁻¹) ^ n :=
  pow_le_pow_left₀ ht.le (le_max_left _ _) n

theorem inv_pow_le_max_inv_pow {t : ℝ} (ht : 0 < t) (n : ℕ) : (t⁻¹) ^ n ≤ (max t t⁻¹) ^ n :=
  pow_le_pow_left₀ (inv_pos.2 ht).le (le_max_right _ _) n

theorem one_le_pow_mul_max_inv_pow {t : ℝ} (ht : 0 < t) {n K : ℕ} (h : n ≤ K) : 1 ≤ t ^ n * (max t t⁻¹) ^ K := by
  have h1 := one_le_max_self_inv ht
  have h2 : (t⁻¹) ^ n ≤ (max t t⁻¹) ^ K := le_trans (inv_pow_le_max_inv_pow ht n) (pow_le_pow_right₀ h1 h)
  calc (1 : ℝ) = t ^ n * (t⁻¹) ^ n := by rw [← mul_pow, mul_inv_cancel₀ ht.ne', one_pow]
    _ ≤ t ^ n * (max t t⁻¹) ^ K := by gcongr

theorem power_change_of_scale_bound (d d' τ F' : ℝ) (E E' e0 s K : ℕ) (hd : 0 < d) (hτ : 0 < τ) (hd' : d' = d * τ) (hF : 0 ≤ F')
    (h1 : E = 2 * e0 + (2 * s + 4)) (h2 : 2 * e0 + 4 = E' + 2 * s) (hK : 2 * s + 4 ≤ K) :
    F' * d' ^ E' ≤ (τ ^ (2 * e0) * F') * d ^ E * (max d' d'⁻¹) ^ K * (max d d⁻¹) ^ K := by
  have hd0 : 0 < d' := by rw [hd']; positivity
  have A : 1 ≤ d ^ (2 * s + 4) * (max d d⁻¹) ^ K := one_le_pow_mul_max_inv_pow hd hK
  have hmu := one_le_max_self_inv hd0
  have B : d' ^ E' ≤ d' ^ (2 * e0) * (max d' d'⁻¹) ^ K := by
    have e : d' ^ E' = d' ^ (2 * e0) * (d' ^ 4 * (d'⁻¹) ^ (2 * s)) := by
      have : d' ^ E' * d' ^ (2 * s) = d' ^ (2 * e0) * d' ^ 4 := by rw [← pow_add, ← pow_add, h2]
      have h3 : d' ^ (2 * s) * (d'⁻¹) ^ (2 * s) = 1 := by rw [← mul_pow, mul_inv_cancel₀ hd0.ne', one_pow]
      calc d' ^ E' = d' ^ E' * (d' ^ (2 * s) * (d'⁻¹) ^ (2 * s)) := by rw [h3, mul_one]
        _ = (d' ^ E' * d' ^ (2 * s)) * (d'⁻¹) ^ (2 * s) := by ring
        _ = _ := by rw [this]; ring
    rw [e]
    have h4 : d' ^ 4 * (d'⁻¹) ^ (2 * s) ≤ (max d' d'⁻¹) ^ K := by
      calc d' ^ 4 * (d'⁻¹) ^ (2 * s) ≤ (max d' d'⁻¹) ^ 4 * (max d' d'⁻¹) ^ (2 * s) :=
            mul_le_mul (pow_le_max_inv_pow hd0 4) (inv_pow_le_max_inv_pow hd0 _) (by positivity) (by positivity)
        _ = (max d' d'⁻¹) ^ (4 + 2 * s) := by rw [pow_add]
        _ ≤ (max d' d'⁻¹) ^ K := pow_le_pow_right₀ hmu (by omega)
    gcongr
  have e2 : (τ ^ (2 * e0) * F') * d ^ E * (max d' d'⁻¹) ^ K * (max d d⁻¹) ^ K =
      F' * (d' ^ (2 * e0) * (max d' d'⁻¹) ^ K) * (d ^ (2 * s + 4) * (max d d⁻¹) ^ K) := by
    rw [h1, pow_add, hd', mul_pow]; ring
  rw [e2]
  have n1 : 0 ≤ F' * (d' ^ (2 * e0) * (max d' d'⁻¹) ^ K) := by positivity
  calc F' * d' ^ E' ≤ F' * (d' ^ (2 * e0) * (max d' d'⁻¹) ^ K) := by gcongr
    _ = F' * (d' ^ (2 * e0) * (max d' d'⁻¹) ^ K) * 1 := by ring
    _ ≤ _ := by gcongr

theorem cell_weight_induction (k r : ℕ) (T T' : ℝ) (δ : ℕ → ℝ) (K : ℕ) (hk : 1 ≤ k) (hK : 2 * (r + 1) + 4 ≤ K)
    (hTT : 0 ≤ T * T') (G : ℝ) (hG : 0 < G) (hGd : G = δ (r + 1) ^ 2 - T * T' * δ r ^ 2) :
    ∀ (bs : List (ℂ × ℕ)) (a : ℕ), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → a + (bs.map Prod.snd).sum = r + 1 →
      MinorModuliChain δ a bs → 0 < δ a →
      0 < ptWeightFrom k r T T' a bs ∧
      G ^ k ≤ ptWeightFrom k r T T' a bs * δ a ^ (2 * (2 * (r + 1 - a) + k)) * max G G⁻¹ *
        (max (δ a) (δ a)⁻¹) ^ K * ((blockEndsFrom a bs).map fun l => (max (δ l) (δ l)⁻¹) ^ (2 * K)).prod := by
  have hy : 1 ≤ max G G⁻¹ := one_le_max_self_inv hG
  intro bs
  induction bs with
  | nil =>
    intro a _ hsum _ hda
    have ha : a = r + 1 := by simpa using hsum
    subst ha
    refine ⟨by simp [ptWeightFrom], ?_⟩
    have h1 : G ≤ δ (r + 1) ^ 2 := by
      rw [hGd]; nlinarith [mul_nonneg hTT (sq_nonneg (δ r))]
    have h2 : G ^ k ≤ δ (r + 1) ^ (2 * k) := by
      rw [pow_mul]; exact pow_le_pow_left₀ hG.le h1 k
    have h3 : 1 ≤ (max (δ (r + 1)) (δ (r + 1))⁻¹) ^ K := one_le_pow₀ (one_le_max_self_inv hda)
    simp only [ptWeightFrom, blockEndsFrom, List.map_nil, List.prod_nil, Nat.sub_self, mul_zero, zero_add, one_mul, mul_one]
    have n0 : 0 ≤ δ (r + 1) ^ (2 * k) := by positivity
    calc G ^ k ≤ δ (r + 1) ^ (2 * k) := h2
      _ = δ (r + 1) ^ (2 * k) * 1 * 1 := by ring
      _ ≤ δ (r + 1) ^ (2 * k) * max G G⁻¹ * (max (δ (r + 1)) (δ (r + 1))⁻¹) ^ K := by gcongr
  | cons b bs ih =>
    intro a hb hsum hch hda
    obtain ⟨t, s⟩ := b
    have ht : t ≠ 0 := (hb (t, s) (List.mem_cons_self)).1
    have hs : 1 ≤ s := (hb (t, s) (List.mem_cons_self)).2
    have hb' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b h => hb b (List.mem_cons_of_mem _ h)
    have hsum' : a + s + (bs.map Prod.snd).sum = r + 1 := by
      simp only [List.map_cons, List.sum_cons] at hsum; omega
    obtain ⟨hc1, hc2⟩ := hch
    have hτ : 0 < ‖t‖ ^ s := pow_pos (norm_pos_iff.2 ht) s
    have hd' : 0 < δ (a + s) := by rw [hc1]; positivity
    obtain ⟨ihp, ihl⟩ := ih (a + s) hb' hsum' hc2 hd'
    have hP0 : 0 ≤ ((blockEndsFrom (a + s) bs).map fun l => (max (δ l) (δ l)⁻¹) ^ (2 * K)).prod :=
      (list_map_prod_le _ _ (fun l => ⟨(even_two_mul K).pow_nonneg _, le_rfl⟩) _).1
    have hmu' := one_le_max_self_inv hd'
    have hmu := one_le_max_self_inv hda
    by_cases hsp : s = 1 ∧ a + 1 = r + 1
    · obtain ⟨hs1, ha⟩ := hsp
      have har : a = r := by omega
      subst hs1
      subst har
      have hnil : bs = [] := by
        cases bs with
        | nil => rfl
        | cons c bs' =>
          have := (hb' c (List.mem_cons_self)).2
          simp only [List.map_cons, List.sum_cons] at hsum'
          omega
      subst hnil
      have hQ : G = δ a ^ 2 * (Complex.normSq t - T * T') := by
        rw [hGd, hc1, Complex.normSq_eq_norm_sq]; ring
      have hd2 : 0 < δ a ^ 2 := by positivity
      have hQ0 : 0 < Complex.normSq t - T * T' := (mul_pos_iff_of_pos_left hd2).1 (hQ ▸ hG)
      have hw : ptWeightFrom k a T T' a [(t, 1)] = (Complex.normSq t - T * T') ^ (k - 1) := by
        simp [ptWeightFrom]
      rw [hw]
      refine ⟨pow_pos hQ0 _, ?_⟩
      have e : 2 * (2 * (a + 1 - a) + k) = 2 * (k - 1) + 6 := by omega
      have e3 : (Complex.normSq t - T * T') ^ (k - 1) * δ a ^ (2 * (k - 1)) = G ^ (k - 1) := by
        rw [hQ, mul_pow, ← pow_mul]; ring
      have e4 : G ^ k = G ^ (k - 1) * G := by
        rw [← pow_succ]; congr 1; omega
      have h6 : 1 ≤ δ a ^ 6 * (max (δ a) (δ a)⁻¹) ^ K := one_le_pow_mul_max_inv_pow hda (by omega)
      have h7 : 1 ≤ (max (δ (a + 1)) (δ (a + 1))⁻¹) ^ (2 * K) := one_le_pow₀ hmu'
      simp only [blockEndsFrom, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [e, pow_add, e4]
      have n1 : 0 ≤ G ^ (k - 1) := by positivity
      calc G ^ (k - 1) * G ≤ G ^ (k - 1) * max G G⁻¹ := by gcongr; exact le_max_left _ _
        _ = G ^ (k - 1) * max G G⁻¹ * 1 * 1 := by ring
        _ ≤ G ^ (k - 1) * max G G⁻¹ * (δ a ^ 6 * (max (δ a) (δ a)⁻¹) ^ K) *
            (max (δ (a + 1)) (δ (a + 1))⁻¹) ^ (2 * K) := by gcongr
        _ = _ := by rw [← e3]; ring
    · simp only [ptWeightFrom, if_neg hsp, blockEndsFrom, List.map_cons, List.prod_cons]
      have hpow : ‖t‖ ^ (2 * s * (Ml k r (a + s) + s - 3)) = (‖t‖ ^ s) ^ (2 * (Ml k r (a + s) + s - 3)) := by
        rw [← pow_mul]; congr 1; ring
      rw [hpow]
      refine ⟨mul_pos (pow_pos hτ _) ihp, ?_⟩
      have hstep := power_change_of_scale_bound (δ a) (δ (a + s)) (‖t‖ ^ s) (ptWeightFrom k r T T' (a + s) bs)
        (2 * (2 * (r + 1 - a) + k)) (2 * (2 * (r + 1 - (a + s)) + k)) (Ml k r (a + s) + s - 3) s K hda hτ hc1 ihp.le
        (by unfold Ml; omega) (by unfold Ml; omega) (by omega)
      have ny : 0 ≤ max G G⁻¹ := by linarith
      calc G ^ k ≤ ptWeightFrom k r T T' (a + s) bs * δ (a + s) ^ (2 * (2 * (r + 1 - (a + s)) + k)) * max G G⁻¹ *
            (max (δ (a + s)) (δ (a + s))⁻¹) ^ K *
            ((blockEndsFrom (a + s) bs).map fun l => (max (δ l) (δ l)⁻¹) ^ (2 * K)).prod := ihl
        _ ≤ ((‖t‖ ^ s) ^ (2 * (Ml k r (a + s) + s - 3)) * ptWeightFrom k r T T' (a + s) bs *
              δ a ^ (2 * (2 * (r + 1 - a) + k)) * (max (δ (a + s)) (δ (a + s))⁻¹) ^ K *
              (max (δ a) (δ a)⁻¹) ^ K) * max G G⁻¹ *
            (max (δ (a + s)) (δ (a + s))⁻¹) ^ K *
            ((blockEndsFrom (a + s) bs).map fun l => (max (δ l) (δ l)⁻¹) ^ (2 * K)).prod := by gcongr
        _ = _ := by rw [two_mul K, pow_add]; ring

section Minors

open Formalism.MainNotions.BesselShellMomentBounds Formalism.HermitianLatticeCounting.ExpansionTerms

theorem minor_chain_of_step (δ : ℕ → ℝ) : ∀ (bs : List (ℂ × ℕ)) (a : ℕ),
    (∀ q (hq : q < bs.length), δ (a + pS bs (q + 1)) = δ (a + pS bs q) * ‖(bs[q]).1‖ ^ (bs[q]).2) →
    MinorModuliChain δ a bs := by
  intro bs
  induction bs with
  | nil => intro a _; trivial
  | cons b bs ih =>
    intro a h
    obtain ⟨t, s⟩ := b
    refine ⟨?_, ih (a + s) (fun q hq => ?_)⟩
    · have := h 0 (by simp)
      simpa [pS] using this
    · have := h (q + 1) (by simpa using hq)
      have e1 : pS ((t, s) :: bs) (q + 1 + 1) = s + pS bs (q + 1) := by simp [pS]
      have e2 : pS ((t, s) :: bs) (q + 1) = s + pS bs q := by simp [pS]
      rw [e1, e2] at this
      simpa [add_assoc] using this

theorem leading_minor_norm_step {d : ℕ} (p : Point ℂ d) (q : ℕ) (hq : q < p.1.length) :
    ‖leadingPrincipalMinor (blockAntidiagonalMatrix (toComp p) (toT p)) (pS p.1 (q + 1))‖ =
      ‖leadingPrincipalMinor (blockAntidiagonalMatrix (toComp p) (toT p)) (pS p.1 q)‖ * ‖(p.1[q]).1‖ ^ (p.1[q]).2 := by
  rw [← sizeUpTo_toComp, ← sizeUpTo_toComp, Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue, Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue]
  have hq' : q < (toComp p).length := by rw [toComp_length]; exact hq
  have hf : (Finset.univ.filter (fun a : Fin (toComp p).length => (a : ℕ) < q + 1)) =
      insert (⟨q, hq'⟩ : Fin (toComp p).length) (Finset.univ.filter (fun a : Fin (toComp p).length => (a : ℕ) < q)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hf, Finset.prod_insert (by simp), norm_mul, mul_comm]
  congr 1
  rw [norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hb : (toComp p).blocksFun ⟨q, hq'⟩ = (p.1[q]).2 := by
    simp [Composition.blocksFun, toComp]
  rw [hb]
  rfl

end Minors

theorem cell_weight_lemma (D : D7) : CellWeightBound D := by
  intro z z' γ p hz hz' hT hT' hRel
  have hG := cell_G_pos D hRel hz hz' hT hT'
  have hδ : ∀ l (hl : l ≤ D.R.rS + 1), ‖DminN z z' γ l‖ =
      ‖Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (Formalism.HermitianLatticeCounting.ExpansionTerms.blockAntidiagonalMatrix (Formalism.MainNotions.BesselShellMomentBounds.toComp p) (Formalism.MainNotions.BesselShellMomentBounds.toT p)) l‖ := by
    intro l hl
    have e : leadMinor (ptMat p) l hl =
        Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (Formalism.HermitianLatticeCounting.ExpansionTerms.blockAntidiagonalMatrix (Formalism.MainNotions.BesselShellMomentBounds.toComp p) (Formalism.MainNotions.BesselShellMomentBounds.toT p)) l := by
      rw [← Formalism.MainNotions.BesselShellMomentBounds.ptMat_eq]
      exact Formalism.MainNotions.BesselShellMomentBounds.leadMinorK_eq _ _ _
    have h := cell_normSq D hRel l hl
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, e] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
  have hle : ∀ q, Formalism.MainNotions.BesselShellMomentBounds.pS p.1 q ≤ D.R.rS + 1 := fun q => (Formalism.MainNotions.BesselShellMomentBounds.toComp p).sizeUpTo_le q
  have hch : MinorModuliChain (fun l => ‖DminN z z' γ l‖) 0 p.1 := by
    apply minor_chain_of_step
    intro q hq
    simp only [zero_add]
    rw [hδ _ (hle _), hδ _ (hle _)]
    exact leading_minor_norm_step p q hq
  have h0 : ‖DminN z z' γ 0‖ = 1 := by
    rw [hδ 0 (Nat.zero_le _)]
    have := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aValue ℂ _ (Formalism.MainNotions.BesselShellMomentBounds.toComp p) (Formalism.MainNotions.BesselShellMomentBounds.toT p) 0
    rw [Composition.sizeUpTo_zero] at this
    rw [this]
    simp
  have a1 : DminN z z' γ (D.R.rS + 1) = Dmin D.R.k D.R.rS z z' γ (Fin.last (D.R.rS + 1)) := by
    unfold DminN; rw [dif_pos (by omega)]; rfl
  have a2 : DminN z z' γ D.R.rS = Dmin D.R.k D.R.rS z z' γ ⟨D.R.rS, by omega⟩ := by
    unfold DminN; rw [dif_pos (by omega)]
  have hGd : Gf D.R.k D.R.rS z z' γ = ‖DminN z z' γ (D.R.rS + 1)‖ ^ 2 -
      Tz D.R.k D.R.rS z * Tz D.R.k D.R.rS z' * ‖DminN z z' γ D.R.rS‖ ^ 2 := by
    rw [a1, a2, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; rfl
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hm : 2 * (D.R.rS + 1) + 4 ≤ D.R.m + 4 := by
    obtain ⟨t, ht⟩ := D.R.m_even
    have h2 := D.R.two_le_m
    simp only [Ranks.rS]
    omega
  obtain ⟨w0, w1⟩ := cell_weight_induction D.R.k D.R.rS (Tz D.R.k D.R.rS z) (Tz D.R.k D.R.rS z')
    (fun l => ‖DminN z z' γ l‖) (D.R.m + 4) hk hm (mul_nonneg hT.le hT'.le) _ hG hGd p.1 0 p.2.1
    (by rw [zero_add]; exact p.2.2) hch (by simp only [h0]; norm_num)
  refine ⟨w0, ?_⟩
  simp only [h0, one_pow, inv_one, max_self, mul_one] at w1
  rw [block_ends_eq_partial_ends, ← mul_assoc]
  exact w1

theorem weight_admissible_mono (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 C C₂ : ℝ) (h : C ≤ C₂)
    (hA : VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C) : VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C₂ := by
  intro hH τ w w' hTT θ hθ W hGW lam' hl S hGS μsec hμ γ p hRel θ' hθ' νR hν
  refine le_trans (hA hH τ w w' hTT θ hθ W hGW lam' hl S hGS μsec hμ γ p hRel θ' hθ' νR hν) ?_
  have hb := one_le_scale_base large₂
  have h1 : large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 4) ≤ large₂.sc.b ^ (C₂ * (D.R.m : ℝ) ^ 4) :=
    Real.rpow_le_rpow_of_exponent_le hb (by gcongr)
  have h2 : (max 1 (Gf D.R.k D.R.rS W.z W.z' γ)⁻¹) ^ (C * (D.R.m : ℝ) ^ 2) ≤
      (max 1 (Gf D.R.k D.R.rS W.z W.z' γ)⁻¹) ^ (C₂ * (D.R.m : ℝ) ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by gcongr)
  gcongr

theorem constant_bound_mono (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 C C₂ : ℝ) (h : C ≤ C₂)
    (hA : VanishingOnXAndXPlusBranching.Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 C1 C) : VanishingOnXAndXPlusBranching.Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 C1 C₂ := by
  intro hH τ w w' hTT θ hθ W hGW S hGS hdeg μsec hμ
  refine le_trans (hA hH τ w w' hTT θ hθ W hGW S hGS hdeg μsec hμ) ?_
  have hb := one_le_scale_base large₂
  have h1 : large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2) ≤ large₂.sc.b ^ (C₂ * (D.R.m : ℝ) ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le hb (by gcongr)
  have hti0 : 0 ≤ (tvPr D τ w' ^ D.R.k)⁻¹ := inv_nonneg.2 (D.R.k_even.pow_nonneg _)
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left h1 (mul_nonneg (Nat.cast_nonneg _) hti0)

theorem weightStatement_holds (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A Cn C1 CPT Cc C : ℝ) (hCn : 0 ≤ Cn)
    (hC : max CPT 0 + max Cc 0 + 6 ≤ C) : VanishingOnXAndXPlusBranching.HodgeTateFromSandwich D large₂ C' Cl Cg cb Cu cT CT C0 A Cn C1 CPT Cc C :=
  fun hA1 hP1 => weightStatement_of_section D large₂ C' Cl Cg cb Cu cT CT C0 A Cn C1 (max CPT 0) (max Cc 0) C (cell_weight_lemma D)
    Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists hCn (le_max_right _ _) (le_max_right _ _) hC
    (weight_admissible_mono D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT _ (le_max_left _ _) hA1)
    (constant_bound_mono D large₂ C' Cl Cg cb Cu cT CT C0 C1 Cc _ (le_max_left _ _) hP1)

end Formalism.MainNotions.BridgeLemma

end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Finset

section Abs

variable {ι : Type}

theorem one_le_finset_prod (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  Finset.prod_induction f (fun x => 1 ≤ x) (fun _ _ ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl h

theorem single_le_finset_prod (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) (a : ι) (ha : a ∈ s) :
    f a ≤ ∏ i ∈ s, f i := by
  classical
  rw [← Finset.mul_prod_erase s f ha]
  have h1 : 1 ≤ ∏ i ∈ s.erase a, f i := one_le_finset_prod _ _ (fun i hi => h i (Finset.mem_of_mem_erase hi))
  have h0 : 0 ≤ f a := le_trans zero_le_one (h a ha)
  nlinarith

theorem finset_prod_list_prod_comm (P : Finset ι) (E : List ℕ) (f : ι → ℕ → ℝ) :
    ∏ v ∈ P, (E.map (f v)).prod = (E.map (fun l => ∏ v ∈ P, f v l)).prod := by
  induction E with
  | nil => simp
  | cons a E ih => simp only [List.map_cons, List.prod_cons, Finset.prod_mul_distrib, ih]

theorem list_prod_le_pow_length_local (E : List ℕ) (g : ℕ → ℝ) (X : ℝ) (h0 : ∀ l ∈ E, 0 ≤ g l) (h : ∀ l ∈ E, g l ≤ X) :
    (E.map g).prod ≤ X ^ E.length := by
  induction E with
  | nil => simp
  | cons a E ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    have ha0 := h0 a (by simp)
    have ha := h a (by simp)
    have hp : 0 ≤ (E.map g).prod := List.prod_nonneg (by
      intro x hx
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact h0 l (by simp [hl]))
    exact mul_le_mul ha (ih (fun l hl => h0 l (by simp [hl])) (fun l hl => h l (by simp [hl]))) hp (le_trans ha0 ha)

theorem foldr_max_le_list_prod (E : List ℕ) (g : ℕ → ℝ) (h : ∀ l ∈ E, 1 ≤ g l) :
    (E.map g).foldr max 1 ≤ (E.map g).prod ∧ 1 ≤ (E.map g).prod ∧ 1 ≤ (E.map g).foldr max 1 := by
  induction E with
  | nil => simp
  | cons a E ih =>
    obtain ⟨i1, i2, i3⟩ := ih (fun l hl => h l (by simp [hl]))
    have ha := h a (by simp)
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    refine ⟨max_le (by nlinarith) (by nlinarith), by nlinarith, le_trans ha (le_max_left _ _)⟩

variable [Fintype ι]

theorem loss_abs_product_bound (P : Finset ι) (E : List ℕ) (G : ι → ℝ) (Dn : ι → ℕ → ℝ) (X B c1 c2 : ℝ)
    (hB : 1 ≤ B) (hX : 1 ≤ X) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hG : ∀ v, 0 < G v) (hGp : 1 ≤ ∏ v, G v) (hGX : ∏ v, max 1 (G v) ≤ X ^ 2)
    (hD : ∀ l ∈ E, ∀ v, 0 < Dn v l) (hDp : ∀ l ∈ E, 1 ≤ ∏ v, Dn v l)
    (hDX : ∀ l ∈ E, ∏ v, max 1 (Dn v l) ≤ X) :
    ∏ v ∈ P, (B * (max (G v) (G v)⁻¹) ^ c1 * (E.map (fun l => (max (Dn v l) (Dn v l)⁻¹) ^ c2)).prod) ≤
      B ^ Fintype.card ι * (X ^ 4) ^ c1 * ((X ^ 2) ^ c2) ^ E.length := by
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]
  have hMG0 : ∀ v, 0 ≤ max (G v) (G v)⁻¹ := fun v => le_trans (hG v).le (le_max_left _ _)
  have e1 : B ^ P.card ≤ B ^ Fintype.card ι := pow_le_pow_right₀ hB (Finset.card_le_univ P)
  have e2 : ∏ v ∈ P, (max (G v) (G v)⁻¹) ^ c1 ≤ (X ^ 4) ^ c1 := by
    rw [Real.finsetProd_rpow P _ (fun v _ => hMG0 v)]
    apply Real.rpow_le_rpow (Finset.prod_nonneg (fun v _ => hMG0 v)) _ hc1
    have h := (Formalism.HermitianLatticeCounting.P.prodMaxInvLeSq ι G P hG hGp).1
    simp only [one_div] at h
    refine le_trans h ?_
    calc (∏ v, max 1 (G v)) ^ 2 ≤ (X ^ 2) ^ 2 :=
          pow_le_pow_left₀ (Finset.prod_nonneg (fun v _ => le_trans zero_le_one (le_max_left _ _))) hGX 2
      _ = X ^ 4 := by ring
  have e3 : ∏ v ∈ P, (E.map (fun l => (max (Dn v l) (Dn v l)⁻¹) ^ c2)).prod ≤ ((X ^ 2) ^ c2) ^ E.length := by
    rw [finset_prod_list_prod_comm P E (fun v l => (max (Dn v l) (Dn v l)⁻¹) ^ c2)]
    apply list_prod_le_pow_length_local
    · intro l hl
      exact Finset.prod_nonneg (fun v _ => Real.rpow_nonneg (le_trans (hD l hl v).le (le_max_left _ _)) _)
    · intro l hl
      have hM0 : ∀ v, 0 ≤ max (Dn v l) (Dn v l)⁻¹ := fun v => le_trans (hD l hl v).le (le_max_left _ _)
      rw [Real.finsetProd_rpow P _ (fun v _ => hM0 v)]
      apply Real.rpow_le_rpow (Finset.prod_nonneg (fun v _ => hM0 v)) _ hc2
      have h := (Formalism.HermitianLatticeCounting.P.prodMaxInvLeSq ι (fun v => Dn v l) P (hD l hl) (hDp l hl)).1
      simp only [one_div] at h
      exact le_trans h (pow_le_pow_left₀
        (Finset.prod_nonneg (fun v _ => le_trans zero_le_one (le_max_left _ _))) (hDX l hl) 2)
  have p1 : 0 ≤ ∏ v ∈ P, (max (G v) (G v)⁻¹) ^ c1 := Finset.prod_nonneg (fun v _ => Real.rpow_nonneg (hMG0 v) _)
  have p2 : 0 ≤ B ^ Fintype.card ι := by positivity
  have p5 : 0 ≤ (X ^ 4) ^ c1 := by positivity
  have p6 : 0 ≤ ∏ v ∈ P, (E.map (fun l => (max (Dn v l) (Dn v l)⁻¹) ^ c2)).prod :=
    Finset.prod_nonneg (fun v _ => List.prod_nonneg (by
      intro x hx
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact Real.rpow_nonneg (le_trans (hD l hl v).le (le_max_left _ _)) _))
  exact mul_le_mul (mul_le_mul e1 e2 p1 p2) e3 p6 (mul_nonneg p2 p5)

theorem loss_product_abs_bound (P : Finset ι) (E : List ℕ) (Dn : ι → ℕ → ℝ) (X B e : ℝ)
    (hB : 1 ≤ B) (he : 0 ≤ e)
    (hD : ∀ l ∈ E, ∀ v, 0 < Dn v l) (hDp : ∀ l ∈ E, 1 ≤ ∏ v, Dn v l)
    (hDX : ∀ l ∈ E, ∏ v, max 1 (Dn v l) ≤ X) :
    ∏ v ∈ P, (B * (E.map (fun l => max 1 (Dn v l)⁻¹)).foldr max 1) ^ e ≤
      (B ^ Fintype.card ι * X ^ E.length) ^ e := by
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hf : ∀ v, (E.map (fun l => max 1 (Dn v l)⁻¹)).foldr max 1 ≤ (E.map (fun l => max 1 (Dn v l)⁻¹)).prod ∧
      1 ≤ (E.map (fun l => max 1 (Dn v l)⁻¹)).prod ∧ 1 ≤ (E.map (fun l => max 1 (Dn v l)⁻¹)).foldr max 1 :=
    fun v => foldr_max_le_list_prod E (fun l => max 1 (Dn v l)⁻¹) (fun l _ => le_max_left _ _)
  have h0 : ∀ v, 0 ≤ B * (E.map (fun l => max 1 (Dn v l)⁻¹)).foldr max 1 :=
    fun v => mul_nonneg hB0 (le_trans zero_le_one (hf v).2.2)
  rw [Real.finsetProd_rpow P _ (fun v _ => h0 v)]
  apply Real.rpow_le_rpow (Finset.prod_nonneg (fun v _ => h0 v)) _ he
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  have e1 : B ^ P.card ≤ B ^ Fintype.card ι := pow_le_pow_right₀ hB (Finset.card_le_univ P)
  have e2 : ∏ v ∈ P, (E.map (fun l => max 1 (Dn v l)⁻¹)).foldr max 1 ≤ X ^ E.length := by
    refine le_trans (Finset.prod_le_prod (fun v _ => le_trans zero_le_one (hf v).2.2) (fun v _ => (hf v).1)) ?_
    rw [finset_prod_list_prod_comm P E (fun v l => max 1 (Dn v l)⁻¹)]
    apply list_prod_le_pow_length_local
    · intro l _
      exact Finset.prod_nonneg (fun v _ => le_trans zero_le_one (le_max_left _ _))
    · intro l hl
      have h := (Formalism.HermitianLatticeCounting.P.prodMaxInvLeSq ι (fun v => Dn v l) P (hD l hl) (hDp l hl)).2
      simp only [one_div] at h
      exact le_trans h (hDX l hl)
  exact mul_le_mul e1 e2 (Finset.prod_nonneg (fun v _ => le_trans zero_le_one (hf v).2.2)) (by positivity)

end Abs

section Rec

variable (D : D7) (large₂ : SizeData₂ D)

theorem log_scale_nonneg : 0 ≤ large₂.sc.L := by
  unfold Scale.L
  exact Real.rpow_nonneg (le_trans zero_le_one large₂.sc.one_lt_alt.le) _

theorem scale_base_rpow_eq_exp (y : ℝ) : large₂.sc.b ^ y = Real.exp (large₂.sc.L * y) := by
  unfold Scale.b
  rw [Real.exp_mul]

theorem log_scale_base_eq : Real.log large₂.sc.b = large₂.sc.L := by
  unfold Scale.b
  rw [Real.log_exp]

theorem window_radius_pos (w : D.what₂.Word) : 0 < Tr D w := by
  unfold Tr
  exact_mod_cast (D.mem w).A.T_prime.pos

theorem block_ends_length_le {r : ℕ} (p : Point ℂ (r + 1)) : (ptBlockEnds p).length ≤ r + 1 := by
  unfold ptBlockEnds
  rw [List.length_tail, List.length_scanl, Nat.add_sub_cancel, List.length_map]
  have h := List.length_le_sum_of_one_le (p.1.map Prod.snd) (by
    intro i hi
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hi
    exact (p.2.1 b hb).2)
  rw [List.length_map, p.2.2] at h
  exact h

theorem rank_parameters_le : (D.R.rS : ℝ) ≤ D.R.m ∧ ((D.R.rS + 1 : ℕ) : ℝ) ≤ D.R.m ∧ (1 : ℝ) ≤ D.R.m := by
  have h2 := D.R.two_le_m
  have e : D.R.rS = D.R.m / 2 - 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast (by omega : D.R.rS ≤ D.R.m)
  · exact_mod_cast (by omega : D.R.rS + 1 ≤ D.R.m)
  · exact_mod_cast (by omega : 1 ≤ D.R.m)

theorem one_le_size_volume {k r : ℕ} (H : ℝ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) : 1 ≤ sizeV H z z' γ :=
  one_le_finset_prod _ _ (fun _ _ => le_max_left _ _)

theorem minor_factor_le_size_volume {k r : ℕ} (H : ℝ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) (l : ℕ) :
    max 1 (‖DminN z z' γ l‖ / H) ≤ sizeV H z z' γ := by
  unfold DminN
  by_cases h : l < r + 2
  · rw [dif_pos h]
    exact single_le_finset_prod Finset.univ (fun l : Fin (r + 2) => max 1 (‖Dmin k r z z' γ l‖ / H))
      (fun _ _ => le_max_left _ _) ⟨l, h⟩ (Finset.mem_univ _)
  · rw [dif_neg h]
    simp only [norm_zero, zero_div]
    rw [max_eq_left zero_le_one]
    exact one_le_size_volume H z z' γ

variable {D}

theorem prod_minor_max_le_height_size (H : ℝ) (hH : 1 ≤ H) (zs zs' : D.what₂.Tau → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (γs : D.what₂.Tau → MatKR D.R.k D.R.rS) (l : ℕ) :
    ∏ τ, max 1 ‖DminN (zs τ) (zs' τ) (γs τ) l‖ ≤ H ^ D.R.f * ∏ τ, sizeV H (zs τ) (zs' τ) (γs τ) := by
  have h := Formalism.HermitianLatticeCounting.P.prodMaxLeProdMaxDiv D.what₂.Tau (fun τ => ‖DminN (zs τ) (zs' τ) (γs τ) l‖) H hH
    (fun _ => norm_nonneg _)
  rw [D.what₂.card_Tau] at h
  refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Finset.prod_le_prod (fun _ _ => le_trans zero_le_one (le_max_left _ _))
    (fun τ _ => minor_factor_le_size_volume H _ _ _ l)

theorem term_points_setup (H : ℝ) (hH : 1 ≤ H) {w w' : D.what₂.Word}
    {zs zs' : D.what₂.Tau → Fin (2 * D.R.rS + D.R.k + 1) → ℂ} {γs : D.what₂.Tau → MatKR D.R.k D.R.rS}
    {ps : D.what₂.Tau → Point ℂ (D.R.rS + 1)} (h : TermPts D w w' zs zs' γs ps) (τ₀ : D.what₂.Tau) :
    (∀ τ, 0 < Gf D.R.k D.R.rS (zs τ) (zs' τ) (γs τ)) ∧
    ∏ τ, max 1 (Gf D.R.k D.R.rS (zs τ) (zs' τ) (γs τ)) ≤
      (H ^ D.R.f * ∏ τ, sizeV H (zs τ) (zs' τ) (γs τ)) ^ 2 ∧
    (∀ l ∈ ptBlockEnds (ps τ₀), ∀ τ, 0 < ‖DminN (zs τ) (zs' τ) (γs τ) l‖) ∧
    (∀ l ∈ ptBlockEnds (ps τ₀), 1 ≤ ∏ τ, ‖DminN (zs τ) (zs' τ) (γs τ) l‖) := by
  obtain ⟨h1, _, _, h4⟩ := h
  have hG : ∀ τ, 0 < Gf D.R.k D.R.rS (zs τ) (zs' τ) (γs τ) := by
    intro τ
    obtain ⟨a1, a2, a3, a4, a5⟩ := h1 τ
    have := Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS (zs τ) (zs' τ) a1 a2 (by rw [a3]; exact window_radius_pos D w)
      (by rw [a4]; exact window_radius_pos D w') (γs τ) a5.1
    exact lt_of_le_of_ne this (Ne.symm a5.2.2)
  refine ⟨hG, ?_, ?_, ?_⟩
  · have hle : ∀ τ, max 1 (Gf D.R.k D.R.rS (zs τ) (zs' τ) (γs τ)) ≤
        (max 1 ‖DminN (zs τ) (zs' τ) (γs τ) (D.R.rS + 1)‖) ^ 2 := by
      intro τ
      obtain ⟨a1, a2, a3, a4, a5⟩ := h1 τ
      have e : DminN (zs τ) (zs' τ) (γs τ) (D.R.rS + 1) =
          Dmin D.R.k D.R.rS (zs τ) (zs' τ) (γs τ) (Fin.last (D.R.rS + 1)) := by
        unfold DminN
        rw [dif_pos (by omega)]
        rfl
      have g1 : Gf D.R.k D.R.rS (zs τ) (zs' τ) (γs τ) ≤ ‖DminN (zs τ) (zs' τ) (γs τ) (D.R.rS + 1)‖ ^ 2 := by
        rw [e, ← Complex.normSq_eq_norm_sq]
        unfold Gf
        have : 0 ≤ Tz D.R.k D.R.rS (zs τ) * Tz D.R.k D.R.rS (zs' τ) *
            Complex.normSq (Dmin D.R.k D.R.rS (zs τ) (zs' τ) (γs τ) ⟨D.R.rS, by omega⟩) := by
          rw [a3, a4]
          exact mul_nonneg (mul_nonneg (window_radius_pos D w).le (window_radius_pos D w').le) (Complex.normSq_nonneg _)
        linarith
      have m1 : (1 : ℝ) ≤ max 1 ‖DminN (zs τ) (zs' τ) (γs τ) (D.R.rS + 1)‖ := le_max_left _ _
      have m2 : ‖DminN (zs τ) (zs' τ) (γs τ) (D.R.rS + 1)‖ ≤ max 1 ‖DminN (zs τ) (zs' τ) (γs τ) (D.R.rS + 1)‖ :=
        le_max_right _ _
      refine max_le (by nlinarith) (le_trans g1 (pow_le_pow_left₀ (norm_nonneg _) m2 2))
    refine le_trans (Finset.prod_le_prod (fun _ _ => le_trans zero_le_one (le_max_left _ _)) (fun τ _ => hle τ)) ?_
    rw [Finset.prod_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg (fun _ _ => le_trans zero_le_one (le_max_left _ _)))
      (prod_minor_max_le_height_size H hH zs zs' γs _) 2
  · intro l hl τ
    have hp := h4 τ₀ l hl
    rcases (norm_nonneg (DminN (zs τ) (zs' τ) (γs τ) l)).lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [← h0]; norm_num)] at hp
      linarith
  · intro l hl
    have hp := h4 τ₀ l hl
    rw [Finset.prod_pow] at hp
    have h0 : 0 ≤ ∏ τ, ‖DminN (zs τ) (zs' τ) (γs τ) l‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
    by_contra hc
    have hc' := not_le.1 hc
    nlinarith

end Rec

section Main

variable (D : D7) (large₂ : SizeData₂ D)

theorem heightStatement_of_bounds (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (h62 : 6 * C ≤ C2)
    (hm : C + 6 * C * Ch ≤ large₂.CGam * D.R.m) : VanishingOnXAndXPlusBranching.TowerRallisLemma D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch := by
  intro w w' zs zs' γs ps hT _ P
  have hL := log_scale_nonneg D large₂
  obtain ⟨hr1, hr2, hm1⟩ := rank_parameters_le D
  have hm0 : (0 : ℝ) ≤ D.R.m := le_trans zero_le_one hm1
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hH : 1 ≤ scalePowQuadraticExponent D large₂ Ch := by
    unfold scalePowQuadraticExponent
    rw [scale_base_rpow_eq_exp]
    exact Real.one_le_exp (by positivity)
  set S : ℝ := ∏ τ, sizeV (scalePowQuadraticExponent D large₂ Ch) (zs τ) (zs' τ) (γs τ) with hS
  have hS1 : 1 ≤ S := one_le_finset_prod _ _ (fun τ _ => one_le_size_volume _ _ _ _)
  have hS0 : 0 < S := lt_of_lt_of_le one_pos hS1
  have hs0 : 0 ≤ Real.log S := Real.log_nonneg hS1
  have hSe : S = Real.exp (Real.log S) := (Real.exp_log hS0).symm
  have hR1 : 1 ≤ GamS D large₂ * S ^ (C2 * (D.R.m : ℝ) ^ 2) := by
    have g1 : 1 ≤ GamS D large₂ := by
      unfold GamS
      exact Real.one_le_exp (by have := large₂.CGam_pos.le; positivity)
    have g2 : 1 ≤ S ^ (C2 * (D.R.m : ℝ) ^ 2) :=
      Real.one_le_rpow hS1 (mul_nonneg (by linarith) (by positivity))
    exact one_le_mul_of_one_le_of_one_le g1 g2
  rcases P.eq_empty_or_nonempty with rfl | ⟨τ₀, _⟩
  · simpa using hR1
  obtain ⟨s1, s2, s3, s4⟩ := term_points_setup (scalePowQuadraticExponent D large₂ Ch) hH hT τ₀
  have hX1 : 1 ≤ scalePowQuadraticExponent D large₂ Ch ^ D.R.f * S := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hH) hS1
  have hB : 1 ≤ large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 4) := by
    rw [scale_base_rpow_eq_exp]
    exact Real.one_le_exp (by positivity)
  have key := loss_abs_product_bound P (ptBlockEnds (ps τ₀)) (fun τ => Gf D.R.k D.R.rS (zs τ) (zs' τ) (γs τ))
    (fun τ l => ‖DminN (zs τ) (zs' τ) (γs τ) l‖) (scalePowQuadraticExponent D large₂ Ch ^ D.R.f * S) (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 4))
    (C * (D.R.m : ℝ) ^ 2) (C * (D.R.m : ℝ)) hB hX1 (by positivity) (by positivity) s1 hT.2.2.1 s2 s3 s4
    (fun l _ => prod_minor_max_le_height_size _ hH zs zs' γs l)
  have e0 : ∏ τ ∈ P, lossV large₂.sc.b C D.R.m (zs τ) (zs' τ) (γs τ) (ps τ) =
      ∏ τ ∈ P, (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 4) *
        (max (Gf D.R.k D.R.rS (zs τ) (zs' τ) (γs τ)) (Gf D.R.k D.R.rS (zs τ) (zs' τ) (γs τ))⁻¹) ^
          (C * (D.R.m : ℝ) ^ 2) *
        ((ptBlockEnds (ps τ₀)).map (fun l => (max ‖DminN (zs τ) (zs' τ) (γs τ) l‖
          ‖DminN (zs τ) (zs' τ) (γs τ) l‖⁻¹) ^ (C * (D.R.m : ℝ)))).prod) := by
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    unfold lossV
    rw [hT.2.1 τ τ₀]
  rw [e0]
  refine le_trans key ?_
  rw [D.what₂.card_Tau]
  set len : ℕ := (ptBlockEnds (ps τ₀)).length with hlen
  have hlen' : (len : ℝ) ≤ D.R.m := le_trans (by exact_mod_cast block_ends_length_le (ps τ₀)) hr2
  set ξ : ℝ := (D.R.f : ℝ) * (large₂.sc.L * (Ch * (D.R.m : ℝ) ^ 2)) + Real.log S with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  have hXe : scalePowQuadraticExponent D large₂ Ch ^ D.R.f * S = Real.exp ξ := by
    unfold scalePowQuadraticExponent
    rw [scale_base_rpow_eq_exp, ← Real.exp_nat_mul, hξ, Real.exp_add, ← hSe]
  rw [hXe, scale_base_rpow_eq_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_mul,
    ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  unfold GamS
  conv_rhs => rw [hSe, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.2
  push_cast
  have a1 : (len : ℝ) * (2 * ξ * (C * (D.R.m : ℝ))) ≤ (D.R.m : ℝ) * (2 * ξ * (C * (D.R.m : ℝ))) :=
    mul_le_mul_of_nonneg_right hlen' (by positivity)
  have a2 : (D.R.m : ℝ) ^ 4 * D.R.f * large₂.sc.L * (C + 6 * C * Ch) ≤
      (D.R.m : ℝ) ^ 4 * D.R.f * large₂.sc.L * (large₂.CGam * D.R.m) := mul_le_mul_of_nonneg_left hm (by positivity)
  have a3 : (D.R.m : ℝ) ^ 2 * Real.log S * (6 * C) ≤ (D.R.m : ℝ) ^ 2 * Real.log S * C2 :=
    mul_le_mul_of_nonneg_left h62 (by positivity)
  have a4 : (D.R.f : ℝ) * (large₂.sc.L * (C * (D.R.m : ℝ) ^ 4)) + 4 * ξ * (C * (D.R.m : ℝ) ^ 2) +
      (D.R.m : ℝ) * (2 * ξ * (C * (D.R.m : ℝ))) =
      (D.R.m : ℝ) ^ 4 * D.R.f * large₂.sc.L * (C + 6 * C * Ch) + (D.R.m : ℝ) ^ 2 * Real.log S * (6 * C) := by
    rw [hξ]; ring
  have a5 : large₂.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L + Real.log S * (C2 * (D.R.m : ℝ) ^ 2) =
      (D.R.m : ℝ) ^ 4 * D.R.f * large₂.sc.L * (large₂.CGam * D.R.m) + (D.R.m : ℝ) ^ 2 * Real.log S * C2 := by ring
  linarith

theorem product_clause_at_record (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (h12 : C ≤ C2)
    (h22 : C ^ 2 + C * Ch ≤ C2) : VanishingOnXAndXPlusBranching.GGFromIrreducibility D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch := by
  intro w w' zs zs' γs ps hT _ P
  have hL := log_scale_nonneg D large₂
  obtain ⟨hr1, hr2, hm1⟩ := rank_parameters_le D
  have hm0 : (0 : ℝ) ≤ D.R.m := le_trans zero_le_one hm1
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have hC2 : 0 ≤ C2 := le_trans hC h12
  have hH : 1 ≤ scalePowQuadraticExponent D large₂ Ch := by
    unfold scalePowQuadraticExponent
    rw [scale_base_rpow_eq_exp]
    exact Real.one_le_exp (by positivity)
  set S : ℝ := ∏ τ, sizeV (scalePowQuadraticExponent D large₂ Ch) (zs τ) (zs' τ) (γs τ) with hS
  have hS1 : 1 ≤ S := one_le_finset_prod _ _ (fun τ _ => one_le_size_volume _ _ _ _)
  have hS0 : 0 < S := lt_of_lt_of_le one_pos hS1
  have hs0 : 0 ≤ Real.log S := Real.log_nonneg hS1
  have hSe : S = Real.exp (Real.log S) := (Real.exp_log hS0).symm
  rw [log_scale_base_eq]
  have hR1 : 1 ≤ Real.exp (C2 * (D.R.m : ℝ) ^ 6 * D.R.f * large₂.sc.L) * S ^ (C2 * (D.R.m : ℝ) ^ 4) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) (Real.one_le_rpow hS1 (by positivity))
  rcases P.eq_empty_or_nonempty with rfl | ⟨τ₀, _⟩
  · simpa using hR1
  obtain ⟨_, _, s3, s4⟩ := term_points_setup (scalePowQuadraticExponent D large₂ Ch) hH hT τ₀
  have hB : 1 ≤ large₂.sc.b ^ (C * (D.R.m : ℝ)) := by
    rw [scale_base_rpow_eq_exp]
    exact Real.one_le_exp (by positivity)
  have key := loss_product_abs_bound P (ptBlockEnds (ps τ₀))
    (fun τ l => ‖DminN (zs τ) (zs' τ) (γs τ) l‖) (scalePowQuadraticExponent D large₂ Ch ^ D.R.f * S) (large₂.sc.b ^ (C * (D.R.m : ℝ)))
    (C * (D.R.rS : ℝ) ^ 3) hB (by positivity) s3 s4 (fun l _ => prod_minor_max_le_height_size _ hH zs zs' γs l)
  have e0 : ∏ τ ∈ P, lossP large₂.sc.b C D.R.m (zs τ) (zs' τ) (γs τ) (ps τ) =
      ∏ τ ∈ P, (large₂.sc.b ^ (C * (D.R.m : ℝ)) *
        ((ptBlockEnds (ps τ₀)).map (fun l => max 1 ‖DminN (zs τ) (zs' τ) (γs τ) l‖⁻¹)).foldr max 1) ^
          (C * (D.R.rS : ℝ) ^ 3) := by
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    unfold lossP
    rw [hT.2.1 τ τ₀]
  rw [e0]
  refine le_trans key ?_
  rw [D.what₂.card_Tau]
  set len : ℕ := (ptBlockEnds (ps τ₀)).length with hlen
  have hlen' : (len : ℝ) ≤ D.R.m := le_trans (by exact_mod_cast block_ends_length_le (ps τ₀)) hr2
  set ξ : ℝ := (D.R.f : ℝ) * (large₂.sc.L * (Ch * (D.R.m : ℝ) ^ 2)) + Real.log S with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  have hXe : scalePowQuadraticExponent D large₂ Ch ^ D.R.f * S = Real.exp ξ := by
    unfold scalePowQuadraticExponent
    rw [scale_base_rpow_eq_exp, ← Real.exp_nat_mul, hξ, Real.exp_add, ← hSe]
  rw [hXe, scale_base_rpow_eq_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_mul]
  conv_rhs => rw [hSe, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have b1 : (D.R.rS : ℝ) ^ 3 ≤ (D.R.m : ℝ) ^ 3 := pow_le_pow_left₀ hr0 hr1 3
  have b2 : (len : ℝ) * ξ ≤ (D.R.m : ℝ) * ξ := mul_le_mul_of_nonneg_right hlen' hξ0
  have b3 : ((D.R.f : ℝ) * (large₂.sc.L * (C * (D.R.m : ℝ))) + (len : ℝ) * ξ) * (C * (D.R.rS : ℝ) ^ 3) ≤
      ((D.R.f : ℝ) * (large₂.sc.L * (C * (D.R.m : ℝ))) + (D.R.m : ℝ) * ξ) * (C * (D.R.m : ℝ) ^ 3) := by
    apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left b1 hC) (by positivity) (by positivity)
  have b4 : (D.R.m : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 6 := pow_le_pow_right₀ hm1 (by norm_num)
  have b5 : C ^ 2 * (D.R.f * large₂.sc.L) * (D.R.m : ℝ) ^ 4 ≤ C ^ 2 * (D.R.f * large₂.sc.L) * (D.R.m : ℝ) ^ 6 :=
    mul_le_mul_of_nonneg_left b4 (by positivity)
  have b6 : (D.R.m : ℝ) ^ 6 * (D.R.f * large₂.sc.L) * (C ^ 2 + C * Ch) ≤ (D.R.m : ℝ) ^ 6 * (D.R.f * large₂.sc.L) * C2 :=
    mul_le_mul_of_nonneg_left h22 (by positivity)
  have b7 : (D.R.m : ℝ) ^ 4 * Real.log S * C ≤ (D.R.m : ℝ) ^ 4 * Real.log S * C2 :=
    mul_le_mul_of_nonneg_left h12 (by positivity)
  have b8 : ((D.R.f : ℝ) * (large₂.sc.L * (C * (D.R.m : ℝ))) + (D.R.m : ℝ) * ξ) * (C * (D.R.m : ℝ) ^ 3) =
      C ^ 2 * (D.R.f * large₂.sc.L) * (D.R.m : ℝ) ^ 4 + (D.R.m : ℝ) ^ 6 * (D.R.f * large₂.sc.L) * (C * Ch) +
        (D.R.m : ℝ) ^ 4 * Real.log S * C := by
    rw [hξ]; ring
  have b9 : C2 * (D.R.m : ℝ) ^ 6 * D.R.f * large₂.sc.L + Real.log S * (C2 * (D.R.m : ℝ) ^ 4) =
      (D.R.m : ℝ) ^ 6 * (D.R.f * large₂.sc.L) * C2 + (D.R.m : ℝ) ^ 4 * Real.log S * C2 := by ring
  have b10 : (D.R.m : ℝ) ^ 6 * (D.R.f * large₂.sc.L) * (C ^ 2 + C * Ch) =
      C ^ 2 * (D.R.f * large₂.sc.L) * (D.R.m : ℝ) ^ 6 + (D.R.m : ℝ) ^ 6 * (D.R.f * large₂.sc.L) * (C * Ch) := by ring
  linarith

end Main

section Fam

variable {eps : ℝ} (Fm : FamP eps)

theorem family_third_fifth_items (Cg cb Cu cT CT C0 A C C2 Ch : ℝ) (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (h62 : 6 * C ≤ C2)
    (h22 : C ^ 2 + C * Ch ≤ C2) :
    OwnEv Fm fun C' Cl x i =>
      VanishingOnXAndXPlusBranching.PointsLemma (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C C2 Ch ∧
        VanishingOnXAndXPlusBranching.Conclusion5 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C C2 Ch := by
  obtain ⟨x0, _, h⟩ := ev_m Fm ((C + 6 * C * Ch) / Fm.CGam)
  refine ownEv_intro Fm x0 (fun x hx _ i => ?_)
  have hG : (Fm.L x i).CGam = Fm.CGam := Fm.CGam_eq x i
  have hpos : 0 < Fm.CGam := hG ▸ (Fm.L x i).CGam_pos
  refine ⟨heightStatement_of_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC hCh h62 ?_,
    product_clause_at_record _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC hCh (by linarith) h22⟩
  have h1 := (div_le_iff₀ hpos).1 (h x hx i)
  rw [hG]
  linarith

end Fam

end Formalism.MainNotions.BridgeLemma

end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped InnerProductSpace

theorem one_le_max_self_inv_pos {a : ℝ} (ha : 0 < a) : 1 ≤ max a a⁻¹ := by
  rcases le_total 1 a with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ ha).2 h)

theorem max_self_inv_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ max a a⁻¹ := le_max_of_le_left ha

theorem max_inv_rpow_mono_exponent {a e1 e2 : ℝ} (ha : 0 ≤ a) (h0 : 0 < e1) (h : e1 ≤ e2) :
    (max a a⁻¹) ^ e1 ≤ (max a a⁻¹) ^ e2 := by
  rcases ha.eq_or_lt with h' | h'
  · subst h'
    simp only [inv_zero, max_self]
    rw [Real.zero_rpow h0.ne', Real.zero_rpow (lt_of_lt_of_le h0 h).ne']
  · exact Real.rpow_le_rpow_of_exponent_le (one_le_max_self_inv_pos h') h

theorem list_prod_max_inv_rpow_nonneg (L : List ℕ) (d : ℕ → ℝ) (hd : ∀ l, 0 ≤ d l) (e : ℝ) :
    0 ≤ (L.map fun l => (max (d l) (d l)⁻¹) ^ e).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_nonneg (Real.rpow_nonneg (max_self_inv_nonneg (hd a)) _) ih

theorem list_prod_max_inv_rpow_mono (L : List ℕ) (d : ℕ → ℝ) (hd : ∀ l, 0 ≤ d l) {e1 e2 : ℝ} (h0 : 0 < e1) (h : e1 ≤ e2) :
    (L.map fun l => (max (d l) (d l)⁻¹) ^ e1).prod ≤ (L.map fun l => (max (d l) (d l)⁻¹) ^ e2).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    exact mul_le_mul (max_inv_rpow_mono_exponent (hd a) h0 h) ih (list_prod_max_inv_rpow_nonneg L d hd e1)
      (Real.rpow_nonneg (max_self_inv_nonneg (hd a)) _)

theorem one_le_list_prod_max_inv_rpow (L : List ℕ) (d : ℕ → ℝ) (hd : ∀ l ∈ L, 0 < d l) {e : ℝ} (he : 0 ≤ e) :
    1 ≤ (L.map fun l => (max (d l) (d l)⁻¹) ^ e).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons]
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow (one_le_max_self_inv_pos (hd a (List.mem_cons_self))) he)
      (ih fun l hl => hd l (List.mem_cons_of_mem _ hl))

theorem single_factor_le_list_prod (L : List ℕ) (d : ℕ → ℝ) (hd : ∀ l ∈ L, 0 < d l) {e : ℝ} (he : 0 ≤ e) (l0 : ℕ) (hl0 : l0 ∈ L) :
    (max (d l0) (d l0)⁻¹) ^ e ≤ (L.map fun l => (max (d l) (d l)⁻¹) ^ e).prod := by
  induction L with
  | nil => simp at hl0
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons]
    have ha : 1 ≤ (max (d a) (d a)⁻¹) ^ e :=
      Real.one_le_rpow (one_le_max_self_inv_pos (hd a (List.mem_cons_self))) he
    have hL : ∀ l ∈ L, 0 < d l := fun l hl => hd l (List.mem_cons_of_mem _ hl)
    rcases List.mem_cons.1 hl0 with h | h
    · subst h
      exact le_mul_of_one_le_right (le_trans zero_le_one ha) (one_le_list_prod_max_inv_rpow L d hL he)
    · exact (ih hL h).trans (le_mul_of_one_le_left (le_trans zero_le_one (one_le_list_prod_max_inv_rpow L d hL he)) ha)

theorem one_le_foldr_max_alt (xs : List ℝ) : 1 ≤ xs.foldr max 1 := by
  induction xs with
  | nil => simp
  | cons a xs ih => rw [List.foldr_cons]; exact le_max_of_le_right ih

section Loss

variable {k r : ℕ} (b : ℝ) (m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) (p : Point ℂ (r + 1))

theorem one_le_loss_factor (hb : 1 ≤ b) {C : ℝ} (hC : 0 ≤ C) : 1 ≤ lossP b C m z z' γ p := by
  unfold lossP
  refine Real.one_le_rpow ?_ (by positivity)
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hb (by positivity)) (one_le_foldr_max_alt _)

theorem local_loss_mono_constant (hb : 1 ≤ b) {Ca C : ℝ} (hCa : 0 ≤ Ca) (h : Ca ≤ C) :
    lossP b Ca m z z' γ p ≤ lossP b C m z z' γ p := by
  unfold lossP
  have hM := one_le_foldr_max_alt ((ptBlockEnds p).map fun l => max 1 ‖DminN z z' γ l‖⁻¹)
  have h1 : b ^ (Ca * (m : ℝ)) ≤ b ^ (C * (m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hb (by gcongr)
  have h0 : 1 ≤ b ^ (Ca * (m : ℝ)) := Real.one_le_rpow hb (by positivity)
  refine (Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right h1 (by linarith)) (by positivity)).trans ?_
  refine Real.rpow_le_rpow_of_exponent_le ?_ (by gcongr)
  exact one_le_mul_of_one_le_of_one_le (h0.trans h1) hM

theorem loss_volume_nonneg (hb : 1 ≤ b) (C : ℝ) (hG : 0 < Gf k r z z' γ) : 0 ≤ lossV b C m z z' γ p := by
  unfold lossV
  refine mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_nonneg (max_self_inv_nonneg hG.le) _)) ?_
  exact list_prod_max_inv_rpow_nonneg _ (fun l => ‖DminN z z' γ l‖) (fun l => norm_nonneg _) _

theorem loss_volume_mono_constant (hb : 1 ≤ b) (hm : 0 < m) {Ca C : ℝ} (hCa : 0 < Ca) (h : Ca ≤ C) (hG : 0 < Gf k r z z' γ) :
    lossV b Ca m z z' γ p ≤ lossV b C m z z' γ p := by
  unfold lossV
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine mul_le_mul (mul_le_mul (Real.rpow_le_rpow_of_exponent_le hb (by gcongr))
    (Real.rpow_le_rpow_of_exponent_le (one_le_max_self_inv_pos hG) (by gcongr))
    (Real.rpow_nonneg (max_self_inv_nonneg hG.le) _) (Real.rpow_nonneg (by linarith) _)) ?_ ?_ ?_
  · exact list_prod_max_inv_rpow_mono _ (fun l => ‖DminN z z' γ l‖) (fun l => norm_nonneg _) (by positivity) (by gcongr)
  · exact list_prod_max_inv_rpow_nonneg _ (fun l => ‖DminN z z' γ l‖) (fun l => norm_nonneg _) _
  · exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (max_self_inv_nonneg hG.le) _)

theorem minor_power_le_loss (hb : 1 ≤ b) {C : ℝ} (hC : 0 ≤ C) (hG : 0 < Gf k r z z' γ)
    (hall : ∀ l ∈ ptBlockEnds p, DminN z z' γ l ≠ 0) (l0 : ℕ) (hl0 : l0 ∈ ptBlockEnds p) (N : ℕ)
    (hN : (N : ℝ) ≤ C * (m : ℝ)) : ‖DminN z z' γ l0‖ ^ N ≤ lossV b C m z z' γ p := by
  unfold lossV
  have hpos : ∀ l ∈ ptBlockEnds p, 0 < ‖DminN z z' γ l‖ := fun l hl => norm_pos_iff.2 (hall l hl)
  have h1 : ‖DminN z z' γ l0‖ ^ N ≤ (max ‖DminN z z' γ l0‖ ‖DminN z z' γ l0‖⁻¹) ^ (C * (m : ℝ)) := by
    refine (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ (‖DminN z z' γ l0‖⁻¹)) N).trans ?_
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_max_self_inv_pos (hpos l0 hl0)) hN
  have h2 := single_factor_le_list_prod (ptBlockEnds p) (fun l => ‖DminN z z' γ l‖) hpos (by positivity : 0 ≤ C * (m : ℝ)) l0 hl0
  have h3 : 1 ≤ b ^ (C * (m : ℝ) ^ 4) * (max (Gf k r z z' γ) (Gf k r z z' γ)⁻¹) ^ (C * (m : ℝ) ^ 2) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hb (by positivity))
      (Real.one_le_rpow (one_le_max_self_inv_pos hG) (by positivity))
  refine (h1.trans h2).trans (le_mul_of_one_le_left ?_ h3)
  exact list_prod_max_inv_rpow_nonneg _ (fun l => ‖DminN z z' γ l‖) (fun l => norm_nonneg _) _

end Loss

theorem hs_norm_sq_eq_sum_basis {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hs_norm_sq_nonneg {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  rw [hs_norm_sq_eq_sum_basis]; positivity

theorem hs_norm_sq_le_rank_mul_norm {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) :
    hsNormSq A ≤ (Module.finrank ℂ Wp : ℝ) * ‖A‖ ^ 2 := by
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  rw [hs_norm_sq_eq_sum_basis]
  have h1 : ∀ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 =
      ∑ j, ‖⟪stdOrthonormalBasis ℂ Wp j, A (stdOrthonormalBasis ℂ Wq i)⟫_ℂ‖ ^ 2 := fun i =>
    ((stdOrthonormalBasis ℂ Wp).sum_sq_norm_inner_right _).symm
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ j, ∑ i, ‖⟪stdOrthonormalBasis ℂ Wp j, A (stdOrthonormalBasis ℂ Wq i)⟫_ℂ‖ ^ 2 =
      ‖ContinuousLinearMap.adjoint A (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 := fun j => by
    rw [← (stdOrthonormalBasis ℂ Wq).sum_sq_norm_inner_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
  simp_rw [h2]
  have h3 : ∀ j, ‖ContinuousLinearMap.adjoint A (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 ≤ ‖A‖ ^ 2 := fun j => by
    have := (ContinuousLinearMap.adjoint A).le_opNorm (stdOrthonormalBasis ℂ Wp j)
    rw [(stdOrthonormalBasis ℂ Wp).orthonormal.1 j, mul_one, LinearIsometryEquiv.norm_map] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  refine (Finset.sum_le_sum fun j _ => h3 j).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem exp_one_mul_pi_lt_nine : Real.exp 1 * Real.pi < 9 := by
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.pi_lt_d2
  have h3 := Real.pi_pos
  have h4 := Real.exp_pos 1
  nlinarith

theorem local_error_term_le (k r : ℕ) (Ca C δ ν t g : ℝ) (hk : r + 2 ≤ k) (hCa : 0 < Ca) (hCaC : Ca ≤ C) (hCk : C ≤ k)
    (hδ : (r : ℝ) + 2 ≤ δ * k) (hν : 0 ≤ ν) (ht : 0 ≤ t) (hg : 0 ≤ g) :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.xv k r Ca ν t g ≤ ν * t * g⁻¹ ^ (2 * r + 2) * (C / k) ^ (2 * (r : ℝ) * (1 - δ)) := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.xv Formalism.HermitianLatticeCounting.LatticeSumBounds.expo
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hC : 0 < C := lt_of_lt_of_le hCa hCaC
  have hcast : ((2 * r * (k - 2 - r) : ℕ) : ℝ) = 2 * (r : ℝ) * ((k : ℝ) - 2 - r) := by
    have : k - 2 - r = k - (2 + r) := by omega
    rw [this]
    push_cast [Nat.cast_sub (by omega : 2 + r ≤ k)]
    ring
  have he : 2 * (r : ℝ) * (1 - δ) ≤ ((2 * r * (k - 2 - r) : ℕ) : ℝ) / (k : ℝ) := by
    rw [hcast, le_div_iff₀ hk0, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have he0 : 0 ≤ ((2 * r * (k - 2 - r) : ℕ) : ℝ) / (k : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : (Ca / (k : ℝ)) ^ (((2 * r * (k - 2 - r) : ℕ) : ℝ) / (k : ℝ)) ≤ (C / (k : ℝ)) ^ (((2 * r * (k - 2 - r) : ℕ) : ℝ) / (k : ℝ)) :=
    Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hCaC hk0.le) he0
  exact h1.trans (Real.rpow_le_rpow_of_exponent_ge (by positivity) ((div_le_one hk0).2 hCk) he)

theorem numerical_bound_first_case (k r : ℕ) (Ca C δ G T g v t Dr la lc pa pc hs Jop dim : ℝ)
    (hk : r + 2 ≤ k) (hkπ : Real.exp 1 * Real.pi ≤ k) (hCa : 0 < Ca) (hCaC : Ca ≤ C) (hCk : C ≤ k)
    (hδ : (r : ℝ) + 2 ≤ δ * k) (hG : 0 < G) (hT : 0 < T) (hg : 0 < g) (hv : 1 ≤ v) (ht : 0 < t) (hDr : 0 < Dr)
    (hlac : la ≤ lc) (hpa : 1 ≤ pa) (hpac : pa ≤ pc) (hhs : 0 ≤ hs) (hJop : 0 ≤ Jop) (hdim : 0 < dim)
    (hDl : Dr ^ (2 * r + 4) ≤ la) (hL2 : nv k r G T g v * hs / dim ≤ la * t⁻¹ ^ k)
    (hABS : Jop ≤ pa * (Ca / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r)) (hrank : hs ≤ dim * Jop ^ 2) :
    nv k r G T g v * hs / dim ≤
      lc * pc ^ 2 * t⁻¹ ^ k * (min 1 (G / (T * Dr ^ 2) * t * g⁻¹ ^ (2 * r + 2) * (C / k) ^ (2 * (r : ℝ) * (1 - δ)))) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hv0 : 0 < v := by linarith
  have hcond : (Real.exp 1 * Real.pi / (k * v)) ^ k * v⁻¹ ^ (2 * r * (k - 2 - r)) ≤ 1 := by
    refine mul_le_one₀ (pow_le_one₀ (by positivity) ?_) (by positivity)
      (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hv))
    rw [div_le_one (by positivity)]
    nlinarith
  have h := Formalism.HermitianLatticeCounting.P.minBoundFirst' k r Ca G T g v t Dr la pa (Real.sqrt hs) Jop dim hk hCa hG hT hg hv0 ht hDr hpa
    hdim hJop (Real.sqrt_nonneg _) hcond hDl (by rw [Real.sq_sqrt hhs]; exact hL2) hABS
    (by rw [Real.sq_sqrt hhs]; exact hrank)
  rw [Real.sq_sqrt hhs] at h
  refine h.trans ?_
  have hla : 0 ≤ la := le_trans (by positivity) hDl
  have hx := local_error_term_le k r Ca C δ (G / (T * Dr ^ 2)) t g hk hCa hCaC hCk hδ (by positivity) ht.le hg.le
  have hx0 : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.xv k r Ca (G / (T * Dr ^ 2)) t g := by unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.xv; positivity
  have hmin : min 1 (Formalism.HermitianLatticeCounting.LatticeSumBounds.xv k r Ca (G / (T * Dr ^ 2)) t g) ≤
      min 1 (G / (T * Dr ^ 2) * t * g⁻¹ ^ (2 * r + 2) * (C / k) ^ (2 * (r : ℝ) * (1 - δ))) :=
    min_le_min le_rfl hx
  have hmin0 : 0 ≤ min 1 (Formalism.HermitianLatticeCounting.LatticeSumBounds.xv k r Ca (G / (T * Dr ^ 2)) t g) := le_min zero_le_one hx0
  have hlc : 0 ≤ lc := hla.trans hlac
  have hpc : 0 ≤ pc := le_trans zero_le_one (hpa.trans hpac)
  gcongr

theorem product_le_enlarged_losses (la lc pa pc X : ℝ) (hla : 0 ≤ la) (hlac : la ≤ lc) (hpa : 1 ≤ pa) (hpac : pa ≤ pc) (hX : 0 ≤ X) :
    la * X ≤ lc * pc ^ 2 * X := by
  have h1 : (1 : ℝ) ≤ pc ^ 2 := one_le_pow₀ (hpa.trans hpac)
  have h2 : la ≤ lc * pc ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right h2 hX

theorem numerical_bound_second_case (k r : ℕ) (Ca C A G T T' g v t Dr sh ch la lc pa pc hs Jop dim : ℝ)
    (hr : 1 ≤ r) (hk : 2 * r + 6 ≤ k) (hCa : 0 < Ca) (hCaC : Ca ≤ C) (hCk : C ≤ k)
    (hA : 6 * Real.exp 1 * Real.pi * A ≤ C) (hG : 0 < G) (hT : 0 < T) (hT' : 0 < T') (hg : 1 ≤ g) (hv : 1 ≤ v)
    (ht : 0 < t) (hDr : 0 < Dr)
    (hlac : la ≤ lc) (hpa : 1 ≤ pa) (hpac : pa ≤ pc) (hhs : 0 ≤ hs) (hJop : 0 ≤ Jop) (hdim : 0 < dim)
    (hDl : Dr ^ (2 * r + 4) ≤ la) (hsh : 0 < sh) (hch : 0 ≤ ch) (hcs : ch ^ 2 = sh ^ 2 + 1)
    (hGs : G = T * T' * Dr ^ 2 * sh ^ 2) (hTA : T' / T ≤ A) (hlow : (k : ℝ) ^ (3 * r) ≤ g⁻¹ ^ (2 * r + 2) * T' * t)
    (hL2 : nv k r G T g v * hs / dim ≤ la * t⁻¹ ^ k)
    (hABS : Jop ≤ pa * (Ca / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r)) (hrank : hs ≤ dim * Jop ^ 2) :
    nv k r G T g v * hs * ((1 + ch) / sh) ^ (2 * k) * T⁻¹ ^ k / dim ≤ lc * pc ^ 2 * (C / k) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hv0 : 0 < v := by linarith
  have hg0 : 0 < g := by linarith
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hTA
  have hcond : v⁻¹ ^ k * (Ca / (k * v)) ^ (2 * r * (k - 2 - r)) ≤ 1 := by
    refine mul_le_one₀ (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hv)) (by positivity)
      (pow_le_one₀ (by positivity) ?_)
    rw [div_le_one (by positivity)]
    nlinarith
  have h := Formalism.HermitianLatticeCounting.P.minBoundSecond' k r Ca A G T T' g v t Dr sh ch la pa (Real.sqrt hs) Jop dim hr hk hCa hG hT hT' hg
    hv0 ht hDr hpa hdim hJop (Real.sqrt_nonneg _) hcond hDl hsh hch hcs hGs hTA hlow
    (by rw [Real.sq_sqrt hhs]; exact hL2) hABS (by rw [Real.sq_sqrt hhs]; exact hrank)
  rw [Real.sq_sqrt hhs] at h
  refine h.trans ?_
  have hla : 0 ≤ la := le_trans (by positivity) hDl
  have hbase : 6 * Real.exp 1 * Real.pi * A / (k * g ^ (2 * r + 2)) ≤ C / k := by
    have hgp : (1 : ℝ) ≤ g ^ (2 * r + 2) := one_le_pow₀ hg
    rw [div_le_div_iff₀ (by positivity) hk0]
    have hC0 : 0 ≤ C := le_trans hCa.le hCaC
    have : 6 * Real.exp 1 * Real.pi * A ≤ C * g ^ (2 * r + 2) := by nlinarith
    nlinarith
  have hb0 : 0 ≤ 6 * Real.exp 1 * Real.pi * A / (k * g ^ (2 * r + 2)) := by positivity
  have hlc : 0 ≤ lc := hla.trans hlac
  have hpc : 0 ≤ pc := le_trans zero_le_one (hpa.trans hpac)
  gcongr

theorem numericVolume_bound_ii (k r : ℕ) (C A G T T' g v t la lc pa pc hs dim : ℝ)
    (hr : 1 ≤ r) (hk : 1 ≤ k) (hA : A ≤ C) (hG : 0 < G) (hT : 0 < T) (hT' : 0 < T') (hg : 1 ≤ g) (hv : 0 < v)
    (ht : 0 < t) (hla : 0 ≤ la) (hlac : la ≤ lc) (hpa : 1 ≤ pa) (hpac : pa ≤ pc) (hhs : 0 ≤ hs) (hdim : 0 < dim)
    (hTA : T' / T ≤ A) (hlow : (k : ℝ) ^ (3 * r) ≤ g⁻¹ ^ (2 * r + 2) * T' * t)
    (hL2 : nv k r G T g v * hs / dim ≤ la * t⁻¹ ^ k) :
    nv k r G T g v * hs * T⁻¹ ^ k / dim ≤ lc * pc ^ 2 * (C / k) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hg0 : 0 < g := by linarith
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hTA
  have h := Formalism.HermitianLatticeCounting.P.minBoundSecondZero k r A G T T' g v t la (Real.sqrt hs) dim hr hk hG hT hT' hg hv ht hla hdim hTA hlow
    (by rw [Real.sq_sqrt hhs]; exact hL2)
  rw [Real.sq_sqrt hhs] at h
  refine h.trans ?_
  have hbase : A / (k * g ^ (2 * r + 2)) ≤ C / k := by
    have hgp : (1 : ℝ) ≤ g ^ (2 * r + 2) := one_le_pow₀ hg
    rw [div_le_div_iff₀ (by positivity) hk0]
    have : A ≤ C * g ^ (2 * r + 2) := by nlinarith
    nlinarith
  have hb0 : 0 ≤ A / (k * g ^ (2 * r + 2)) := by positivity
  have h1 : (A / (k * g ^ (2 * r + 2))) ^ k ≤ (C / k) ^ k := pow_le_pow_left₀ hb0 hbase k
  refine (mul_le_mul_of_nonneg_left h1 hla).trans ?_
  have hC0 : 0 ≤ C := hA0.le.trans hA
  exact product_le_enlarged_losses la lc pa pc _ hla hlac hpa hpac (by positivity)

theorem rank_eq_two_mul_add_two (D : D7) : D.R.m = 2 * D.R.rS + 2 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Ranks.rS]
  omega

theorem rank_lower_bound (D : D7) : 2 * D.R.rS + 6 ≤ D.R.k := by
  obtain ⟨t, ht⟩ := D.R.m_even
  obtain ⟨s, hs⟩ := D.R.k_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  simp only [Ranks.rS]
  omega

theorem one_le_scale_base_local {D : D7} (large₂ : SizeData₂ D) : 1 ≤ large₂.sc.b := by
  unfold Scale.b Scale.L
  exact Real.one_le_exp (Real.rpow_nonneg (le_trans zero_le_one large₂.sc.one_lt_alt.le) _)

theorem level_rpow_neg_rank_eq (D : D7) (hg : 0 < gg D) : gg D ^ (-(D.R.m : ℝ)) = (gg D)⁻¹ ^ (2 * D.R.rS + 2) := by
  rw [Real.rpow_neg hg.le, Real.rpow_natCast, rank_eq_two_mul_add_two D, inv_pow]

theorem local_volume_eq_weight (D : D7) (w : D.what₂.Word) (G : ℝ) (hg : 0 < gg D) :
    normalizedLocalScale D w * G ^ D.R.k = nv D.R.k D.R.rS G (Tr D w) (gg D) D.host.v := by
  unfold normalizedLocalScale nv
  rw [level_rpow_neg_rank_eq D hg, ← mul_pow]
  congr 1
  ring

theorem hyperbolic_parameters_of_minor {k r : ℕ} (T T' : ℝ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) (hT : 0 < T) (hT' : 0 < T')
    (hz : Tz k r z = T) (hz' : Tz k r z' = T') (hD : DminN z z' γ r ≠ 0) (hG : 0 < Gf k r z z' γ) :
    0 < shV T T' z z' γ ∧ 0 ≤ chV T T' z z' γ ∧ chV T T' z z' γ ^ 2 = shV T T' z z' γ ^ 2 + 1 ∧
      Gf k r z z' γ = T * T' * ‖DminN z z' γ r‖ ^ 2 * shV T T' z z' γ ^ 2 := by
  have hDe : DminN z z' γ r = Dmin k r z z' γ ⟨r, by omega⟩ := by
    unfold DminN; rw [dif_pos (by omega)]
  have hd : 0 < ‖DminN z z' γ r‖ := norm_pos_iff.2 hD
  have hTT : 0 < T * T' := mul_pos hT hT'
  have hch2 : chV T T' z z' γ ^ 2 =
      ‖Dmin k r z z' γ (Fin.last (r + 1))‖ ^ 2 / (‖DminN z z' γ r‖ ^ 2 * (T * T')) := by
    unfold chV zeta
    rw [← hDe, norm_div, div_pow, div_pow, Real.sq_sqrt hTT.le, div_div]
  have hGe : Gf k r z z' γ = ‖Dmin k r z z' γ (Fin.last (r + 1))‖ ^ 2 - T * T' * ‖DminN z z' γ r‖ ^ 2 := by
    unfold Gf
    rw [hz, hz', ← hDe, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have h1 : chV T T' z z' γ ^ 2 - 1 = Gf k r z z' γ / (T * T' * ‖DminN z z' γ r‖ ^ 2) := by
    rw [hch2, hGe]; field_simp
  have hpos : 0 < chV T T' z z' γ ^ 2 - 1 := by rw [h1]; positivity
  have hsh2 : shV T T' z z' γ ^ 2 = chV T T' z z' γ ^ 2 - 1 := by
    unfold shV; rw [Real.sq_sqrt hpos.le]
  refine ⟨by unfold shV; exact Real.sqrt_pos.2 hpos, by unfold chV; positivity, by rw [hsh2]; ring, ?_⟩
  rw [hsh2, h1]; field_simp

theorem le_of_exp_pi_mul_le (A C : ℝ) (hA0 : 0 < A) (hA : 6 * Real.exp 1 * Real.pi * A ≤ C) : A ≤ C := by
  have h6 : 1 ≤ 6 * Real.exp 1 * Real.pi := by
    have := Real.add_one_le_exp (1 : ℝ)
    have := Real.pi_gt_three
    nlinarith
  nlinarith

theorem exponent_le_constant_mul (r m Ca : ℝ) (hm : m = 2 * r + 2) (hr : 0 ≤ r) (h2 : 2 ≤ Ca) : 2 * r + 4 ≤ Ca * m := by
  subst hm; nlinarith

theorem lossStatement_of_bounds (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A C1 Ca C δ : ℝ)
    (h2 : 2 ≤ Ca) (hCaC : Ca ≤ C) (hCk : C ≤ D.R.k) (hδ : (D.R.rS : ℝ) + 2 ≤ δ * D.R.k)
    (hA : 6 * Real.exp 1 * Real.pi * A ≤ C) :
    VanishingOnXAndXPlusBranching.ShareFromInputs D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Ca C δ := by
  intro h5 hL2 hABS τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH
  have hL2' := hL2 τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH
  have hABS' := hABS τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH
  beta_reduce at hL2' hABS'
  obtain ⟨hH0, hStand, hTA, -⟩ := hH
  have hlow := h5 hH0 w' τ
  obtain ⟨_, _, hmf, hfk, _, _, _, _, _, _, _, hg1, _, hg2, _, _, _, _, hv, -⟩ := hH0.1
  obtain ⟨_, _, hz, hz', hTz, hTz', -⟩ := hW
  have hr : 1 ≤ D.R.rS := hStand.1
  have hk := rank_lower_bound D
  have hb := one_le_scale_base_local large₂
  have hm := rank_eq_two_mul_add_two D
  have hm0 : 0 < D.R.m := by omega
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
  have hT : 0 < Tr D w := by unfold Tr; exact_mod_cast hTT.1.pos
  have hT' : 0 < Tr D w' := by unfold Tr; exact_mod_cast hTT.2.1.pos
  have hG : 0 < Gf D.R.k D.R.rS W.z W.z' γ := cell_G_pos D hRel hz hz' (hTz ▸ hT) (hTz' ▸ hT')
  have hkb : (1 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    have : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le this hb)
  have hg : 1 ≤ gg D := by
    unfold gg
    exact one_le_mul_of_one_le_of_one_le (hkb.trans hg1) (hkb.trans hg2)
  have hg0 : 0 < gg D := lt_of_lt_of_le one_pos hg
  have hkπ : Real.exp 1 * Real.pi ≤ D.R.k := by
    have h256 : 256 ≤ D.R.k := by
      have h4 : 4 ≤ D.R.m := by omega
      have : 4 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left h4 4
      omega
    have h256' : (256 : ℝ) ≤ D.R.k := by exact_mod_cast h256
    exact le_trans (le_trans exp_one_mul_pi_lt_nine.le (by norm_num)) h256'
  have hCa : 0 < Ca := lt_of_lt_of_le two_pos h2
  have hTc : 0 < Tcrit D w' τ := by
    have h1 : 0 < gg D ^ (-(D.R.m : ℝ)) * Tcrit D w' τ := lt_of_lt_of_le (by positivity) hlow
    exact (pos_iff_pos_of_mul_pos h1).1 (Real.rpow_pos_of_pos hg0 _)
  have ht : 0 < tvPr D τ w' := by unfold tvPr; positivity
  have hlow' : (D.R.k : ℝ) ^ (3 * D.R.rS) ≤ (gg D)⁻¹ ^ (2 * D.R.rS + 2) * Tr D w' * tvPr D τ w' := by
    rw [← level_rpow_neg_rank_eq D hg0, mul_assoc]
    unfold tvPr
    rw [mul_div_cancel₀ _ hT'.ne']
    exact hlow
  have hall : ∀ l ∈ ptBlockEnds p, DminN W.z W.z' γ l ≠ 0 := fun l hl => cell_ne_of_mem D hRel l hl
  have hla0 := loss_volume_nonneg large₂.sc.b D.R.m W.z W.z' γ p hb Ca hG
  have hlac := loss_volume_mono_constant large₂.sc.b D.R.m W.z W.z' γ p hb hm0 hCa hCaC hG
  have hpa := one_le_loss_factor large₂.sc.b D.R.m W.z W.z' γ p hb hCa.le
  have hpac := local_loss_mono_constant large₂.sc.b D.R.m W.z W.z' γ p hb hCa.le hCaC
  have hhs := hs_norm_sq_nonneg (S.J νR γ)
  have hrank := hs_norm_sq_le_rank_mul_norm (S.J νR γ)
  have hTA' : Tr D w' / Tr D w ≤ A := hTA
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hTA'
  have hAC : A ≤ C := le_of_exp_pi_mul_le A C hA0 hA
  have hC0 : 0 ≤ C := hA0.le.trans hAC
  rw [local_volume_eq_weight D w _ hg0, ← inv_pow] at hL2'
  rw [local_volume_eq_weight D w _ hg0, ← inv_pow, ← inv_pow]
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ W.Wp) with hd0 | hd0
  ·
    have hlc := hla0.trans hlac
    rw [hd0]
    simp only [Nat.cast_zero, div_zero]
    have hamp : 0 ≤ ampMinF D C δ τ w w' W.z W.z' γ := by
      unfold ampMinF
      split_ifs
      · exact zero_le_one
      · refine le_min zero_le_one ?_
        unfold nuV
        positivity
    exact ⟨by positivity, by positivity⟩
  have hdim : (0 : ℝ) < Module.finrank ℂ W.Wp := by exact_mod_cast hd0
  by_cases hD : DminN W.z W.z' γ D.R.rS = 0
  ·
    have e1 : ampMinF D C δ τ w w' W.z W.z' γ = 1 := by unfold ampMinF; rw [if_pos hD]
    have e2 : chRatio (Tr D w) (Tr D w') W.z W.z' γ = 1 := by unfold chRatio; rw [if_pos hD]
    rw [e1, e2, one_pow, one_pow, mul_one, mul_one]
    refine ⟨hL2'.trans (product_le_enlarged_losses _ _ _ _ _ hla0 hlac hpa hpac (by positivity)), ?_⟩
    exact numericVolume_bound_ii D.R.k D.R.rS C A _ _ _ _ _ _ _ _ _ _ _ _ hr (by omega) hAC hG hT hT' hg (lt_of_lt_of_le one_pos hv) ht hla0 hlac
      hpa hpac hhs hdim hTA' hlow' hL2'
  · have hDr : 0 < ‖DminN W.z W.z' γ D.R.rS‖ := norm_pos_iff.2 hD
    have hmem : D.R.rS ∈ ptBlockEnds p := cell_mem_blockEnds D hRel D.R.rS hr (by omega) hD
    have hDl : ‖DminN W.z W.z' γ D.R.rS‖ ^ (2 * D.R.rS + 4) ≤ lossV large₂.sc.b Ca D.R.m W.z W.z' γ p := by
      refine minor_power_le_loss large₂.sc.b D.R.m W.z W.z' γ p hb hCa.le hG hall D.R.rS hmem _ ?_
      have hmr : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by exact_mod_cast hm
      push_cast
      exact exponent_le_constant_mul _ _ Ca hmr (Nat.cast_nonneg _) h2
    have hABS'' := hABS' hD
    rw [← inv_pow] at hABS''
    have e1 : ampMinF D C δ τ w w' W.z W.z' γ =
        min 1 (Gf D.R.k D.R.rS W.z W.z' γ / (Tr D w * ‖DminN W.z W.z' γ D.R.rS‖ ^ 2) * tvPr D τ w' *
          (gg D)⁻¹ ^ (2 * D.R.rS + 2) * (C / D.R.k) ^ (2 * (D.R.rS : ℝ) * (1 - δ))) := by
      unfold ampMinF nuV; rw [if_neg hD, level_rpow_neg_rank_eq D hg0]
    have e2 : chRatio (Tr D w) (Tr D w') W.z W.z' γ =
        (1 + chV (Tr D w) (Tr D w') W.z W.z' γ) / shV (Tr D w) (Tr D w') W.z W.z' γ := by
      unfold chRatio; rw [if_neg hD]
    obtain ⟨hsh, hch, hcs, hGs⟩ := hyperbolic_parameters_of_minor (Tr D w) (Tr D w') W.z W.z' γ hT hT' hTz hTz' hD hG
    rw [e1, e2]
    refine ⟨?_, ?_⟩
    · exact numerical_bound_first_case D.R.k D.R.rS Ca C δ _ _ _ _ _ _ _ _ _ _ _ ‖S.J νR γ‖ _ (by omega) hkπ hCa hCaC hCk hδ hG hT hg0 hv ht
        hDr hlac hpa hpac hhs (norm_nonneg _) hdim hDl hL2' hABS'' hrank
    · exact numerical_bound_second_case D.R.k D.R.rS Ca C A _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‖S.J νR γ‖ _ hr hk hCa hCaC hCk hA hG hT hT' hg hv ht
        hDr hlac hpa hpac hhs (norm_nonneg _) hdim hDl hsh hch hcs hGs hTA' hlow' hL2' hABS'' hrank

section Fam

variable {eps : ℝ} (Fm : FamP eps)

theorem family_side_conditions_large (C δ : ℝ) (hδ : 0 < δ) : ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
    C ≤ (Fm.D x i).R.k ∧ ((Fm.D x i).R.rS : ℝ) + 2 ≤ δ * (Fm.D x i).R.k := by
  obtain ⟨a, _, ha⟩ := ev_k Fm C
  obtain ⟨a', _, ha'⟩ := ev_m Fm (1 / δ)
  refine ⟨max a a', fun x hx hx1 i => ⟨ha x (le_trans (le_max_left _ _) hx) i, ?_⟩⟩
  have hm := ha' x (le_trans (le_max_right _ _) hx) i
  have hkm := (Fm.params x hx1 i).k_ge_m2L
  have hL : 1 ≤ (Fm.L x i).sc.L := by
    rw [sc_L Fm hx1]
    exact Real.one_le_rpow (one_lt_of Fm hx1).le (eps_pos Fm).le
  have hmr : ((Fm.D x i).R.m : ℝ) = 2 * ((Fm.D x i).R.rS : ℝ) + 2 := by exact_mod_cast rank_eq_two_mul_add_two (Fm.D x i)
  have hr0 : (0 : ℝ) ≤ (Fm.D x i).R.rS := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) < (Fm.D x i).R.m := by rw [hmr]; positivity
  have h1 : 1 ≤ δ * (Fm.D x i).R.m := by
    rw [div_le_iff₀ hδ] at hm; linarith
  have h2 : ((Fm.D x i).R.m : ℝ) ^ 2 ≤ (Fm.D x i).R.k :=
    le_trans (le_mul_of_one_le_right (by positivity) hL) hkm
  have h3 : ((Fm.D x i).R.m : ℝ) ≤ δ * ((Fm.D x i).R.m : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right h1 hm0.le
    nlinarith
  have h4 : δ * ((Fm.D x i).R.m : ℝ) ^ 2 ≤ δ * (Fm.D x i).R.k := mul_le_mul_of_nonneg_left h2 hδ.le
  linarith

end Fam

end Formalism.MainNotions.BridgeLemma

end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

section Assembly

variable {eps : ℝ} (Fm : FamP eps)

end Assembly

end Formalism.MainNotions.BridgeLemma

end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt MeasureTheory
open scoped ENNReal

section HS

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hs_vector_smul (c : ℂ) (X : Wq →L[ℂ] Wp) : hsVec (c • X) = c • hsVec X := by
  ext j
  simp [hsVec]

theorem hs_vector_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (X : ι → (Wq →L[ℂ] Wp)) :
    hsVec (∑ i ∈ s, a i • X i) = ∑ i ∈ s, a i • hsVec (X i) := by
  ext j
  simp [hsVec]

end HS

theorem weighted_sum_norm_le {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} (F : Finset ι) (a : ι → ℂ)
    (v : ι → V) (d B Kj : ℝ) (hd : 0 ≤ d) (hKj : 0 ≤ Kj) (hsum : ∑ I ∈ F, ‖a I‖ ≤ B)
    (hterm : ∀ I ∈ F, a I = 0 ∨ d * ‖v I‖ ≤ Kj) : d * ‖∑ I ∈ F, a I • v I‖ ≤ B * Kj := by
  calc d * ‖∑ I ∈ F, a I • v I‖ ≤ d * ∑ I ∈ F, ‖a I‖ * ‖v I‖ := by
        refine mul_le_mul_of_nonneg_left ?_ hd
        exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun I _ => norm_smul _ _))
    _ = ∑ I ∈ F, ‖a I‖ * (d * ‖v I‖) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ ∑ I ∈ F, ‖a I‖ * Kj := by
        refine Finset.sum_le_sum (fun I hI => ?_)
        rcases hterm I hI with h | h
        · rw [h]; simp
        · exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = (∑ I ∈ F, ‖a I‖) * Kj := by rw [Finset.sum_mul]
    _ ≤ B * Kj := mul_le_mul_of_nonneg_right hsum hKj

theorem l1_distance_sign_step {N : ℕ} (x y : Fin N → ℝ) (s : ℝ) (hs : s = 1 ∨ s = -1) (I : Finset (Fin N)) :
    l1dist (x + s • epsI I) y ≤ l1dist x y + I.card := by
  unfold l1dist
  have h : ∀ i, |(x + s • epsI I) i - y i| ≤ |x i - y i| + (if i ∈ I then (1 : ℝ) else 0) := by
    intro i
    have e : (x + s • epsI I) i - y i = (x i - y i) + s * (if i ∈ I then (1 : ℝ) else 0) := by
      simp only [Pi.add_apply, Pi.smul_apply, epsI, smul_eq_mul]
      ring
    rw [e]
    refine le_trans (abs_add_le _ _) ?_
    have : |s * (if i ∈ I then (1 : ℝ) else 0)| = (if i ∈ I then (1 : ℝ) else 0) := by
      rcases hs with rfl | rfl <;> split_ifs <;> simp
    rw [this]
  calc ∑ i, |(x + s • epsI I) i - y i| ≤ ∑ i, (|x i - y i| + (if i ∈ I then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum (fun i _ => h i)
    _ = ∑ i, |x i - y i| + I.card := by
        rw [Finset.sum_add_distrib]
        simp

theorem degree_ratio_iteration (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 Cn C1 CDl : ℝ}
    (hA2 : VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl) (hH0 : Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (τ : D.what₂.Tau) (w w' : D.what₂.Word) (hTT : HypTT D w w') (θ : ℝ) (hθ : normWin D large₂ C1 θ)
    (W : LocW D.R.k D.R.rS) (hGW : GoodW D τ w w' θ W) (l : ℕ) (hl : l ≤ D.R.rS + 1)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (hμ : IsSection D.R.k D.R.rS W.z W.z' μsec)
    (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)) (hRel : RelPt D W.z W.z' γ p) (θ' : ℝ)
    (hθ' : normWin D large₂ C1 θ') (νR : Measure (Mt D.R.k D.R.rS)) (hν : RMeas D W γ θ' νR) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ (lam'' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W),
      l1dist lam'' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → GoodS D lam'' A →
      ‖hsVec (jhUnit D w w' A μsec νR γ)‖ ≤ K) :
    ∀ (j : ℕ) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A₀ : LocS W), GoodS D lam' A₀ →
      l1dist lam' (lamD D τ) + (j : ℝ) * l ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
      ‖DminN W.z W.z' γ l‖ ^ j * ‖hsVec (jhUnit D w w' A₀ μsec νR γ)‖ ≤
        (large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2)) ^ j * K := by
  intro j
  induction j with
  | zero =>
    intro lam' A₀ hG hr
    simpa using hK lam' A₀ (by simpa using hr) hG
  | succ j ih =>
    intro lam' A₀ hG hr
    have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
    have hr0 : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := by
      have : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * l := by positivity
      linarith
    obtain ⟨s, hs, H⟩ := hA2 hH0 τ w w' hTT θ hθ W hGW lam' hr0 A₀ hG l hl
    classical
    obtain ⟨a, ha0, hasum, haeq⟩ := H
      (fun I => if h : ∃ A : LocS W, GoodS D (lam' + s • epsI I) A then h.choose else A₀)
      (fun I _ h => by simp only [dif_pos h]; exact h.choose_spec)
    have heq := congrArg hsVec (haeq μsec hμ γ p hRel θ' hθ' νR hν)
    rw [hs_vector_smul, hs_vector_finset_sum] at heq
    have hb0 : 0 < large₂.sc.b := lt_of_lt_of_le one_pos (one_le_b large₂)
    have hB0 : 0 ≤ large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) := Real.rpow_nonneg hb0.le _
    calc ‖DminN W.z W.z' γ l‖ ^ (j + 1) * ‖hsVec (jhUnit D w w' A₀ μsec νR γ)‖
        = ‖DminN W.z W.z' γ l‖ ^ j * ‖DminN W.z W.z' γ l • hsVec (jhUnit D w w' A₀ μsec νR γ)‖ := by
          rw [norm_smul]; ring
      _ ≤ large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) * ((large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2)) ^ j * K) := by
          rw [heq]
          refine weighted_sum_norm_le _ a _ _ _ _ (by positivity) (by positivity) hasum (fun I hI => ?_)
          have hc : I.card = l := (Finset.mem_filter.1 hI).2
          by_cases hex : ∃ A : LocS W, GoodS D (lam' + s • epsI I) A
          · right
            refine ih _ _ (by simp only [dif_pos hex]; exact hex.choose_spec) ?_
            have h1 := l1_distance_sign_step lam' (lamD D τ) s hs I
            rw [hc] at h1
            push_cast at hr
            linarith
          · left
            exact ha0 I hc hex
      _ = (large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2)) ^ (j + 1) * K := by ring

theorem threshold_bound_even_decay (r q : ℕ) (d : Fin (r + 2) → ℝ) (H B Y Z : ℝ) (hH : 1 ≤ H) (hd0 : d 0 ≤ H)
    (hB0 : 0 ≤ B) (hBH : B ≤ H) (hZ : 0 ≤ Z) (h0 : Y ≤ Z) (h : ∀ l, Y * d l ^ (2 * q) ≤ Z * B ^ (2 * q)) :
    Y ≤ Z * (∏ l, max 1 (d l / H)) ^ (-(2 * (q : ℝ) / ((r : ℝ) + 1))) := by
  have hH0 : 0 < H := by linarith
  obtain ⟨ls, -, hls⟩ := Finset.exists_max_image Finset.univ d ⟨0, Finset.mem_univ _⟩
  rcases le_or_gt (d ls) H with hc | hc
  · have : ∏ l, max 1 (d l / H) = 1 := Finset.prod_eq_one (fun l _ =>
      max_eq_left ((div_le_one hH0).2 (le_trans (hls l (Finset.mem_univ _)) hc)))
    rw [this, Real.one_rpow, mul_one]
    exact h0
  · have ht1 : 1 < d ls / H := (one_lt_div hH0).2 hc
    have ht0 : 0 < d ls / H := by linarith
    have hf : ∀ l, max 1 (d l / H) ≤ d ls / H := fun l =>
      max_le ht1.le (div_le_div_of_nonneg_right (hls l (Finset.mem_univ _)) hH0.le)
    have hsz : ∏ l, max 1 (d l / H) ≤ (d ls / H) ^ (r + 1) := by
      rw [Fin.prod_univ_succ, max_eq_left ((div_le_one hH0).2 hd0), one_mul]
      calc ∏ i : Fin (r + 1), max 1 (d i.succ / H) ≤ ∏ _i : Fin (r + 1), d ls / H :=
            Finset.prod_le_prod (fun i _ => le_trans zero_le_one (le_max_left _ _)) (fun i _ => hf _)
        _ = (d ls / H) ^ (r + 1) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hs1 : 0 < ∏ l, max 1 (d l / H) :=
      Finset.prod_pos (fun l _ => lt_of_lt_of_le one_pos (le_max_left _ _))
    have he : ((d ls / H) ^ (r + 1)) ^ (-(2 * (q : ℝ) / ((r : ℝ) + 1))) = ((d ls / H) ^ (2 * q))⁻¹ := by
      rw [← Real.rpow_natCast (d ls / H) (r + 1), ← Real.rpow_mul ht0.le, ← Real.rpow_natCast (d ls / H) (2 * q),
        ← Real.rpow_neg ht0.le]
      congr 1
      push_cast
      field_simp
    have hmono : ((d ls / H) ^ (r + 1)) ^ (-(2 * (q : ℝ) / ((r : ℝ) + 1))) ≤
        (∏ l, max 1 (d l / H)) ^ (-(2 * (q : ℝ) / ((r : ℝ) + 1))) :=
      Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by
        have : (0 : ℝ) ≤ 2 * (q : ℝ) / ((r : ℝ) + 1) := by positivity
        linarith) (Set.mem_Ioi.2 hs1) (Set.mem_Ioi.2 (lt_of_lt_of_le hs1 hsz)) hsz
    have hdl : 0 < d ls := by linarith
    have h1 : Y ≤ Z * ((d ls / H) ^ (2 * q))⁻¹ := by
      have hp : 0 < d ls ^ (2 * q) := by positivity
      have h3 : Y ≤ Z * B ^ (2 * q) / d ls ^ (2 * q) := by rw [le_div_iff₀ hp]; exact h ls
      refine h3.trans ?_
      rw [div_pow, inv_div, mul_div_assoc]
      have h4 : B ^ (2 * q) ≤ H ^ (2 * q) := pow_le_pow_left₀ hB0 hBH _
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h4 hp.le) hZ
    calc Y ≤ Z * ((d ls / H) ^ (2 * q))⁻¹ := h1
      _ = Z * ((d ls / H) ^ (r + 1)) ^ (-(2 * (q : ℝ) / ((r : ℝ) + 1))) := by rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmono hZ

theorem L2_decay_pointwise_estimate (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 CPT CDl Cc C : ℝ)
    (hPT : 0 ≤ CPT) (hCc : 0 ≤ Cc) (hC : CPT + Cc + 6 ≤ C)
    (hA1 : VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT)
    (hA2 : VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl)
    (hP1 : VanishingOnXAndXPlusBranching.Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 C1 Cc) (hH0 : Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (τ : D.what₂.Tau) (w w' : D.what₂.Word) (hTT : HypTT D w w') (θ : ℝ) (hθ : normWin D large₂ C1 θ)
    (W : LocW D.R.k D.R.rS) (hGW : GoodW D τ w w' θ W) (S : LocS W) (hGS : GoodS D (lamD D τ) S)
    (hdeg : S.deg = D.dsig τ) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)) (hRel : RelPt D W.z W.z' γ p) (θ' : ℝ)
    (hθ' : normWin D large₂ C1 θ') (νR : Measure (Mt D.R.k D.R.rS)) (hν : RMeas D W γ θ' νR)
    (l : ℕ) (hl : l ≤ D.R.rS + 1) (q : ℕ) (hq : (q : ℝ) * l ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3) :
    normalizedLocalScale D w * Gf D.R.k D.R.rS W.z W.z' γ ^ D.R.k * hsNormSq (S.J νR γ) * ‖DminN W.z W.z' γ l‖ ^ (2 * q) ≤
      lossV large₂.sc.b C D.R.m W.z W.z' γ p * (tvPr D τ w' ^ D.R.k)⁻¹ * (Module.finrank ℂ W.Wp : ℝ) *
        (large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2)) ^ (2 * q) := by
  have hGW2 := hGW
  obtain ⟨_, _, hz, hz', hTz, hTz', _⟩ := hGW2
  have hT : 0 < Tr D w := by
    unfold Tr; exact_mod_cast hTT.1.pos
  have hT' : 0 < Tr D w' := by
    unfold Tr; exact_mod_cast hTT.2.1.pos
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hm1 : 2 ≤ D.R.m := D.R.two_le_m
  obtain ⟨μsec, hμ⟩ := Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists D.R.k D.R.rS W.z W.z' hk1 hz hz' (by rw [hTz]; exact hT)
    (by rw [hTz']; exact hT')
  have hl00 : l1dist (lamD D τ) (lamD D τ) = 0 := by
    unfold l1dist; simp
  have hCn0 : 0 ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := le_trans (by positivity) hq
  have h1 := hA1 hH0 τ w w' hTT θ hθ W hGW (lamD D τ) (by rw [hl00]; exact hCn0) S hGS μsec hμ γ p hRel θ' hθ' νR hν
  have h2 := hP1 hH0 τ w w' hTT θ hθ W hGW S hGS hdeg μsec hμ
  have hG : 0 < Gf D.R.k D.R.rS W.z W.z' γ :=
    cell_G_pos D hRel hz hz' (by rw [hTz]; exact hT) (by rw [hTz']; exact hT')
  obtain ⟨hw0, hw1⟩ := cell_weight_lemma D W.z W.z' γ p hz hz' (by rw [hTz]; exact hT) (by rw [hTz']; exact hT') hRel
  rw [hTz, hTz'] at hw0 hw1
  set G := Gf D.R.k D.R.rS W.z W.z' γ with hGd
  set X := hsNormSq (S.J νR γ) with hX
  set wt := ptWeight D.R.k D.R.rS (Tr D w) (Tr D w') p with hwt
  set n0 := normalizedLocalScale D w with hn0
  set dim : ℝ := (Module.finrank ℂ W.Wp : ℝ) with hdim
  set ti := (tvPr D τ w' ^ D.R.k)⁻¹ with hti
  set B1 := large₂.sc.b ^ (CPT * (D.R.m : ℝ) ^ 4) * (max 1 G⁻¹) ^ (CPT * (D.R.m : ℝ) ^ 2) with hB1
  set Mx := max G G⁻¹ * ((ptBlockEnds p).map fun l => (max ‖DminN W.z W.z' γ l‖ ‖DminN W.z W.z' γ l‖⁻¹) ^ (2 * (D.R.m + 4))).prod
    with hMx
  set B := large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) with hB
  set P := ‖DminN W.z W.z' γ l‖ ^ (2 * q) with hP
  set R := dim * ti * large₂.sc.b ^ (Cc * (D.R.m : ℝ) ^ 2) with hR
  have hb := one_le_b large₂
  have hX0 : 0 ≤ X := hsNormSq_nonneg _
  have hn00 : 0 ≤ n0 := by rw [hn0]; unfold normalizedLocalScale; exact D.R.k_even.pow_nonneg _
  have hti0 : 0 ≤ ti := inv_nonneg.2 (D.R.k_even.pow_nonneg _)
  have hdim0 : 0 ≤ dim := Nat.cast_nonneg _
  have hB10 : 0 ≤ B1 := mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hbc0 : 0 ≤ large₂.sc.b ^ (Cc * (D.R.m : ℝ) ^ 2) := Real.rpow_nonneg (by linarith) _
  have hR0 : 0 ≤ R := mul_nonneg (mul_nonneg hdim0 hti0) hbc0
  have hB0 : 0 ≤ B := Real.rpow_nonneg (by linarith) _
  have hP0 : 0 ≤ P := by positivity
  have hMx0 : 0 ≤ Mx := by
    apply mul_nonneg (le_trans hG.le (le_max_left _ _))
    exact (list_map_prod_le _ _ (fun l => ⟨by positivity, le_rfl⟩) _).1

  have hK : ∀ (lam'' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W),
      l1dist lam'' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → GoodS D lam'' A →
      ‖hsVec (jhUnit D w w' A μsec νR γ)‖ ≤ Real.sqrt (B1 / wt) := by
    intro lam'' A hr hA
    have h3 := jhUnit_le D w w' A μsec νR γ wt B1 hB10
      (hA1 hH0 τ w w' hTT θ hθ W hGW lam'' hr A hA μsec hμ γ p hRel θ' hθ' νR hν)
    refine Real.le_sqrt_of_sq_le ?_
    rw [hsVec_norm_sq, le_div_iff₀ hw0, mul_comm]
    exact h3
  have hit := degree_ratio_iteration D large₂ hA2 hH0 τ w w' hTT θ hθ W hGW l hl μsec hμ γ p hRel θ' hθ' νR hν
    (Real.sqrt (B1 / wt)) (Real.sqrt_nonneg _) hK q (lamD D τ) S hGS (by rw [hl00, zero_add]; exact hq)
  have hjh : wt * hsNormSq (jhUnit D w w' S μsec νR γ) * P ≤ B1 * B ^ (2 * q) := by
    have h4 := pow_le_pow_left₀ (by positivity) hit 2
    rw [mul_pow, mul_pow, hsVec_norm_sq, Real.sq_sqrt (div_nonneg hB10 hw0.le), ← pow_mul, ← pow_mul,
      mul_comm q 2] at h4
    calc wt * hsNormSq (jhUnit D w w' S μsec νR γ) * P
        = wt * (P * hsNormSq (jhUnit D w w' S μsec νR γ)) := by ring
      _ ≤ wt * (B ^ (2 * q) * (B1 / wt)) := mul_le_mul_of_nonneg_left h4 hw0.le
      _ = B1 * B ^ (2 * q) := by field_simp
  have key : n0 * (wt * X) * P ≤ B1 * R * B ^ (2 * q) := by
    have hrhs : 0 ≤ B1 * R * B ^ (2 * q) := by positivity
    by_cases hM : (MMv D w w' S μsec).toReal = 0
    · rcases (ENNReal.toReal_eq_zero_iff _).1 hM with h0 | h0
      · rw [h0, mul_zero] at h1
        have h5 : wt * X ≤ 0 := ENNReal.ofReal_eq_zero.1 (le_antisymm h1 bot_le)
        have h6 : wt * X = 0 := le_antisymm h5 (mul_nonneg hw0.le hX0)
        rw [h6]; simpa using hrhs
      · rw [h0] at h2
        have h5 : ENNReal.ofReal n0 = 0 := by
          by_contra hne
          rw [ENNReal.mul_top hne] at h2
          exact absurd (lt_of_le_of_lt h2 ENNReal.ofReal_lt_top) (lt_irrefl _)
        have h6 : n0 = 0 := le_antisymm (ENNReal.ofReal_eq_zero.1 h5) hn00
        rw [h6]; simpa using hrhs
    · have hpos : 0 < (MMv D w w' S μsec).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hM)
      have htop : MMv D w w' S μsec ≠ ⊤ := fun e => hM (by rw [e]; rfl)
      rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul hn00] at h2
      have h7 : n0 * (MMv D w w' S μsec).toReal ≤ R := (ENNReal.ofReal_le_ofReal_iff hR0).1 h2
      have h3 : ((MMv D w w' S μsec).toReal ^ (-(1 / 2 : ℝ))) ^ 2 = ((MMv D w w' S μsec).toReal)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_neg_one]
        norm_num
      have h8 : hsNormSq (jhUnit D w w' S μsec νR γ) = ((MMv D w w' S μsec).toReal)⁻¹ * X := by
        unfold jhUnit
        rw [hsNormSq_real_smul, h3]
      have h9 : X = (MMv D w w' S μsec).toReal * hsNormSq (jhUnit D w w' S μsec νR γ) := by
        rw [h8]; field_simp
      calc n0 * (wt * X) * P
          = (n0 * (MMv D w w' S μsec).toReal) * (wt * hsNormSq (jhUnit D w w' S μsec νR γ) * P) := by
            rw [h9]; ring
        _ ≤ R * (B1 * B ^ (2 * q)) :=
            mul_le_mul h7 hjh (mul_nonneg (mul_nonneg hw0.le (hsNormSq_nonneg _)) hP0) hR0
        _ = B1 * R * B ^ (2 * q) := by ring
  have hloss := loss_factor_le_rpow large₂.sc.b CPT Cc C D.R.m W.z W.z' γ p hb hm1 hPT hCc hC hG
  have hBq : 0 ≤ B ^ (2 * q) := by positivity
  calc n0 * G ^ D.R.k * X * P ≤ n0 * (wt * Mx) * X * P := by gcongr
    _ = n0 * (wt * X) * P * Mx := by ring
    _ ≤ B1 * R * B ^ (2 * q) * Mx := by gcongr
    _ = (B1 * Mx * large₂.sc.b ^ (Cc * (D.R.m : ℝ) ^ 2)) * ti * dim * B ^ (2 * q) := by rw [hR]; ring
    _ ≤ lossV large₂.sc.b C D.R.m W.z W.z' γ p * ti * dim * B ^ (2 * q) := by gcongr

theorem L2_decay_of_admissible (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A Cn C1 CPT CDl Cc Cpr C Ch : ℝ)
    (hCn : 0 ≤ Cn) (hCpr : Cpr ≤ Cn) (hC : max CPT 0 + max Cc 0 + 6 ≤ C) (hCh0 : 0 ≤ Ch) (hCh : CDl ≤ Ch)
    (hA1 : VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT)
    (hA2 : VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl)
    (hP1 : VanishingOnXAndXPlusBranching.Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 C1 Cc) :
    L2WithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch := by
  intro τ w w' hTT θ hθ W hGW S hGS hdeg γ p hRel θ' hθ' νR hν hHyp q hq
  have hL2 := weightStatement_holds D large₂ C' Cl Cg cb Cu cT CT C0 A Cn C1 CPT Cc C hCn hC hA1 hP1 τ w w' hTT θ hθ W hGW S hGS hdeg
    γ p hRel θ' hθ' νR hν hHyp
  beta_reduce at hL2
  have hb := one_le_b large₂
  have hGW2 := hGW
  obtain ⟨_, _, hz, hz', hTz, hTz', _⟩ := hGW2
  have hT : 0 < Tr D w := by
    unfold Tr; exact_mod_cast hTT.1.pos
  have hT' : 0 < Tr D w' := by
    unfold Tr; exact_mod_cast hTT.2.1.pos
  have hG : 0 < Gf D.R.k D.R.rS W.z W.z' γ :=
    cell_G_pos D hRel hz hz' (by rw [hTz]; exact hT) (by rw [hTz']; exact hT')
  have hC0 : 0 ≤ C := by
    have := le_max_right CPT 0
    have := le_max_right Cc 0
    linarith
  have hloss0 : 0 ≤ lossV large₂.sc.b C D.R.m W.z W.z' γ p :=
    le_trans zero_le_one (one_le_lossV large₂.sc.b D.R.m W.z W.z' γ p hb hC0 hG (fun l hl => cell_ne_of_mem D hRel l hl))
  have hti0 : 0 ≤ (tvPr D τ w' ^ D.R.k)⁻¹ := inv_nonneg.2 (D.R.k_even.pow_nonneg _)
  have hZ : 0 ≤ lossV large₂.sc.b C D.R.m W.z W.z' γ p * (tvPr D τ w' ^ D.R.k)⁻¹ := mul_nonneg hloss0 hti0
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hH1 : 1 ≤ scalePowQuadraticExponent D large₂ Ch := by
    unfold scalePowQuadraticExponent; exact Real.one_le_rpow hb (by positivity)
  have hBH : large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) ≤ scalePowQuadraticExponent D large₂ Ch := by
    unfold scalePowQuadraticExponent
    exact Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right hCh (by positivity))
  have hd0 : ‖Dmin D.R.k D.R.rS W.z W.z' γ 0‖ ≤ scalePowQuadraticExponent D large₂ Ch := by
    have : Dmin D.R.k D.R.rS W.z W.z' γ 0 = 1 := by
      unfold Dmin
      exact Matrix.det_eq_one_of_card_eq_zero (Fintype.card_fin 0)
    rw [this, norm_one]; exact hH1
  unfold sizeV
  refine threshold_bound_even_decay D.R.rS q (fun l => ‖Dmin D.R.k D.R.rS W.z W.z' γ l‖) (scalePowQuadraticExponent D large₂ Ch)
    (large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2)) _ _ hH1 hd0 (Real.rpow_nonneg (by linarith) _) hBH hZ hL2 (fun l => ?_)
  have hle : (l : ℕ) ≤ D.R.rS + 1 := Nat.le_of_lt_succ l.isLt
  have hlm : ((l : ℕ) : ℝ) ≤ D.R.m := by
    have := rank_eq_two_mul_add_two D
    exact_mod_cast (by omega : (l : ℕ) ≤ D.R.m)
  have hrange : (q : ℝ) * ((l : ℕ) : ℝ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := by
    have h1 : (q : ℝ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 2 :=
      le_trans hq (by gcongr)
    calc (q : ℝ) * ((l : ℕ) : ℝ) ≤ (Cn * D.R.k * (D.R.m : ℝ) ^ 2) * D.R.m :=
          mul_le_mul h1 hlm (Nat.cast_nonneg _) (by positivity)
      _ = Cn * D.R.k * (D.R.m : ℝ) ^ 3 := by ring
  have hcore := L2_decay_pointwise_estimate D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 (max CPT 0) CDl (max Cc 0) C (le_max_right _ _)
    (le_max_right _ _) hC (weight_admissible_mono D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT _ (le_max_left _ _) hA1) hA2
    (constant_bound_mono D large₂ C' Cl Cg cb Cu cT CT C0 C1 Cc _ (le_max_left _ _) hP1) hHyp.1 τ w w' hTT θ hθ W hGW S hGS hdeg
    γ p hRel θ' hθ' νR hν (l : ℕ) hle q hrange
  have hDe : DminN W.z W.z' γ (l : ℕ) = Dmin D.R.k D.R.rS W.z W.z' γ l := by
    unfold DminN; rw [dif_pos l.isLt]
  rw [hDe] at hcore
  rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) (Module.finrank ℂ W.Wp)) with hd | hd
  · rw [← hd, div_zero, zero_mul]
    exact mul_nonneg hZ (by positivity)
  · rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    calc _ ≤ _ := hcore
      _ = _ := by ring

end Formalism.MainNotions.BridgeLemma

end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.LatticeSumBounds

theorem scaled_div_le_of_mul (a h d B s : ℝ) (hs : 0 < s) (H : a * h / d ≤ B * s ^ 2) : a * (h / s ^ 2) / d ≤ B := by
  have e : a * (h / s ^ 2) / d = a * h / d / s ^ 2 := by ring
  rw [e, div_le_iff₀ (by positivity)]
  exact H

theorem mul_div_le_of_scaled (a h d X s : ℝ) (hs : 0 < s) (H : a * (h / s ^ 2) / d ≤ X) : a * h / d ≤ X * s ^ 2 := by
  have e : a * (h / s ^ 2) / d = a * h / d / s ^ 2 := by ring
  rw [e, div_le_iff₀ (by positivity)] at H
  exact H

theorem mul_div_le_of_scaled_four (a h R T d X s : ℝ) (hs : 0 < s) (H : a * (h / s ^ 2) * R * T / d ≤ X) :
    a * h * R * T / d ≤ X * s ^ 2 := by
  have e : a * (h / s ^ 2) * R * T / d = a * h * R * T / d / s ^ 2 := by ring
  rw [e, div_le_iff₀ (by positivity)] at H
  exact H

theorem mul_div_le_of_scaled_three (a h T d X s : ℝ) (hs : 0 < s) (H : a * (h / s ^ 2) * T / d ≤ X) :
    a * h * T / d ≤ X * s ^ 2 := by
  have e : a * (h / s ^ 2) * T / d = a * h * T / d / s ^ 2 := by ring
  rw [e, div_le_iff₀ (by positivity)] at H
  exact H

theorem div_le_of_le_mul_alt (J P s : ℝ) (hs : 0 < s) (H : J ≤ P * s) : J / s ≤ P := by
  rw [div_le_iff₀ hs]; exact H

theorem div_sq_le_mul_div_sq (h d J s : ℝ) (hs : 0 < s) (H : h ≤ d * J ^ 2) : h / s ^ 2 ≤ d * (J / s) ^ 2 := by
  rw [div_pow, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right H (by positivity)

theorem decayProp_of_l2AbsDecay (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A C1 Cpr Ca C Ch δ : ℝ)
    (h2 : 2 ≤ Ca) (hCaC : Ca ≤ C) (hCk : C ≤ D.R.k) (hδ : (D.R.rS : ℝ) + 2 ≤ δ * D.R.k)
    (hA : 6 * Real.exp 1 * Real.pi * A ≤ C)
    (h5 : VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0)
    (hL2 : HilbertSchmidtBoundWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr Ca Ch)
    (hABS : AbsWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr Ca Ch) :
    VanishingOnXAndXPlusBranching.division_rows_rational_lattice D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ := by
  intro τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH q hq
  have hL2' := hL2 τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH q hq
  have hABS' := hABS τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH q hq
  obtain ⟨hH0, hStand, hTA, -⟩ := hH
  have hlow := h5 hH0 w' τ
  obtain ⟨_, _, hmf, hfk, _, _, _, _, _, _, _, hg1, _, hg2, _, _, _, _, hv, -⟩ := hH0.1
  obtain ⟨_, _, hz, hz', hTz, hTz', -⟩ := hW
  have hr : 1 ≤ D.R.rS := hStand.1
  have hk := rank_lower_bound D
  have hb := one_le_scale_base_local large₂
  have hm := rank_eq_two_mul_add_two D
  have hm0 : 0 < D.R.m := by omega
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
  have hv0 : 0 < D.host.v := lt_of_lt_of_le one_pos hv
  have hT : 0 < Tr D w := by unfold Tr; exact_mod_cast hTT.1.pos
  have hT' : 0 < Tr D w' := by unfold Tr; exact_mod_cast hTT.2.1.pos
  have hG : 0 < Gf D.R.k D.R.rS W.z W.z' γ := cell_G_pos D hRel hz hz' (hTz ▸ hT) (hTz' ▸ hT')
  have hkb : (1 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    have : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le this hb)
  have hg : 1 ≤ gg D := by
    unfold gg
    exact one_le_mul_of_one_le_of_one_le (hkb.trans hg1) (hkb.trans hg2)
  have hg0 : 0 < gg D := lt_of_lt_of_le one_pos hg
  have hkπ : Real.exp 1 * Real.pi ≤ D.R.k := by
    have h256 : 256 ≤ D.R.k := by
      have h4 : 4 ≤ D.R.m := by omega
      have : 4 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left h4 4
      omega
    have h256' : (256 : ℝ) ≤ D.R.k := by exact_mod_cast h256
    exact le_trans (le_trans exp_one_mul_pi_lt_nine.le (by norm_num)) h256'
  have hCa : 0 < Ca := lt_of_lt_of_le two_pos h2
  have hTc : 0 < Tcrit D w' τ := by
    have h1 : 0 < gg D ^ (-(D.R.m : ℝ)) * Tcrit D w' τ := lt_of_lt_of_le (by positivity) hlow
    exact (pos_iff_pos_of_mul_pos h1).1 (Real.rpow_pos_of_pos hg0 _)
  have ht : 0 < tvPr D τ w' := by unfold tvPr; positivity
  have hlow' : (D.R.k : ℝ) ^ (3 * D.R.rS) ≤ (gg D)⁻¹ ^ (2 * D.R.rS + 2) * Tr D w' * tvPr D τ w' := by
    rw [← level_rpow_neg_rank_eq D hg0, mul_assoc]
    unfold tvPr
    rw [mul_div_cancel₀ _ hT'.ne']
    exact hlow
  have hall : ∀ l ∈ ptBlockEnds p, DminN W.z W.z' γ l ≠ 0 := fun l hl => cell_ne_of_mem D hRel l hl
  have hla0 := loss_volume_nonneg large₂.sc.b D.R.m W.z W.z' γ p hb Ca hG
  have hlac := loss_volume_mono_constant large₂.sc.b D.R.m W.z W.z' γ p hb hm0 hCa hCaC hG
  have hpa := one_le_loss_factor large₂.sc.b D.R.m W.z W.z' γ p hb hCa.le
  have hpac := local_loss_mono_constant large₂.sc.b D.R.m W.z W.z' γ p hb hCa.le hCaC
  have hhs := hs_norm_sq_nonneg (S.J νR γ)
  have hrank := hs_norm_sq_le_rank_mul_norm (S.J νR γ)
  have hTA' : Tr D w' / Tr D w ≤ A := hTA
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hTA'
  have hAC : A ≤ C := le_of_exp_pi_mul_le A C hA0 hA
  have hC0 : 0 ≤ C := hA0.le.trans hAC

  have hSz : 1 ≤ sizeV (scalePowQuadraticExponent D large₂ Ch) W.z W.z' γ := one_le_size_volume _ _ _ _
  obtain ⟨s, hsdef⟩ : ∃ s, s = sizeV (scalePowQuadraticExponent D large₂ Ch) W.z W.z' γ ^ (-((q : ℝ) / ((D.R.rS : ℝ) + 1))) := ⟨_, rfl⟩
  have hs0 : 0 < s := hsdef ▸ Real.rpow_pos_of_pos (by linarith) _
  have hs2 : sizeV (scalePowQuadraticExponent D large₂ Ch) W.z W.z' γ ^ (-(2 * (q : ℝ) / ((D.R.rS : ℝ) + 1))) = s ^ 2 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    push_cast
    ring
  rw [hs2] at hL2'
  rw [← hsdef] at hABS'
  rw [hs2, ← hsdef]
  refine ⟨?_, ?_, ?_⟩
  ·
    exact hL2'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlac (by positivity)) (by positivity))
  ·
    intro hD
    refine (hABS' hD).trans ?_
    have hq1 : (Ca / (D.R.k * D.host.v)) ^ (D.R.rS * (D.R.k - 2 - D.R.rS)) ≤
        (C / (D.R.k * D.host.v)) ^ (D.R.rS * (D.R.k - 2 - D.R.rS)) :=
      pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hCaC (by positivity)) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul hpac hq1 (by positivity) (by linarith)) (by positivity)) hs0.le

  rw [local_volume_eq_weight D w _ hg0, ← inv_pow] at hL2'
  rw [local_volume_eq_weight D w _ hg0, ← inv_pow, ← inv_pow]
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ W.Wp) with hd0 | hd0
  · have hlc := hla0.trans hlac
    rw [hd0]
    simp only [Nat.cast_zero, div_zero]
    have hamp : 0 ≤ ampMinF D C δ τ w w' W.z W.z' γ := by
      unfold ampMinF
      split_ifs
      · exact zero_le_one
      · refine le_min zero_le_one ?_
        unfold nuV
        positivity
    exact ⟨by positivity, by positivity⟩
  have hdim : (0 : ℝ) < Module.finrank ℂ W.Wp := by exact_mod_cast hd0
  have hL2s := scaled_div_le_of_mul _ _ _ _ s hs0 hL2'
  have hhs' : 0 ≤ hsNormSq (S.J νR γ) / s ^ 2 := by positivity
  by_cases hD : DminN W.z W.z' γ D.R.rS = 0
  · have e1 : ampMinF D C δ τ w w' W.z W.z' γ = 1 := by unfold ampMinF; rw [if_pos hD]
    have e2 : chRatio (Tr D w) (Tr D w') W.z W.z' γ = 1 := by unfold chRatio; rw [if_pos hD]
    rw [e1, e2, one_pow, one_pow, mul_one, mul_one]
    refine ⟨mul_div_le_of_scaled _ _ _ _ s hs0 (hL2s.trans (product_le_enlarged_losses _ _ _ _ _ hla0 hlac hpa hpac (by positivity))), ?_⟩
    exact mul_div_le_of_scaled_three _ _ _ _ _ s hs0
      (numericVolume_bound_ii D.R.k D.R.rS C A _ _ _ _ _ _ _ _ _ _ _ _ hr (by omega) hAC hG hT hT' hg hv0 ht hla0 hlac
        hpa hpac hhs' hdim hTA' hlow' hL2s)
  · have hDr : 0 < ‖DminN W.z W.z' γ D.R.rS‖ := norm_pos_iff.2 hD
    have hmem : D.R.rS ∈ ptBlockEnds p := cell_mem_blockEnds D hRel D.R.rS hr (by omega) hD
    have hDl : ‖DminN W.z W.z' γ D.R.rS‖ ^ (2 * D.R.rS + 4) ≤ lossV large₂.sc.b Ca D.R.m W.z W.z' γ p := by
      refine minor_power_le_loss large₂.sc.b D.R.m W.z W.z' γ p hb hCa.le hG hall D.R.rS hmem _ ?_
      have hmr : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by exact_mod_cast hm
      push_cast
      exact exponent_le_constant_mul _ _ Ca hmr (Nat.cast_nonneg _) h2
    have hABS'' := hABS' hD
    rw [← inv_pow] at hABS''
    have hABSs := div_le_of_le_mul_alt _ _ s hs0 hABS''
    have hranks := div_sq_le_mul_div_sq _ _ _ s hs0 hrank
    have hJ' : 0 ≤ ‖S.J νR γ‖ / s := by positivity
    have e1 : ampMinF D C δ τ w w' W.z W.z' γ =
        min 1 (Gf D.R.k D.R.rS W.z W.z' γ / (Tr D w * ‖DminN W.z W.z' γ D.R.rS‖ ^ 2) * tvPr D τ w' *
          (gg D)⁻¹ ^ (2 * D.R.rS + 2) * (C / D.R.k) ^ (2 * (D.R.rS : ℝ) * (1 - δ))) := by
      unfold ampMinF nuV; rw [if_neg hD, level_rpow_neg_rank_eq D hg0]
    have e2 : chRatio (Tr D w) (Tr D w') W.z W.z' γ =
        (1 + chV (Tr D w) (Tr D w') W.z W.z' γ) / shV (Tr D w) (Tr D w') W.z W.z' γ := by
      unfold chRatio; rw [if_neg hD]
    obtain ⟨hsh, hch, hcs, hGs⟩ := hyperbolic_parameters_of_minor (Tr D w) (Tr D w') W.z W.z' γ hT hT' hTz hTz' hD hG
    rw [e1, e2]
    refine ⟨?_, ?_⟩
    · exact mul_div_le_of_scaled _ _ _ _ s hs0
        (numerical_bound_first_case D.R.k D.R.rS Ca C δ _ _ _ _ _ _ _ _ _ _ _ (‖S.J νR γ‖ / s) _ (by omega) hkπ hCa hCaC hCk hδ hG hT hg0 hv ht
          hDr hlac hpa hpac hhs' hJ' hdim hDl hL2s hABSs hranks)
    · exact mul_div_le_of_scaled_four _ _ _ _ _ _ s hs0
        (numerical_bound_second_case D.R.k D.R.rS Ca C A _ _ _ _ _ _ _ _ _ _ _ _ _ _ (‖S.J νR γ‖ / s) _ hr hk hCa hCaC hCk hA hG hT hT' hg hv ht
          hDr hlac hpa hpac hhs' hJ' hdim hDl hsh hch hcs hGs hTA' hlow' hL2s hABSs hranks)

theorem abs_bound_of_zero_decay (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A C1 Ca Ch : ℝ)
    (h : AbsWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 A C1 0 Ca Ch) : VanishingOnXAndXPlusBranching.Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Ca := by
  intro τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH hD
  have h0 := h τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH 0 (by simp) hD
  simpa using h0

theorem size_volume_antitone_height {k r : ℕ} {H H' : ℝ} (hH : 0 < H) (h : H ≤ H') (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) :
    sizeV H' z z' γ ≤ sizeV H z z' γ := by
  unfold sizeV
  refine Finset.prod_le_prod (fun l _ => le_trans zero_le_one (le_max_left _ _)) (fun l _ => ?_)
  exact max_le_max le_rfl (div_le_div_of_nonneg_left (norm_nonneg _) hH h)

theorem height_constant_mono_pos (D : D7) (large₂ : SizeData₂ D) {Ch Ch' : ℝ} (h : Ch ≤ Ch') :
    0 < scalePowQuadraticExponent D large₂ Ch ∧ scalePowQuadraticExponent D large₂ Ch ≤ scalePowQuadraticExponent D large₂ Ch' := by
  have hb := one_le_scale_base_local large₂
  unfold scalePowQuadraticExponent
  exact ⟨Real.rpow_pos_of_pos (by linarith) _,
    Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right h (by positivity))⟩

theorem decay_factor_mono_height (D : D7) (large₂ : SizeData₂ D) {Ch Ch' a : ℝ} (h : Ch ≤ Ch') (ha : 0 ≤ a)
    (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (γ : MatKR D.R.k D.R.rS) :
    sizeV (scalePowQuadraticExponent D large₂ Ch) z z' γ ^ (-a) ≤ sizeV (scalePowQuadraticExponent D large₂ Ch') z z' γ ^ (-a) := by
  obtain ⟨h0, h1⟩ := height_constant_mono_pos D large₂ h
  exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (one_le_size_volume _ _ _ _))
    (size_volume_antitone_height h0 h1 z z' γ) (by linarith)

theorem abs_decay_mono_constants (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 A C1 Cpr Ca C Ch Ch' : ℝ} (hCa : 0 ≤ Ca)
    (hC : Ca ≤ C) (hCh : Ch ≤ Ch') (H : AbsWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr Ca Ch) :
    AbsWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch' := by
  intro τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH q hq hD
  refine (H τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH q hq hD).trans ?_
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, -⟩ := hH.1.1
  have hv0 : 0 < D.host.v := lt_of_lt_of_le one_pos hv
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hb := one_le_scale_base_local large₂
  have hpa := one_le_loss_factor large₂.sc.b D.R.m W.z W.z' γ p hb hCa
  have hpac := local_loss_mono_constant large₂.sc.b D.R.m W.z W.z' γ p hb hCa hC
  have hq1 : (Ca / (D.R.k * D.host.v)) ^ (D.R.rS * (D.R.k - 2 - D.R.rS)) ≤
      (C / (D.R.k * D.host.v)) ^ (D.R.rS * (D.R.k - 2 - D.R.rS)) :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hC (by positivity)) _
  have hf := decay_factor_mono_height D large₂ hCh (show 0 ≤ (q : ℝ) / ((D.R.rS : ℝ) + 1) by positivity) W.z W.z' γ
  have hC0 : 0 ≤ C := hCa.trans hC
  refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul hpac hq1 (by positivity) (by linarith)) (by positivity)) hf
    (Real.rpow_nonneg (le_trans zero_le_one (one_le_size_volume _ _ _ _)) _) ?_
  have : 0 ≤ lossP large₂.sc.b C D.R.m W.z W.z' γ p := by linarith
  positivity

section Fam

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.MainNotions.BridgeLemma

end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt MeasureTheory
open scoped ENNReal

theorem rpow_neg_half_eq_sqrt_inv {x : ℝ} (hx : 0 < x) : x ^ (-(1 / 2 : ℝ)) = Real.sqrt x⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.sqrt_inv, Real.sqrt_eq_rpow]

theorem formal_degree_pos (D : D7) {W : LocW D.R.k D.R.rS} {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (h : GoodS D lam A) : 0 < A.deg := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, P, _, hF⟩ := h
  exact hF.1

theorem degree_ratio_iteration_alt (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 Cn C1 CDl : ℝ}
    (hA2 : VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl) (hH0 : Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    (τ : D.what₂.Tau) (w w' : D.what₂.Word) (hTT : HypTT D w w') (θ : ℝ) (hθ : normWin D large₂ C1 θ)
    (W : LocW D.R.k D.R.rS) (hGW : GoodW D τ w w' θ W) (l : ℕ) (hl : l ≤ D.R.rS + 1)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (hμ : IsSection D.R.k D.R.rS W.z W.z' μsec)
    (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)) (hRel : RelPt D W.z W.z' γ p) (θ' : ℝ)
    (hθ' : normWin D large₂ C1 θ') (νR : Measure (Mt D.R.k D.R.rS)) (hν : RMeas D W γ θ' νR)
    (cf : LocS W → ℝ) (E M : ℝ) (hE : 0 ≤ E) (hM : 0 ≤ M) (hcf : ∀ A, 0 ≤ cf A)
    (hK : ∀ (lam'' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W),
      l1dist lam'' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → GoodS D lam'' A →
      ‖jhUnit D w w' A μsec νR γ‖ ≤ cf A * M)
    (hstep : ∀ (lam'' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W),
      l1dist lam'' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → GoodS D lam'' A →
      ∀ (I : Finset (Fin (2 * D.R.rS + D.R.k + 1))) (s : ℝ), I.card = l → (s = 1 ∨ s = -1) →
        ∀ A' : LocS W, GoodS D (lam'' + s • epsI I) A' → cf A' ≤ E * cf A) :
    ∀ (j : ℕ) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A₀ : LocS W), GoodS D lam' A₀ →
      l1dist lam' (lamD D τ) + (j : ℝ) * l ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
      ‖DminN W.z W.z' γ l‖ ^ j * ‖jhUnit D w w' A₀ μsec νR γ‖ ≤
        (large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) * E) ^ j * (cf A₀ * M) := by
  intro j
  induction j with
  | zero =>
    intro lam' A₀ hG hr
    simpa using hK lam' A₀ (by simpa using hr) hG
  | succ j ih =>
    intro lam' A₀ hG hr
    have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
    have hr0 : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := by
      have : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * l := by positivity
      linarith
    obtain ⟨s, hs, H⟩ := hA2 hH0 τ w w' hTT θ hθ W hGW lam' hr0 A₀ hG l hl
    classical
    obtain ⟨a, ha0, hasum, haeq⟩ := H
      (fun I => if h : ∃ A : LocS W, GoodS D (lam' + s • epsI I) A then h.choose else A₀)
      (fun I _ h => by simp only [dif_pos h]; exact h.choose_spec)
    have heq := haeq μsec hμ γ p hRel θ' hθ' νR hν
    have hb0 : 0 < large₂.sc.b := lt_of_lt_of_le one_pos (one_le_b large₂)
    have hB0 : 0 ≤ large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) := Real.rpow_nonneg hb0.le _
    have hc0 := hcf A₀
    calc ‖DminN W.z W.z' γ l‖ ^ (j + 1) * ‖jhUnit D w w' A₀ μsec νR γ‖
        = ‖DminN W.z W.z' γ l‖ ^ j * ‖DminN W.z W.z' γ l • jhUnit D w w' A₀ μsec νR γ‖ := by
          rw [norm_smul]; ring
      _ ≤ large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) *
            ((large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) * E) ^ j * (E * cf A₀ * M)) := by
          rw [heq]
          refine weighted_sum_norm_le _ a _ _ _ _ (by positivity) (by positivity) hasum (fun I hI => ?_)
          have hc : I.card = l := (Finset.mem_filter.1 hI).2
          by_cases hex : ∃ A : LocS W, GoodS D (lam' + s • epsI I) A
          · right
            have hgood : GoodS D (lam' + s • epsI I)
                (if h : ∃ A : LocS W, GoodS D (lam' + s • epsI I) A then h.choose else A₀) := by
              simp only [dif_pos hex]; exact hex.choose_spec
            refine (ih _ _ hgood ?_).trans ?_
            · have h1 := l1_distance_sign_step lam' (lamD D τ) s hs I
              rw [hc] at h1
              push_cast at hr
              linarith
            · have h2 := hstep lam' A₀ hr0 hG I s hc hs _ hgood
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hM) (by positivity)
          · left
            exact ha0 I hc hex
      _ = (large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) * E) ^ (j + 1) * (cf A₀ * M) := by ring

theorem threshold_bound_size_decay (r N : ℕ) (d : Fin (r + 2) → ℝ) (H B Y Z : ℝ) (hH : 1 ≤ H) (hd0 : d 0 ≤ H)
    (hB0 : 0 ≤ B) (hBH : B ≤ H) (hZ : 0 ≤ Z) (h0 : Y ≤ Z) (h : ∀ l, Y * d l ^ N ≤ Z * B ^ N) :
    Y ≤ Z * (∏ l, max 1 (d l / H)) ^ (-((N : ℝ) / ((r : ℝ) + 1))) := by
  have hH0 : 0 < H := by linarith
  obtain ⟨ls, -, hls⟩ := Finset.exists_max_image Finset.univ d ⟨0, Finset.mem_univ _⟩
  rcases le_or_gt (d ls) H with hc | hc
  · have : ∏ l, max 1 (d l / H) = 1 := Finset.prod_eq_one (fun l _ =>
      max_eq_left ((div_le_one hH0).2 (le_trans (hls l (Finset.mem_univ _)) hc)))
    rw [this, Real.one_rpow, mul_one]
    exact h0
  · have ht1 : 1 < d ls / H := (one_lt_div hH0).2 hc
    have ht0 : 0 < d ls / H := by linarith
    have hf : ∀ l, max 1 (d l / H) ≤ d ls / H := fun l =>
      max_le ht1.le (div_le_div_of_nonneg_right (hls l (Finset.mem_univ _)) hH0.le)
    have hsz : ∏ l, max 1 (d l / H) ≤ (d ls / H) ^ (r + 1) := by
      rw [Fin.prod_univ_succ, max_eq_left ((div_le_one hH0).2 hd0), one_mul]
      calc ∏ i : Fin (r + 1), max 1 (d i.succ / H) ≤ ∏ _i : Fin (r + 1), d ls / H :=
            Finset.prod_le_prod (fun i _ => le_trans zero_le_one (le_max_left _ _)) (fun i _ => hf _)
        _ = (d ls / H) ^ (r + 1) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hs1 : 0 < ∏ l, max 1 (d l / H) :=
      Finset.prod_pos (fun l _ => lt_of_lt_of_le one_pos (le_max_left _ _))
    have he : ((d ls / H) ^ (r + 1)) ^ (-((N : ℝ) / ((r : ℝ) + 1))) = ((d ls / H) ^ N)⁻¹ := by
      rw [← Real.rpow_natCast (d ls / H) (r + 1), ← Real.rpow_mul ht0.le, ← Real.rpow_natCast (d ls / H) N,
        ← Real.rpow_neg ht0.le]
      congr 1
      push_cast
      field_simp
    have hmono : ((d ls / H) ^ (r + 1)) ^ (-((N : ℝ) / ((r : ℝ) + 1))) ≤
        (∏ l, max 1 (d l / H)) ^ (-((N : ℝ) / ((r : ℝ) + 1))) :=
      Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by
        have : (0 : ℝ) ≤ (N : ℝ) / ((r : ℝ) + 1) := by positivity
        linarith) (Set.mem_Ioi.2 hs1) (Set.mem_Ioi.2 (lt_of_lt_of_le hs1 hsz)) hsz
    have hdl : 0 < d ls := by linarith
    have h1 : Y ≤ Z * ((d ls / H) ^ N)⁻¹ := by
      have hp : 0 < d ls ^ N := by positivity
      have h3 : Y ≤ Z * B ^ N / d ls ^ N := by rw [le_div_iff₀ hp]; exact h ls
      refine h3.trans ?_
      rw [div_pow, inv_div, mul_div_assoc]
      have h4 : B ^ N ≤ H ^ N := pow_le_pow_left₀ hB0 hBH _
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h4 hp.le) hZ
    calc Y ≤ Z * ((d ls / H) ^ N)⁻¹ := h1
      _ = Z * ((d ls / H) ^ (r + 1)) ^ (-((N : ℝ) / ((r : ℝ) + 1))) := by rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmono hZ

theorem abs_decay_of_all_parameters (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A Cn C1 CDl hilbertNinetyConstant Cpr Ca Ch : ℝ)
    (hCn : 0 ≤ Cn) (hCpr : Cpr ≤ Cn) (hCa : 0 ≤ Ca) (hilbertNinetyConstant_pos : 0 ≤ hilbertNinetyConstant) (hCh0 : 0 ≤ Ch) (hCh : CDl + 1 ≤ Ch)
    (hn : (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) ≤ large₂.sc.b ^ (2 * (D.R.m : ℝ) ^ 2))
    (hA2 : VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl)
    (hA9 : VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1)
    (hDeg : DegreeRatioUnitShiftBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant)
    (hAbs : AbsAllParameters D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cn Ca) :
    AbsWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr Ca Ch := by
  intro τ w w' hTT θ hθ W hGW S hGS hdeg γ p hRel θ' hθ' νR hν hHyp q hq hDr
  have hH0 := hHyp.1
  have hb := one_le_b large₂
  have hb0 : 0 < large₂.sc.b := lt_of_lt_of_le one_pos hb
  have hGW2 := hGW
  obtain ⟨_, _, hz, hz', hTz, hTz', _⟩ := hGW2
  have hT : 0 < Tr D w := by
    unfold Tr; exact_mod_cast hTT.1.pos
  have hT' : 0 < Tr D w' := by
    unfold Tr; exact_mod_cast hTT.2.1.pos
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨μsec, hμ⟩ := Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists D.R.k D.R.rS W.z W.z' hk1 hz hz' (by rw [hTz]; exact hT)
    (by rw [hTz']; exact hT')
  obtain ⟨K, hK0, hKe⟩ := hA9 hH0 τ w w' hTT θ hθ W hGW μsec hμ
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, -⟩ := hH0.1
  have hv0 : 0 < D.host.v := lt_of_lt_of_le one_pos hv
  have hl00 : l1dist (lamD D τ) (lamD D τ) = 0 := by
    unfold l1dist; simp
  have hR0 : 0 ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := by positivity
  set M := lossP large₂.sc.b Ca D.R.m W.z W.z' γ p *
      (Ca / (D.R.k * D.host.v)) ^ (D.R.rS * (D.R.k - 2 - D.R.rS)) *
      (‖DminN W.z W.z' γ D.R.rS‖ ^ (D.R.k - 2 - D.R.rS))⁻¹ with hMd
  have hM0 : 0 ≤ M := by
    have h1 : 0 ≤ lossP large₂.sc.b Ca D.R.m W.z W.z' γ p :=
      le_trans zero_le_one (one_le_lossP large₂.sc.b D.R.m W.z W.z' γ p hb hCa)
    have h2 : 0 ≤ Ca / (D.R.k * D.host.v) := div_nonneg hCa (mul_nonneg hk0 hv0.le)
    positivity
  have hJ : ∀ (lam'' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A' : LocS W),
      l1dist lam'' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → GoodS D lam'' A' → ‖A'.J νR γ‖ ≤ M :=
    fun lam'' A' hr hA' => hAbs τ w w' hTT θ hθ W hGW lam'' hr A' hA' γ p hRel θ' hθ' νR hν hHyp hDr

  have hjh : ∀ (lam'' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A' : LocS W),
      l1dist lam'' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → GoodS D lam'' A' →
      ‖jhUnit D w w' A' μsec νR γ‖ = Real.sqrt (A'.deg / K) * ‖A'.J νR γ‖ := by
    intro lam'' A' hr hA'
    have hd := formal_degree_pos D hA'
    have hpos : 0 < K / A'.deg := div_pos hK0 hd
    unfold jhUnit
    rw [hKe lam'' hr A' hA', ENNReal.toReal_ofReal hpos.le, rpow_neg_half_eq_sqrt_inv hpos, inv_div, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hr1 : (1 : ℝ) ≤ D.R.r := by
    have h2 := D.R.two_le_m
    have : 1 ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  set E := Real.sqrt ((D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ))) with hEd
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  have hH1 : 1 ≤ scalePowQuadraticExponent D large₂ Ch := by
    unfold scalePowQuadraticExponent; exact Real.one_le_rpow hb (by positivity)
  have hEb : E ≤ large₂.sc.b ^ ((D.R.m : ℝ) ^ 2) := by
    rw [hEd]
    refine Real.sqrt_le_iff.2 ⟨Real.rpow_nonneg hb0.le _, hn.trans (le_of_eq ?_)⟩
    rw [← Real.rpow_mul_natCast hb0.le]
    congr 1
    push_cast
    ring
  have hBH : large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) * E ≤ scalePowQuadraticExponent D large₂ Ch := by
    unfold scalePowQuadraticExponent
    calc large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) * E
        ≤ large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) * large₂.sc.b ^ ((D.R.m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hEb (Real.rpow_nonneg hb0.le _)
      _ = large₂.sc.b ^ ((CDl + 1) * (D.R.m : ℝ) ^ 2) := by
          rw [← Real.rpow_add hb0]; congr 1; ring
      _ ≤ large₂.sc.b ^ (Ch * (D.R.m : ℝ) ^ 2) :=
          Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right hCh (by positivity))
  have hd0 : ‖Dmin D.R.k D.R.rS W.z W.z' γ 0‖ ≤ scalePowQuadraticExponent D large₂ Ch := by
    have : Dmin D.R.k D.R.rS W.z W.z' γ 0 = 1 := by
      unfold Dmin
      exact Matrix.det_eq_one_of_card_eq_zero (Fintype.card_fin 0)
    rw [this, norm_one]; exact hH1
  unfold sizeV
  refine threshold_bound_size_decay D.R.rS q (fun l => ‖Dmin D.R.k D.R.rS W.z W.z' γ l‖) (scalePowQuadraticExponent D large₂ Ch)
    (large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) * E) _ _ hH1 hd0 (mul_nonneg (Real.rpow_nonneg hb0.le _) hE0) hBH hM0
    (hJ (lamD D τ) S (by rw [hl00]; exact hR0) hGS) (fun l => ?_)
  have hle : (l : ℕ) ≤ D.R.rS + 1 := Nat.le_of_lt_succ l.isLt
  have hlmN : (l : ℕ) ≤ D.R.m := by
    have := rank_eq_two_mul_add_two D
    omega
  have hlm : ((l : ℕ) : ℝ) ≤ D.R.m := by exact_mod_cast hlmN
  have hrange : (q : ℝ) * ((l : ℕ) : ℝ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := by
    have h1 : (q : ℝ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 2 :=
      le_trans hq (by gcongr)
    calc (q : ℝ) * ((l : ℕ) : ℝ) ≤ (Cn * D.R.k * (D.R.m : ℝ) ^ 2) * D.R.m :=
          mul_le_mul h1 hlm (Nat.cast_nonneg _) (by positivity)
      _ = Cn * D.R.k * (D.R.m : ℝ) ^ 3 := by ring
  have hit := degree_ratio_iteration_alt D large₂ hA2 hH0 τ w w' hTT θ hθ W hGW (l : ℕ) hle μsec hμ γ p hRel θ' hθ' νR hν
    (fun A' => Real.sqrt (A'.deg / K)) E M hE0 hM0 (fun _ => Real.sqrt_nonneg _)
    (fun lam'' A' hr hA' => by
      rw [hjh lam'' A' hr hA']
      exact mul_le_mul_of_nonneg_left (hJ lam'' A' hr hA') (Real.sqrt_nonneg _))
    (fun lam'' A₁ hr hA₁ I s hc hs A₂ hA₂ => by
      have h1 := hDeg hH0 τ w w' hTT θ hθ W hGW lam'' hr A₁ hA₁ I s hs A₂ hA₂
      have hd1 := formal_degree_pos D hA₁
      have h2 : (D.R.r : ℝ) ^ (hilbertNinetyConstant * (I.card : ℝ)) ≤ (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hr1 (mul_le_mul_of_nonneg_left (by rw [hc]; exact hlm) hilbertNinetyConstant_pos)
      have h3 : A₂.deg ≤ (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) * A₁.deg := by
        rw [← div_le_iff₀ hd1]; exact h1.trans h2
      rw [hEd, ← Real.sqrt_mul (Real.rpow_nonneg (by linarith) _)]
      refine Real.sqrt_le_sqrt ?_
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right h3 hK0.le)
    q (lamD D τ) S hGS (by rw [hl00, zero_add]; exact hrange)
  have hDe : DminN W.z W.z' γ (l : ℕ) = Dmin D.R.k D.R.rS W.z W.z' γ l := by
    unfold DminN; rw [dif_pos l.isLt]
  rw [hDe, hjh (lamD D τ) S (by rw [hl00]; exact hR0) hGS] at hit
  have hc0 : 0 < Real.sqrt (S.deg / K) := Real.sqrt_pos.2 (div_pos (formal_degree_pos D hGS) hK0)
  have h5 : Real.sqrt (S.deg / K) * (‖S.J νR γ‖ * ‖Dmin D.R.k D.R.rS W.z W.z' γ l‖ ^ q) ≤
      Real.sqrt (S.deg / K) * (M * (large₂.sc.b ^ (CDl * (D.R.m : ℝ) ^ 2) * E) ^ q) := by
    calc _ = ‖Dmin D.R.k D.R.rS W.z W.z' γ l‖ ^ q * (Real.sqrt (S.deg / K) * ‖S.J νR γ‖) := by ring
      _ ≤ _ := hit
      _ = _ := by ring
  exact le_of_mul_le_mul_left h5 hc0

section Fam

variable {eps : ℝ} (Fm : FamP eps)

theorem rank_power_le_scale_power (hilbertNinetyConstant : ℝ) (hC : 0 ≤ hilbertNinetyConstant) : ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
    ((Fm.D x i).R.r : ℝ) ^ (hilbertNinetyConstant * ((Fm.D x i).R.m : ℝ)) ≤ (Fm.L x i).sc.b ^ (2 * ((Fm.D x i).R.m : ℝ) ^ 2) := by
  obtain ⟨a, ha1, ha⟩ := ev_rpow (show (0 : ℝ) < 1 / 8 by norm_num) (24 * hilbertNinetyConstant)
  refine ⟨max a 2, fun x hx hx1 i => ?_⟩
  have hxa : a ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have he := eps_pos Fm
  have hl := eps_lt Fm
  have hm := m_ge Fm hx1 i
  have hL : 1 ≤ (Fm.L x i).sc.L := by
    rw [sc_L Fm hx1]
    exact Real.one_le_rpow (by linarith) he.le
  have hk := (Fm.sizes x hx1 i).2.2.1.2
  unfold szTh at hk
  rw [Fm.L_x x i hx1, Fm.L_eps] at hk
  have hk5 : ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ) :=
    hk.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
  have hrk : ((Fm.D x i).R.r : ℝ) ≤ 2 * (Fm.D x i).R.k := by
    have h3 := (Fm.D x i).R.m_add_three_le_k
    have : (Fm.D x i).R.r ≤ 2 * (Fm.D x i).R.k := by unfold Ranks.r; omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ (Fm.D x i).R.r := by
    have h2 := (Fm.D x i).R.two_le_m
    have h3 := (Fm.D x i).R.m_add_three_le_k
    have : 1 ≤ (Fm.D x i).R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hr6 : ((Fm.D x i).R.r : ℝ) ≤ x ^ (6 : ℝ) := by
    calc ((Fm.D x i).R.r : ℝ) ≤ 2 * (Fm.D x i).R.k := hrk
      _ ≤ x * x ^ (5 : ℝ) := mul_le_mul hx2 hk5 (Nat.cast_nonneg _) hx0.le
      _ = x ^ (6 : ℝ) := by
          rw [← Real.rpow_one_add' hx0.le (by norm_num)]; norm_num
  have hlog : Real.log (Fm.D x i).R.r ≤ 48 * x ^ ((1 : ℝ) / 8) := by
    calc Real.log (Fm.D x i).R.r ≤ Real.log (x ^ (6 : ℝ)) := Real.log_le_log (by linarith) hr6
      _ = 6 * Real.log x := Real.log_rpow hx0 _
      _ ≤ 6 * (x ^ ((1 : ℝ) / 8) / (1 / 8)) :=
          mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx0.le (by norm_num)) (by norm_num)
      _ = 48 * x ^ ((1 : ℝ) / 8) := by ring
  have hlog0 : 0 ≤ Real.log (Fm.D x i).R.r := Real.log_nonneg hr1
  have hx8 : 0 ≤ x ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hx0.le _
  have hm2 : hilbertNinetyConstant * Real.log (Fm.D x i).R.r ≤ 2 * (Fm.D x i).R.m := by
    have h4 : x ^ ((1 : ℝ) / 4) = x ^ ((1 : ℝ) / 8) * x ^ ((1 : ℝ) / 8) := by
      rw [← Real.rpow_add hx0]; norm_num
    calc hilbertNinetyConstant * Real.log (Fm.D x i).R.r ≤ hilbertNinetyConstant * (48 * x ^ ((1 : ℝ) / 8)) := mul_le_mul_of_nonneg_left hlog hC
      _ = 2 * ((24 * hilbertNinetyConstant) * x ^ ((1 : ℝ) / 8)) := by ring
      _ ≤ 2 * (x ^ ((1 : ℝ) / 8) * x ^ ((1 : ℝ) / 8)) := by
          have := mul_le_mul_of_nonneg_right (ha x hxa) hx8
          linarith
      _ = 2 * x ^ ((1 : ℝ) / 4) := by rw [h4]
      _ ≤ 2 * (Fm.D x i).R.m := by linarith
  have hm0 : (0 : ℝ) ≤ (Fm.D x i).R.m := Nat.cast_nonneg _
  rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < (Fm.D x i).R.r)]
  unfold Scale.b
  rw [← Real.exp_mul]
  apply Real.exp_le_exp.2
  calc Real.log (Fm.D x i).R.r * (hilbertNinetyConstant * (Fm.D x i).R.m)
      = (hilbertNinetyConstant * Real.log (Fm.D x i).R.r) * (Fm.D x i).R.m := by ring
    _ ≤ (2 * (Fm.D x i).R.m) * (Fm.D x i).R.m := mul_le_mul_of_nonneg_right hm2 hm0
    _ = 1 * (2 * ((Fm.D x i).R.m : ℝ) ^ 2) := by ring
    _ ≤ (Fm.L x i).sc.L * (2 * ((Fm.D x i).R.m : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hL (by positivity)

end Fam

end Formalism.MainNotions.BridgeLemma

end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

section Final

variable {eps : ℝ} (Fm : FamP eps)

end Final

end Formalism.MainNotions.BridgeLemma

end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

section Final

variable {eps : ℝ} (Fm : FamP eps)

end Final

end Formalism.MainNotions.BridgeLemma

end
