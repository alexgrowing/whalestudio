import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.BinMatNatDegreeLe

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type} {r : ℕ} (w e : Fin r → σ)

theorem mX_zero (J : ℕ) (u v : MvPolynomial σ ℚ_[p]) : mX w e J 0 u v = M.fockK u v := by
  unfold mX; simp

theorem neglog_pow_mul (x0 : ℕ) (c : ℚ_[p]) (hc : c ≠ 0) :
    -Real.logb p ‖(p : ℚ_[p]) ^ x0 * c‖ = (x0 : ℝ) + c.valuation := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [norm_mul, norm_pow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hc,
    Real.logb_mul (pow_ne_zero _ (inv_ne_zero (by linarith))) (zpow_ne_zero _ (by linarith)), Real.logb_pow,
    Real.logb_inv, Real.logb_self_eq_one hp1, neg_add, Formalism.GM.MeanGammaLemmas.neglog_zpow]
  ring

theorem win_abs (hGW : GramWindow2) (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (hr : 1 ≤ r) (o n : ℕ) (T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) (dF : ℚ_[p])
    (n₁ : ℕ) (f : Fin n₁ → MvPolynomial σ ℚ_[p]) (hli : LinearIndependent ℤ_[p] f)
    (hbi : ∀ b, BiHom w e o n (f b)) (x0 : ℕ)
    (hint : ∀ l ≤ min o n, ∀ a b, ‖(p : ℚ_[p]) ^ x0 * (mX w e (min o n) l (T (f a)) (f b) / dF)‖ ≤ 1)
    (horth : ∀ a b, a ≠ b → M.fockK (T (f a)) (f b) / dF = 0) (D1z : ℤ)
    (hsmall : ∀ a, M.fockK (T (f a)) (f a) / dF ≠ 0 ∧ (M.fockK (T (f a)) (f a) / dF).valuation ≤ D1z)
    (Λ : ℝ) (hV : ((min o n : ℕ) : ℝ) / ((p : ℝ) - 1) - padicValNat p (min o n).factorial ≤ Λ)
    (z0 W h : ℕ) (k : ℤ) (hk : 0 ≤ k) (hW : 0 < W) (hWh : W ≤ p ^ h) (hJh : min o n + 1 ≤ p ^ h) :
    (∑ i ∈ Finset.range W, (M.bad p (fun u v => M.fockK (tiePhi w e o n (z0 + i) (T u)) v / dF)
        (Submodule.span ℤ_[p] (Set.range f)) k : ℝ)) ≤
      (W : ℝ) * ((n₁ : ℝ) * (((min o n : ℕ) : ℝ) / W +
        (((x0 : ℝ) + D1z + Λ) + ((min o n : ℕ) : ℝ) * h / W) / ((k : ℝ) + 1))) := by
  set J := min o n with hJ
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set c : Fin n₁ → Fin n₁ → ℕ → ℚ_[p] := fun a b =>
    cW (o + n + r - 1) J (fun l => (p : ℚ_[p]) ^ x0 * (mX w e J l (T (f a)) (f b) / dF)) with hc
  have hlb := lead_bound p n₁ J c (fun a => (p : ℚ_[p]) ^ x0 * (M.fockK (T (f a)) (f a) / dF))
    (fun a b => by
      simp only [hc]
      rw [cW_top, mX_zero]
      split_ifs with hab
      · rw [hab]
      · rw [horth a b hab, mul_zero])
    ((x0 : ℝ) + D1z) Λ
    (fun a => ⟨mul_ne_zero (pow_ne_zero _ hp0) (hsmall a).1, by
      rw [neglog_pow_mul x0 _ (hsmall a).1]
      have : ((M.fockK (T (f a)) (f a) / dF).valuation : ℝ) ≤ (D1z : ℝ) := by exact_mod_cast (hsmall a).2
      linarith⟩) hV
  refine hGW p σ n₁ J h W k ((x0 : ℝ) + D1z + Λ) z0
    (fun i u v => M.fockK (tiePhi w e o n (z0 + i) (T u)) v / dF) f
    (fun i => (p : ℚ_[p]) ^ x0 * ((o + n + r + (z0 + i) - 1).choose J : ℚ_[p])) c hli
    (fun i a u v => by
      show M.fockK (tiePhi w e o n (z0 + i) (T (a • u))) v / dF = _
      rw [map_smul, map_smul, ProjS.fockK_smul_left, mul_div_assoc])
    (fun i u u' v => by
      show M.fockK (tiePhi w e o n (z0 + i) (T (u + u'))) v / dF = _
      rw [map_add, map_add, ProjS.fockK_add_left, add_div])
    (fun i a u v => by
      show M.fockK (tiePhi w e o n (z0 + i) (T u)) (a • v) / dF = _
      rw [ProjS.fockK_smul_right, mul_div_assoc])
    (fun i u v v' => by
      show M.fockK (tiePhi w e o n (z0 + i) (T u)) (v + v') / dF = _
      rw [ProjS.fockK_add_right, add_div])
    hW hWh hJh hk (fun a b i => cW_norm _ _ _ (fun l hl => hint l hl a b) i) hlb.1 hlb.2 ?_
  intro i _
  have hJM : J ≤ o + n + r + (z0 + i) - 1 := by omega
  refine ⟨mul_ne_zero (pow_ne_zero _ hp0) (by exact_mod_cast (Nat.choose_pos hJM).ne'), ?_, fun a b => ?_⟩
  · rw [norm_mul, norm_pow, Padic.norm_p]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    have h1 : ‖(((o + n + r + (z0 + i) - 1).choose J : ℕ) : ℚ_[p])‖ ≤ 1 := by
      rw [← PadicInt.coe_natCast, ← PadicInt.norm_def]; exact PadicInt.norm_le_one _
    have h2 : ((p : ℝ)⁻¹) ^ x0 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1.le)
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [Matrix.map_apply, Formalism.GM.MeanGammaLemmas.binMatK_eval_nat]
    simp only [hc]
    rw [cW_sum (o + n + r - 1) J (z0 + i) (by omega)]
    have hpp := phi_pair w e hw he hwe hr o n (z0 + i) (T (f a)) (f b) (hbi b)
    rw [← hJ] at hpp
    calc (p : ℚ_[p]) ^ x0 * ((o + n + r + (z0 + i) - 1).choose J : ℚ_[p]) *
          (M.fockK (tiePhi w e o n (z0 + i) (T (f a))) (f b) / dF)
        = (p : ℚ_[p]) ^ x0 * ((((o + n + r + (z0 + i) - 1).choose J : ℚ_[p]) *
          M.fockK (tiePhi w e o n (z0 + i) (T (f a))) (f b)) / dF) := by ring
      _ = _ := by
        rw [hpp, Finset.sum_div, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l hl => ?_
        have hl' : l ≤ J := by simp only [mem_range] at hl; omega
        rw [show o + n + r - 1 + (z0 + i) - l = o + n + r + (z0 + i) - 1 - l by omega]
        ring

end Formalism.MainNotions.G.GramWindowAlt

end
