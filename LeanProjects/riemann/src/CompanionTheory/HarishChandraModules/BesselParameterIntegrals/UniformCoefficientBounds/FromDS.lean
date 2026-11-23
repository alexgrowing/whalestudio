import Mathlib
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundOfCompact
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.CoefGen

open Matrix MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.Upq.Coef

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.CutBP.Jmu Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG ReciprocityTheory.ChartRestriction.DS

theorem thrStar_le {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) : thrStar ε ≤ 32 * (n : ℝ) ^ 3 := by
  have hp : pOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hq : qOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have h0 : S7.q0 ε ≤ n := by unfold S7.q0; omega
  have hp' : (pOf ε : ℝ) ≤ n := by exact_mod_cast hp
  have hq' : (qOf ε : ℝ) ≤ n := by exact_mod_cast hq
  have h0' : (S7.q0 ε : ℝ) ≤ n := by exact_mod_cast h0
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) ≤ n ^ 3 := le_self_pow₀ h1 (by norm_num)
  have h3 : (n : ℝ) ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
  refine max_le ?_ ?_
  · have : (n : ℝ) * pOf ε * qOf ε ≤ n * n * n := by gcongr
    nlinarith
  · have h4 : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * n :=
      Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
    have h5 : 16 * (n : ℝ) * S7.q0 ε ≤ 16 * n * n := by gcongr
    nlinarith

theorem dsigW_SK {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) : ∀ (W : List (Mx k r)) (v : H),
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v = PI.UpqRep.dsigW (k := k) (r := r) σ W v
  | [], _ => rfl
  | X :: W, v => by
    change Formalism.MainNotions.S.dsig σ X (Formalism.MainNotions.S.dsigW σ W v) = PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ W v)
    rw [dsigW_SK σ W v]; rfl

theorem decay_infinite_range : DecInf := by
  intro k r ε lam h H _ _ _ σ hlam hσ hgap hok v0 hv0
  have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast by omega)
  have hh := hok.2.1
  have ht := thrStar_le (n := 2 * r + k + 1) (by omega) ε
  have hs : (1 : ℝ) ≤ Real.sqrt (2 * ((r : ℝ) + 1)) :=
    Real.one_le_sqrt.2 (by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith)
  have ha0 : 0 ≤ aOf r h := div_nonneg (by linarith) (by positivity)
  have ha : aOf r h ≤ h / 8 := div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  have hm : thrStar ε + (⌊aOf r h⌋₊ : ℕ) < h := by
    have := Nat.floor_le ha0
    linarith
  obtain ⟨C, Ws, hWs, hC⟩ := DecInf.decSm hlam hgap _ hm (σ := σ) hσ
  have hv0s := CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam H σ hlam hσ v0 hv0
  set N := (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v0‖).sum
  refine ⟨|C * N|, Ws, fun W hW => (hWs W hW).2, fun w hw x hx => ?_⟩
  have h1 := hC w hw v0 hv0s x hx
  simp only [dsigW_SK] at h1
  set M := (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W w‖).sum
  have hM : 0 ≤ M := List.sum_nonneg fun t ht => by
    obtain ⟨W, -, rfl⟩ := List.mem_map.1 ht
    exact norm_nonneg _
  have hg1 : 1 ≤ B.gN x := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hx
  have h2 : B.gN x ^ (aOf r h - 1) ≤ B.gN x ^ (⌊aOf r h⌋₊ : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hg1 (Nat.sub_one_lt_floor _).le
  have h3 : B.gN x ^ (aOf r h - 1) * ‖⟪v0, σ x w⟫_ℂ‖ ≤ |C * N| * M := by
    refine (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans (h1.trans ?_)
    have e : N = (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v0‖).sum := by
      simp only [N, dsigW_SK]
    rw [← e, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hM
  rw [← neg_sub, Real.rpow_neg (by linarith), ← div_eq_mul_inv,
    le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) _), mul_comm]
  exact h3

theorem capelli_coefficient_continuity : CoefCC := by
  intro hK k r Wp Wq _ _ _ _ _ _ Bs ε lam h u u' νq νq' A hG
  have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast by omega)
  have hh := hG.1.2.2.2.1.2.1
  have ht := thrStar_le (n := 2 * r + k + 1) (by omega) ε
  have hm : thrStar ε + (64 * (2 * r + k + 1) ^ 3 : ℕ) < h := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    linarith
  obtain ⟨C, Ws, -, hC⟩ := DecInf.decSm hG.1.1 hG.1.2.2.1 _ hm (σ := A.σ) hG.1.2.1
  rw [coef_eq_cf]
  exact inCC_cf_of_dec hK hG.1.1 hG.1.2.1 (lowest_unit_vector_is_K_finite hG) _ (fun a ha b hb => ⟨_, fun g hg =>
    (congrArg (· * _) (Real.rpow_natCast _ _)).trans_le (hC b hb a ha g hg)⟩) 5

end CompanionTheory.D.Upq.Coef

end
