import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDivSqrtLeFourExp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BadRowsShareBoundTwoPrimesStatement
import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.DataParams

noncomputable section

open Polynomial Classical GlobalTheory.BadShare Formalism.BasicNotions Formalism.MainNotions

namespace UpperTheory.Win

theorem two_mul_div_le_exp {x z c P Q : ℝ} (hx : Real.exp 209 ≤ x) (hz : 0 < z) (hP1 : P ≤ x ^ (c + 1))
    (hP2 : P ≤ x ^ (10 : ℝ)) (hQ1 : x ^ (c + 5) < Q) (hQ2 : x ^ (z / 5 - z / 100) ≤ Real.log Q) :
    2 * P / Q ≤ Real.exp (-(x ^ (z / 7))) := by
  have hx2 : 2 ≤ x := by have := Real.add_one_le_exp (209 : ℝ); linarith
  have hx0 : 0 < x := by linarith
  have hQ0 : 0 < Q := (Real.rpow_pos_of_pos hx0 _).trans hQ1
  have hl : 209 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
  have e2 : (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
  have ep : ∀ a : ℝ, x ^ a = Real.exp (Real.log x * a) := fun a => Real.rpow_def_of_pos hx0 a
  rw [div_le_iff₀ hQ0]
  rcases le_total (x ^ (z / 7)) (3 * Real.log x) with h | h
  · calc 2 * P ≤ Real.exp (Real.log 2) * Real.exp (Real.log x * (c + 1)) := by
          rw [← e2, ← ep]; linarith
      _ ≤ Real.exp (-(x ^ (z / 7))) * Real.exp (Real.log x * (c + 5)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          exact Real.exp_le_exp.2 (by nlinarith)
      _ ≤ _ := by
          rw [← ep]
          exact mul_le_mul_of_nonneg_left hQ1.le (Real.exp_pos _).le
  · set v := x ^ (z / 7) with hv
    have hv1 : 625 ≤ v := by linarith
    have h5 : (5 : ℝ) ≤ v ^ (1 / 4 : ℝ) := by
      have e : (5 : ℝ) = (625 : ℝ) ^ (1 / 4 : ℝ) := by
        rw [show (625 : ℝ) = 5 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [e]
      exact Real.rpow_le_rpow (by norm_num) hv1 (by norm_num)
    have h6 : v * v ^ (1 / 4 : ℝ) ≤ x ^ (z / 5 - z / 100) := by
      rw [hv, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h7 : 5 * v ≤ Real.log Q := by nlinarith
    calc 2 * P ≤ Real.exp (Real.log 2) * Real.exp (Real.log x * 10) := by
          rw [← e2, ← ep]; linarith
      _ ≤ Real.exp (-v) * Real.exp (Real.log Q) := by
          rw [← Real.exp_add, ← Real.exp_add]
          exact Real.exp_le_exp.2 (by linarith)
      _ = _ := by rw [Real.exp_log hQ0]

theorem fm_div_min_le {D : D7} (L : SizeData₂ D) (hP : ParameterChoice' D L) (h : SizesAt L) (hx : Real.exp 209 ≤ L.sc.x) :
    2 * ((D.R.f : ℝ) * D.R.m) / ((min D.host.q D.host.d : ℕ) : ℝ) ≤ Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) := by
  obtain ⟨-, -, hK, -, hT, -, hQ, -⟩ := h
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.rank_add_five_le
  have h3 : D.R.f ≤ D.R.k := D.R.f_le_k
  have sq : ∀ (y : ℕ) (a b : ℝ), D.R.k ≤ y → (y : ℝ) ≤ L.sc.x ^ a → a + a ≤ b → (D.R.f : ℝ) * D.R.m ≤ L.sc.x ^ b := by
    intro y a b hy ha hb
    have a1 : (D.R.f : ℝ) ≤ y := by exact_mod_cast h3.trans hy
    have a2 : (D.R.m : ℝ) ≤ y := by exact_mod_cast (by omega : D.R.m ≤ y)
    calc (D.R.f : ℝ) * D.R.m ≤ L.sc.x ^ a * L.sc.x ^ a :=
          mul_le_mul (a1.trans ha) (a2.trans ha) (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hx0 _).le
      _ = L.sc.x ^ (a + a) := (Real.rpow_add hx0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1.le hb
  refine two_mul_div_le_exp (c := 2 * L.Ct) hx L.sc.ez_pos
    (sq D.R.t _ _ (by omega) hT.2 (by unfold szTh; linarith))
    (sq D.R.k _ _ le_rfl hK.2 (by unfold szTh; linarith)) ?_ ?_
  · rw [Nat.cast_min]
    exact lt_min hP.qd_pow.1 hP.qd_pow.2
  · rcases min_choice D.host.q D.host.d with e | e <;> rw [e]
    · exact hQ.2.1
    · exact hQ.2.2.2.1

theorem badShare_win (eps C : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ z : ℝ, z ≤ eps →
    ∀ (g₁ g₂ : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (N m q d f : ℕ) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂],
    Fintype.card ι₁ = f → Fintype.card ι₂ = f → PrimeOK g₁ q d → PrimeOK g₂ q d →
    Real.exp (8 * x ^ eps) ≤ g₁ → Real.exp (8 * x ^ eps) ≤ g₂ → x ^ (2 : ℝ) ≤ f → (f : ℝ) ≤ x ^ C → (m : ℝ) ≤ x ^ C →
    x ^ eps ≤ N → (N : ℝ) ≤ x ^ C → 2 * ((f : ℝ) * m) / ((min q d : ℕ) : ℝ) ≤ Real.exp (-(x ^ (z / 7))) →
    ∀ (L₁ : ι₁ → Lev g₁ N) (L₂ : ι₂ → Lev g₂ N) (τ₁ : ι₁ → (ZMod g₁)[X] → GG g₁ N → ℂ) (τ₂ : ι₂ → (ZMod g₂)[X] → GG g₂ N → ℂ),
    (∀ v, IsSeries (τ₁ v)) → (∀ v, IsSeries (τ₂ v)) →
    ∀ (ch₁ : ι₁ → Fin m → (ZMod g₁)ˣ) (ch₂ : ι₂ → Fin m → (ZMod g₂)ˣ)
      (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
      (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M), CountAt ρ 0 →
    ∃ del : ℝ, 0 ≤ del ∧ del ≤ Real.exp (-(x ^ (z / 7))) ∧
      (1 - del) * (rk ρ (tens2 (tens fun v => (L₁ v).e) (tens fun v => (L₂ v).e)) : ℝ) ≤
        (rk ρ (conv (tens2 (eGood τ₁ ch₁) (eGood τ₂ ch₂)) (tens2 (tens fun v => (L₁ v).e) (tens fun v => (L₂ v).e))) : ℝ) := by
  obtain ⟨x₀, hx₀⟩ := badBound_numbers eps C heps heps1
  refine ⟨max x₀ 1, ?_⟩
  intro x hx z hz g₁ g₂ _ _ N m q d f ι₁ ι₂ _ _ h1 h2 hp1 hp2 hg1 hg2 hf hf' hm hN hN' hq
    L₁ L₂ τ₁ τ₂ ht1 ht2 ch₁ ch₂ M _ _ _ ρ hC
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hf0 : (0 : ℝ) ≤ (f : ℝ) := Nat.cast_nonneg f
  have hE : Real.exp (-(x ^ (eps / 7))) ≤ Real.exp (-(x ^ (z / 7))) :=
    Real.exp_le_exp.2 (neg_le_neg (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)))
  have hE0 := Real.exp_pos (-(x ^ (z / 7)))
  have one : ∀ g : ℝ, Real.exp (8 * x ^ eps) ≤ g →
      max 0 (badBound g f m N ((min q d : ℕ) : ℝ)) ≤ Real.exp (-(x ^ (z / 7))) / 2 := by
    intro g hg
    obtain ⟨-, -, hb⟩ := hx₀ x ((le_max_left _ _).trans hx) g f m N _ hg hf hf' hm0 hm hN hN' le_rfl
    refine max_le (by linarith) ?_
    have e : badBound g f m N ((min q d : ℕ) : ℝ) = badBound g f m N (Real.exp (x ^ (eps / 6))) +
        2 * ((f : ℝ) * m) / ((min q d : ℕ) : ℝ) / 4 - 2 * f * m * (1 / (4 * Real.exp (x ^ (eps / 6)))) := by
      unfold badBound; ring
    have : 0 ≤ 2 * (f : ℝ) * m * (1 / (4 * Real.exp (x ^ (eps / 6)))) := by positivity
    rw [e]; linarith
  obtain ⟨hN5, -, -⟩ := hx₀ x ((le_max_left _ _).trans hx) g₁ f m N _ hg1 hf hf' hm0 hm hN hN' le_rfl
  have hN5' : 100000 ≤ N := by exact_mod_cast hN5
  have key := GlobalTheory.T.badRows_share_bound_two_primes g₁ g₂ N m q d ι₁ ι₂ hN5' hp1 hp2 L₁ L₂ τ₁ τ₂ ht1 ht2 ch₁ ch₂ M ρ 0 le_rfl (by norm_num) hC
  rw [h1, h2] at key
  refine ⟨_, ?_, ?_, key⟩
  · have := le_max_left 0 (badBound g₁ f m N ((min q d : ℕ) : ℝ))
    have := le_max_left 0 (badBound g₂ f m N ((min q d : ℕ) : ℝ))
    norm_num only
    linarith
  · have := one g₁ hg1
    have := one g₂ hg2
    norm_num only
    linarith

end UpperTheory.Win

end
