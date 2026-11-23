import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InSOfParts
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RegBd

open GlobalTheory.ShFam

theorem abs_coef_le {T : Type} [Fintype T] {N : ℕ} (u : T → Fin N → ℝ) (τ : T) (i : Fin N) :
    |coef u τ i| ≤ 2 * ‖u‖ := by
  have h1 : ∀ j, |u τ j| ≤ ‖u‖ := fun j => by
    have := (norm_le_pi_norm (u τ) j).trans (norm_le_pi_norm u τ)
    simpa [Real.norm_eq_abs] using this
  unfold coef
  split_ifs with hi
  · calc |u τ i - u τ ⟨i + 1, hi⟩| ≤ |u τ i| + |u τ ⟨i + 1, hi⟩| := abs_sub _ _
      _ ≤ 2 * ‖u‖ := by linarith [h1 i, h1 ⟨i + 1, hi⟩]
  · linarith [h1 i, norm_nonneg u]

theorem bdPart_of_low (hL : LowSt) (hC : CentSt) :
    OnObj fun _ _ _ T _ _ => ∀ c, GlobalTheory.RegEst.BdPart (T.F c) := by
  intro D O hO hN A T H h c
  obtain ⟨x, P, hc⟩ := hO
  obtain ⟨C₁, t₀, hC₁, ht₀, hlow⟩ := hL D O x P hc hN ⟨A, T, H, ⟨h⟩⟩
  have hcent := hC D O x P hc hN ⟨A, T, H, ⟨h⟩⟩
  beta_reduce at hcent
  have han := h.an c

  have hB : ∀ (a : Fin ((T.M c).n + 1)) (τ : D.what₂.Tau) (i : Fin O.N), ∃ B : ℝ, 0 ≤ B ∧
      ((i : ℕ) + 1 = O.N → ∀ y, |extBd O.Φ (HeightParts.psi O x c ((h.man c).ε a) τ i) y| ≤ B) := by
    intro a τ i
    by_cases hi : (i : ℕ) + 1 = O.N
    · have hco := AnRead.SmoothOn.continuousOn (hcent c ((h.man c).ε a) τ i hi).1 isOpen_univ
      obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hco
      exact ⟨max B 0, le_max_right _ _, fun _ y => by
        have := hB y (Set.mem_univ _)
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' hi⟩
  choose B hB0 hB using hB
  obtain ⟨Bc, hBc, hBc0⟩ : ∃ Bc : ℝ, (∀ a τ i, B a τ i ≤ Bc) ∧ 0 ≤ Bc := by
    refine ⟨∑ a, ∑ τ, ∑ i, B a τ i, fun a τ i => ?_,
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => hB0 a τ i⟩
    calc B a τ i ≤ ∑ i', B a τ i' := Finset.single_le_sum (fun i' _ => hB0 a τ i') (Finset.mem_univ i)
      _ ≤ ∑ τ', ∑ i', B a τ' i' := Finset.single_le_sum (f := fun τ' => ∑ i', B a τ' i')
          (fun τ' _ => Finset.sum_nonneg fun i' _ => hB0 a τ' i') (Finset.mem_univ τ)
      _ ≤ ∑ a', ∑ τ', ∑ i', B a' τ' i' := Finset.single_le_sum (f := fun a' => ∑ τ', ∑ i', B a' τ' i')
          (fun a' _ => Finset.sum_nonneg fun τ' _ => Finset.sum_nonneg fun i' _ => hB0 a' τ' i') (Finset.mem_univ a)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C₁ + Bc := ⟨_, rfl⟩
  have hC₁K : C₁ ≤ K := by rw [hK]; linarith
  have hBcK : Bc ≤ K := by rw [hK]; linarith
  obtain ⟨nT, hnT, hsum⟩ : ∃ nT : ℝ, 0 ≤ nT ∧ ∀ q : ℝ, ∑ _τ : D.what₂.Tau, ∑ _i : Fin O.N, q = nT * q :=
    ⟨∑ _τ : D.what₂.Tau, ∑ _i : Fin O.N, (1 : ℝ), Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => zero_le_one,
      fun q => by simp only [Finset.sum_mul, one_mul]⟩
  obtain ⟨L₀, hL₀1, hL₀t⟩ : ∃ L₀ : ℝ, 1 ≤ L₀ ∧ -Real.log t₀ ≤ L₀ :=
    ⟨max 1 (-Real.log t₀), le_max_left _ _, le_max_right _ _⟩
  refine ⟨L₀⁻¹, inv_pos.2 (by linarith), nT * K, fun C hC u hu s hs hss l hl a y => ?_⟩

  have hs1 : s ≤ 1 := hss.trans (inv_le_one_of_one_le₀ hL₀1)
  have hs2 : s ^ 2 ≤ L₀⁻¹ := by nlinarith
  have hl' : L₀ ≤ l := by
    rw [hl]
    calc L₀ = (L₀⁻¹)⁻¹ := (inv_inv L₀).symm
      _ ≤ (s ^ 2)⁻¹ := inv_anti₀ (pow_pos hs 2) hs2
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg (by linarith)
  have et : Real.exp (-(s ^ 2)⁻¹) = Real.exp (-l) := by rw [hl]
  have ht : 0 < Real.exp (-l) := Real.exp_pos _
  have htt : Real.exp (-l) ≤ t₀ := by
    calc Real.exp (-l) ≤ Real.exp (Real.log t₀) := Real.exp_le_exp.2 (by linarith)
      _ = t₀ := Real.exp_log ht₀
  have hlog : Real.log (Real.log (1 / Real.exp (-l))) = Real.log l := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hK0 : 0 ≤ K := by rw [hK]; exact add_nonneg hC₁ hBc0
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have hanti : ∀ τ, Antitone (u τ) := fun τ a b hab => hu τ a b hab

  have eS : (T.F c).phS u s a y = (∑ τ, ∑ i, coef u τ i *
      P.regFund c ((h.man c).ε a) τ i (Real.exp (-l)) ((h.man c).pt a y)) / 2 := by
    rw [han.phS u s hs a y, hc.reg_eq, et]
    rfl

  have hterm : ∀ τ (i : Fin O.N),
      -(2 * ‖u‖ * (K * Real.log l + K)) ≤ coef u τ i * P.regFund c ((h.man c).ε a) τ i (Real.exp (-l)) ((h.man c).pt a y) ∧
      coef u τ i * P.regFund c ((h.man c).ε a) τ i (Real.exp (-l)) ((h.man c).pt a y) ≤ 2 * ‖u‖ * K := by
    intro τ i
    have hw := abs_coef_le u τ i
    by_cases hi : (i : ℕ) + 1 < O.N
    · have hw0 : 0 ≤ coef u τ i := coef_nonneg hanti τ hi
      obtain ⟨hlo, hup, -⟩ := hlow _ ht htt c ((h.man c).ε a) τ i hi ((h.man c).pt a y)
      rw [hlog] at hlo
      have hw' : coef u τ i ≤ 2 * ‖u‖ := (le_abs_self _).trans hw
      have hCl : 0 ≤ C₁ * Real.log l := mul_nonneg hC₁ hlogl
      have e1 := mul_le_mul_of_nonneg_left hlo hw0
      have e2 := mul_le_mul_of_nonneg_right hw' hCl
      have e3 := mul_le_mul_of_nonneg_left hup hw0
      have e4 := mul_le_mul_of_nonneg_right hw' hC₁
      have e5 : C₁ * Real.log l ≤ K * Real.log l + K := by
        have := mul_le_mul_of_nonneg_right hC₁K hlogl
        linarith
      have e6 := mul_le_mul_of_nonneg_left e5 (by positivity : (0 : ℝ) ≤ 2 * ‖u‖)
      have e7 := mul_le_mul_of_nonneg_left hC₁K (by positivity : (0 : ℝ) ≤ 2 * ‖u‖)
      constructor <;> nlinarith
    · have hcen : (i : ℕ) + 1 = O.N := by omega
      have eg : P.regFund c ((h.man c).ε a) τ i (Real.exp (-l)) ((h.man c).pt a y) =
          extBd O.Φ (HeightParts.psi O x c ((h.man c).ε a) τ i) ((h.man c).pt a y) := if_neg hi
      have hg : |P.regFund c ((h.man c).ε a) τ i (Real.exp (-l)) ((h.man c).pt a y)| ≤ Bc := by
        rw [eg]
        exact (hB a τ i hcen _).trans (hBc a τ i)
      have hm : |coef u τ i * P.regFund c ((h.man c).ε a) τ i (Real.exp (-l)) ((h.man c).pt a y)| ≤ 2 * ‖u‖ * Bc := by
        rw [abs_mul]
        exact mul_le_mul hw hg (abs_nonneg _) (by positivity)
      have e1 : 2 * ‖u‖ * Bc ≤ 2 * ‖u‖ * (K * Real.log l + K) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : 0 ≤ K * Real.log l := mul_nonneg hK0 hlogl
        linarith
      have e2 : 2 * ‖u‖ * Bc ≤ 2 * ‖u‖ * K :=
        mul_le_mul_of_nonneg_left hBcK (by positivity)
      exact ⟨by linarith [neg_abs_le (coef u τ i * P.regFund c ((h.man c).ε a) τ i (Real.exp (-l)) ((h.man c).pt a y))],
        by linarith [le_abs_self (coef u τ i * P.regFund c ((h.man c).ε a) τ i (Real.exp (-l)) ((h.man c).pt a y))]⟩
  have hlo := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) =>
    Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hterm τ i).1
  have hup := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) =>
    Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hterm τ i).2
  rw [hsum] at hlo hup
  refine ⟨⟨?_, ?_⟩, fun hy => ?_⟩
  · rw [eS]
    have hCC : 0 ≤ (C - nT * K) * ‖u‖ * (Real.log l + 1) :=
      mul_nonneg (mul_nonneg (sub_nonneg.2 hC) hu0) (by linarith)
    calc -(C * ‖u‖ * Real.log l) - C * ‖u‖
        = nT * -(2 * ‖u‖ * (K * Real.log l + K)) / 2 - (C - nT * K) * ‖u‖ * (Real.log l + 1) := by ring
      _ ≤ nT * -(2 * ‖u‖ * (K * Real.log l + K)) / 2 := sub_le_self _ hCC
      _ ≤ _ := le_of_sub_nonneg (by rw [← sub_div]; exact div_nonneg (sub_nonneg.2 hlo) zero_le_two)
  · rw [eS]
    have hCC : 0 ≤ (C - nT * K) * ‖u‖ := mul_nonneg (sub_nonneg.2 hC) hu0
    calc _ ≤ nT * (2 * ‖u‖ * K) / 2 :=
          le_of_sub_nonneg (by rw [← sub_div]; exact div_nonneg (sub_nonneg.2 hup) zero_le_two)
      _ = C * ‖u‖ - (C - nT * K) * ‖u‖ := by ring
      _ ≤ C * ‖u‖ := sub_le_self _ hCC
  ·
    have hz : (h.man c).pt a y ∈ offBd O.Φ c ((h.man c).ε a) := fun hh => hy ((han.Z a y).2 hh)
    rw [eS, han.ph u a y hy]
    have hle : ∑ τ, ∑ i, coef u τ i * phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a y) ≤
        ∑ τ, ∑ i, coef u τ i * P.regFund c ((h.man c).ε a) τ i (Real.exp (-l)) ((h.man c).pt a y) := by
      refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => ?_
      by_cases hi : (i : ℕ) + 1 < O.N
      · exact mul_le_mul_of_nonneg_left ((hlow _ ht htt c ((h.man c).ε a) τ i hi ((h.man c).pt a y)).2.2 hz)
          (coef_nonneg hanti τ hi)
      · have e5 : P.regFund c ((h.man c).ε a) τ i (Real.exp (-l)) ((h.man c).pt a y) =
            phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a y) :=
          (if_neg hi).trans (if_pos hz)
        exact le_of_eq (congrArg (coef u τ i * ·) e5.symm)
    have e4 : O.chg c none u ((h.man c).ε a) ((h.man c).pt a y) = (∑ τ, ∑ i, coef u τ i *
        phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a y)) / 2 := by
      rw [eq_div_iff two_ne_zero, mul_comm]
      exact (hc.two_mul_chg c u ((h.man c).ε a) ((h.man c).pt a y)).trans (phW_eq_sum _ _ _ _ _ _)
    rw [e4]
    linarith [hle]

end GlobalTheory.RegBd

end
