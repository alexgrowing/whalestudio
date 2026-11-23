import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormLeOpNormBlockDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.GoodMetric

theorem pow_le_logTwo_mul_pow {L : ℝ} {N N' k : ℕ} (hN' : N = 0 → N' = 0) (hL : N = 0 ∨ Real.log 2 ≤ L)
    (hk : k ≤ N') : L ^ k ≤ (Real.log 2)⁻¹ ^ N' * L ^ N' := by
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hD : 1 ≤ (Real.log 2)⁻¹ ^ N' := one_le_pow₀ (one_le_inv₀ h2 |>.2 h2'.le)
  rcases hL with hN | hL
  · have : N' = 0 := hN' hN
    subst this
    have : k = 0 := by omega
    subst this
    simp
  · have hL0 : 0 < L := h2.trans_le hL
    rcases le_or_gt 1 L with h1 | h1
    · calc L ^ k ≤ L ^ N' := pow_le_pow_right₀ h1 hk
        _ = 1 * L ^ N' := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hD (by positivity)
    · calc L ^ k ≤ 1 := pow_le_one₀ hL0.le h1.le
        _ ≤ (L * (Real.log 2)⁻¹) ^ N' := one_le_pow₀ (by rw [← div_eq_mul_inv, one_le_div h2]; exact hL)
        _ = _ := by rw [mul_pow, mul_comm]

theorem sum_abs_log_eq_zero_or_ge {n : ℕ} (S : Finset (Fin n)) (v : ReciprocityTheory.L2DbarEstimates.V n)
    (hS : ∀ a ∈ S, ‖v a‖ < 1 / 2) :
    ∑ a ∈ S, |Real.log ‖v a‖| = 0 ∨ Real.log 2 ≤ ∑ a ∈ S, |Real.log ‖v a‖| := by
  by_cases h : ∀ a ∈ S, |Real.log ‖v a‖| = 0
  · exact Or.inl (Finset.sum_eq_zero h)
  · push_neg at h
    obtain ⟨a, ha, hne⟩ := h
    right
    have hv : ‖v a‖ ≠ 0 := fun h0 => hne (by rw [h0]; simp)
    have hpos : 0 < ‖v a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    have hlt : Real.log ‖v a‖ < Real.log (1 / 2) := Real.log_lt_log hpos (hS a ha)
    have hl : Real.log 2 ≤ |Real.log ‖v a‖| := by
      rw [one_div, Real.log_inv] at hlt
      rw [abs_of_neg (by linarith [Real.log_pos one_lt_two])]
      linarith
    exact hl.trans (Finset.single_le_sum (f := fun a => |Real.log ‖v a‖|) (fun _ _ => abs_nonneg _) ha)

end GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric

theorem goodBound_of_blockDiagonal' : ∀ (n : ℕ) (S : Finset (Fin n)) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (G : ∀ τ : ι, ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin (m τ)) ℂ) (c : ℝ) (N : ℕ), ∃ (c' : ℝ) (N' : ℕ), ∀ v : ReciprocityTheory.L2DbarEstimates.V n, (∀ a ∈ S, ‖v a‖ < 1 / 2) → (Matrix.blockDiagonal' fun τ => G τ v).det ≠ 0 → (∀ p q, ContDiffAt ℝ 2 (fun u => (Matrix.blockDiagonal' fun τ => G τ u) p q) v) → GlobalTheory.GoodMetric.GoodBound S c N (fun u => Matrix.blockDiagonal' fun τ => G τ u) v → ∀ τ, GlobalTheory.GoodMetric.GoodBound S c' N' (G τ) v := by
  intro n S ι _ _ m G c N
  set K := ∑ τ, m τ
  set N' := N * (K + 1)
  set F : ℝ := ∏ τ, ((m τ).factorial : ℝ)
  set D : ℝ := (Real.log 2)⁻¹ ^ N'
  refine ⟨F * (max 1 c) ^ (K + 1) * D, N', ?_⟩
  intro v hS hdet hC hG τ
  set L := ∑ a ∈ S, |Real.log ‖v a‖| with hLdef
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hdp : 0 < ‖(Matrix.blockDiagonal' fun τ => G τ v).det‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hdet)
  have hcY : 0 < c * L ^ N := hdp.trans_le hG.det
  have hY : 0 < L ^ N := by
    rcases (pow_nonneg hL0 N).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hcY; exact absurd hcY (lt_irrefl 0)
  have hc : 0 < c := pos_of_mul_pos_left hcY hY.le
  have hLN : N = 0 ∨ Real.log 2 ≤ L := by
    rcases sum_abs_log_eq_zero_or_ge S v hS with h | h
    · left
      by_contra hN
      rw [← hLdef] at h
      rw [h, zero_pow hN] at hY
      exact lt_irrefl 0 hY
    · exact Or.inr h
  have hN' : N = 0 → N' = 0 := fun h => by simp [N', h]
  have key : ∀ k ≤ N', L ^ k ≤ D * L ^ N' := fun k hk => pow_le_logTwo_mul_pow hN' hLN hk
  have hF : 1 ≤ F := by
    have : F = ((∏ τ, (m τ).factorial : ℕ) : ℝ) := by simp [F]
    rw [this]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _)
  have hD : 1 ≤ D := one_le_pow₀ ((one_le_inv₀ (Real.log_pos one_lt_two)).2
    (by have := Real.log_two_lt_d9; linarith))
  have hM1 : 1 ≤ max 1 c := le_max_left _ _
  have hcF : c ≤ F * (max 1 c) ^ (K + 1) :=
    calc c ≤ max 1 c := le_max_right _ _
      _ ≤ (max 1 c) ^ (K + 1) := le_self_pow₀ hM1 (by omega)
      _ = 1 * (max 1 c) ^ (K + 1) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hF (by positivity)
  have hcc' : c ≤ F * (max 1 c) ^ (K + 1) * D :=
    hcF.trans (le_mul_of_one_le_right (by positivity) hD)

  have hent : ∀ τ' (i j : Fin (m τ')), ‖G τ' v i j‖ ≤ c * L ^ N := fun τ' i j => by
    have := hG.entry ⟨τ', i⟩ ⟨τ', j⟩
    simpa [Matrix.blockDiagonal'_apply_eq] using this
  have hprod : (Matrix.blockDiagonal' fun τ => G τ v).det = ∏ τ', (G τ' v).det :=
    GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod _
  have hunit : ∀ τ', IsUnit (G τ' v).det := fun τ' => by
    rw [hprod] at hdet
    exact (Finset.prod_ne_zero_iff.1 hdet τ' (Finset.mem_univ _)).isUnit
  have hCτ : ∀ τ', GlobalTheory.HermFrame.MContDiffAt 2 (G τ') v := fun τ' i j => by
    have := hC ⟨τ', i⟩ ⟨τ', j⟩
    simpa [Matrix.blockDiagonal'_apply_eq] using this
  have hconn : ∀ ξ, GlobalTheory.HermFrame.conn (fun u => Matrix.blockDiagonal' fun τ => G τ u) v ξ =
      Matrix.blockDiagonal' fun τ => GlobalTheory.HermFrame.conn (G τ) v ξ := fun ξ =>
    GlobalTheory.HermFrame.conn_blockDiagonal' hunit ξ
  have hcurv : ∀ ξ η, GlobalTheory.HermFrame.curv (fun u => Matrix.blockDiagonal' fun τ => G τ u) v ξ η =
      Matrix.blockDiagonal' fun τ => GlobalTheory.HermFrame.curv (G τ) v ξ η := fun ξ η =>
    GlobalTheory.HermFrame.curv_blockDiagonal' hCτ hunit ξ η
  have hdel : ∀ ξ η, GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.conn
      (fun u => Matrix.blockDiagonal' fun τ => G τ u) u ξ) v η =
      Matrix.blockDiagonal' fun τ => GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.conn (G τ) u ξ) v η := by
    intro ξ η
    have he : (fun u => GlobalTheory.HermFrame.conn (fun u => Matrix.blockDiagonal' fun τ => G τ u) u ξ) =ᶠ[𝓝 v]
        fun u => Matrix.blockDiagonal' fun τ => GlobalTheory.HermFrame.conn (G τ) u ξ :=
      (Filter.eventually_all.2 fun i => (hCτ i).eventually_isUnit (hunit i)).mono
        fun x hx => GlobalTheory.HermFrame.conn_blockDiagonal' hx ξ
    rw [GlobalTheory.HermFrame.mdel_congr he, GlobalTheory.HermFrame.mdel_blockDiagonal']

  set e := c * L ^ N
  set M := max 1 e
  have hM : 1 ≤ M := le_max_left _ _
  have hdetle : ∀ τ', ‖(G τ' v).det‖ ≤ ((m τ').factorial : ℝ) * M ^ m τ' := fun τ' => by
    have := Matrix.det_le (abv := NormedField.toAbsoluteValue ℂ) (A := G τ' v) (x := M)
      fun i j => (hent τ' i j).trans (le_max_right _ _)
    calc ‖(G τ' v).det‖ = (NormedField.toAbsoluteValue ℂ) (G τ' v).det := rfl
      _ ≤ _ := this
      _ = _ := by simp [Fintype.card_fin, nsmul_eq_mul]
  set P := ∏ τ' ∈ Finset.univ.erase τ, ‖(G τ' v).det‖
  have hnorm : ‖(Matrix.blockDiagonal' fun τ => G τ v).det‖ = ‖(G τ v).det‖ * P := by
    rw [hprod, norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  have hP0 : 0 < P := Finset.prod_pos fun τ' _ => norm_pos_iff.2 (hunit τ').ne_zero
  have hinv : ‖(G τ v).det‖⁻¹ = ‖(Matrix.blockDiagonal' fun τ => G τ v).det‖⁻¹ * P := by
    rw [hnorm, mul_inv, mul_assoc, inv_mul_cancel₀ hP0.ne', mul_one]
  have hPle : P ≤ F * M ^ K := by
    have h1 : P ≤ ∏ τ' ∈ Finset.univ.erase τ, ((m τ').factorial : ℝ) * M ^ m τ' :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ' _ => hdetle τ'
    have h2 : ∏ τ' ∈ Finset.univ.erase τ, ((m τ').factorial : ℝ) * M ^ m τ' ≤
        ∏ τ', ((m τ').factorial : ℝ) * M ^ m τ' := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
      refine le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => by positivity) ?_
      exact one_le_mul_of_one_le_of_one_le
        (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)) (one_le_pow₀ hM)
    have h3 : ∏ τ', ((m τ').factorial : ℝ) * M ^ m τ' = F * M ^ K := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    linarith
  have hMle : M ≤ max 1 c * max 1 (L ^ N) :=
    max_le (one_le_mul_of_one_le_of_one_le hM1 (le_max_left _ _))
      (mul_le_mul (le_max_right _ _) (le_max_right _ _) hY.le (by positivity))
  have hMY : (max 1 (L ^ N)) ^ (K + 1) ≤ D * L ^ N' := by
    rcases le_total 1 (L ^ N) with h | h
    · rw [max_eq_right h, ← pow_mul]; exact key _ le_rfl
    · rw [max_eq_left h, one_pow]; simpa using key 0 (Nat.zero_le _)
  refine ⟨fun i j => ?_, ?_, fun a i j => ?_, fun a b i j => ?_, fun a b i j => ?_⟩
  · calc ‖G τ v i j‖ ≤ c * L ^ N := hent τ i j
      _ ≤ c * (D * L ^ N') := mul_le_mul_of_nonneg_left (key N (by simp [N']; exact Nat.le_mul_of_pos_right _ (by omega))) hc.le
      _ = c * D * L ^ N' := by ring
      _ ≤ F * (max 1 c) ^ (K + 1) * D * L ^ N' :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcF (by positivity)) (by positivity)
  · rw [hinv]
    calc ‖(Matrix.blockDiagonal' fun τ => G τ v).det‖⁻¹ * P ≤ e * (F * M ^ K) :=
          mul_le_mul hG.det hPle hP0.le hcY.le
      _ ≤ M * (F * M ^ K) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = F * M ^ (K + 1) := by ring
      _ ≤ F * (max 1 c * max 1 (L ^ N)) ^ (K + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hMle _) (by positivity)
      _ = F * (max 1 c) ^ (K + 1) * (max 1 (L ^ N)) ^ (K + 1) := by ring
      _ ≤ F * (max 1 c) ^ (K + 1) * (D * L ^ N') := mul_le_mul_of_nonneg_left hMY (by positivity)
      _ = _ := by ring
  · have := hG.form a ⟨τ, i⟩ ⟨τ, j⟩
    rw [hconn, Matrix.blockDiagonal'_apply_eq] at this
    exact this.trans hcc'
  · have := hG.dbar a b ⟨τ, i⟩ ⟨τ, j⟩
    rw [hcurv, Matrix.blockDiagonal'_apply_eq] at this
    exact this.trans hcc'
  · have := hG.del a b ⟨τ, i⟩ ⟨τ, j⟩
    rw [hdel, hdel, Matrix.sub_apply, Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_eq,
      ← Matrix.sub_apply] at this
    exact this.trans hcc'

end GlobalTheory.GoodMetric
