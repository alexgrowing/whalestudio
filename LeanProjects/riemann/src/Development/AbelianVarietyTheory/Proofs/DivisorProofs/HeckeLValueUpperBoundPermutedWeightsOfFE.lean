import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeLFunctionLeZetaThreeHalvesPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCompletedHeckeLCMOneLePhragmenLindelofStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmValueCharacterConductorExponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSizesLogBoundStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.SqTop GlobalTheory.FunObj GlobalTheory.FunObj.SqNum Formalism.BasicNotions GlobalTheory.ChiGrid Formalism.IndefR.Links

namespace GlobalTheory.SqTop

theorem lBound_of : GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → FieldDat → LBound := by
  intro hFE hS hFD
  set c : ℝ := max 0 (Real.log ‖riemannZeta (3 / 2)‖) with hc
  obtain ⟨CF1, hB⟩ := GlobalTheory.T.gridSizes_log_bound c
  obtain ⟨CF2, hF⟩ := hFD
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, hB⟩ := hB ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, hF⟩ := hF ε CF (le_of_max_le_right hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ hL G => ?_⟩
  have hb := hB C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hL G
  obtain ⟨hCM, hAb, hFd, hBase, -⟩ := hF C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hL G
  intro i j s hs1 hs2 π χ Λ hχ hΛ
  set κ := kap D (⟨1, CF, large₂.sc.b⟩ : Consts).cGap i j s with hκ
  set n : ℕ := Module.finrank ℚ D.host.E with hn
  have key : c * (n : ℝ) + Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) +
      ∑ τ, Real.log (1 + ((κ τ : ℝ) + s)) ≤ bTH D C large₂.sc.x large₂.sc.b := hb i j s hs1 hs2
  have hc0 : 0 ≤ c := le_max_left _ _
  have hcz : Real.log ‖riemannZeta (3 / 2)‖ ≤ c := le_max_right _ _
  have hd0 : 0 ≤ Real.log |((discr D.host.E : ℤ) : ℝ)| := Real.log_nonneg (by
    have := Int.one_le_abs (NumberField.discr_ne_zero D.host.E); exact_mod_cast this)
  have hq0 : 0 ≤ Real.log (levQ G.pl : ℝ) := Real.log_natCast_nonneg _
  have hk0 : 0 ≤ ∑ τ, Real.log (1 + ((κ τ : ℝ) + s)) :=
    Finset.sum_nonneg fun τ _ => Real.log_nonneg (by have : (0:ℝ) ≤ κ τ := Nat.cast_nonneg _; have : (0:ℝ) ≤ s := Nat.cast_nonneg _; linarith)
  have hn0 : (0 : ℝ) ≤ c * n := mul_nonneg hc0 (Nat.cast_nonneg _)
  by_cases h0 : Λ s = 0
  · rw [h0, norm_zero, Real.log_zero]
    linarith
  have hpos : 0 < ‖Λ s‖ := norm_pos_iff.2 h0
  have hz : 0 < ‖riemannZeta (3 / 2)‖ := norm_pos_iff.2 (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  rcases (by omega : s = 1 ∨ 2 ≤ s) with rfl | h2
  · obtain ⟨a, ha, haN⟩ := GlobalTheory.T.exists_cmValueCharacter_conductorExponents D G 1 _ χ hχ
    have hA := GlobalTheory.T.norm_completedHeckeL_CM_one_le_phragmenLindelof D.host.E D.what₂.Tau (cmPhi D) hFE hS hFd.2.2.2.2.2.2.1 χ (fun τ => ((κ (π τ) : ℕ) : ℤ) + ((1 : ℕ) : ℤ)) a Λ
      hχ.1 hχ.2.1 hχ.2.2.1 (fun τ => by positivity) ha hΛ
    simp only [Nat.cast_one] at hpos h0 ⊢
    set N : ℕ := (discr D.host.E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k with hN
    set P : ℝ := ∏ τ, (1 + ((((κ (π τ) : ℕ) : ℤ) + ((1 : ℕ) : ℤ) : ℤ) : ℝ)) with hP
    have hP0 : 0 < P := Finset.prod_pos fun τ _ => by push_cast; positivity
    have hN0 : (0 : ℝ) < N := by
      by_contra hc'
      have : (N : ℝ) = 0 := le_antisymm (not_lt.1 hc') (Nat.cast_nonneg _)
      rw [this, mul_zero, zero_mul] at hA
      linarith
    have hNle : (N : ℝ) ≤ |((discr D.host.E : ℤ) : ℝ)| * (levQ G.pl : ℝ) ^ 2 := by
      rw [hN, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact_mod_cast haN
    have hQ0 : (0 : ℝ) < levQ G.pl := by
      by_contra hc'
      have : (levQ G.pl : ℝ) = 0 := le_antisymm (not_lt.1 hc') (Nat.cast_nonneg _)
      rw [this, zero_pow two_ne_zero, mul_zero] at hNle; linarith
    have hD0 : (0 : ℝ) < |((discr D.host.E : ℤ) : ℝ)| := by
      have := Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
      have : (1 : ℝ) ≤ |((discr D.host.E : ℤ) : ℝ)| := by exact_mod_cast this
      linarith
    have h1 : Real.log ‖Λ 1‖ ≤ Real.log (‖riemannZeta (3 / 2)‖ ^ n) + Real.log N + Real.log P := by
      rw [← Real.log_mul (by positivity) hN0.ne', ← Real.log_mul (by positivity) hP0.ne']
      exact Real.log_le_log hpos hA
    have h2 : Real.log N ≤ Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) := by
      calc Real.log N ≤ Real.log (|((discr D.host.E : ℤ) : ℝ)| * (levQ G.pl : ℝ) ^ 2) := Real.log_le_log hN0 hNle
        _ = _ := by rw [Real.log_mul hD0.ne' (by positivity), Real.log_pow]; push_cast; ring
    have h3 : Real.log P = ∑ τ, Real.log (1 + ((κ τ : ℝ) + ((1 : ℕ) : ℝ))) := by
      rw [hP, Real.log_prod (fun τ _ => by push_cast; positivity)]
      rw [← Equiv.sum_comp π (fun τ => Real.log (1 + ((κ τ : ℝ) + ((1 : ℕ) : ℝ))))]
      refine Finset.sum_congr rfl fun τ _ => ?_
      push_cast; ring_nf
    have h4 : Real.log (‖riemannZeta (3 / 2)‖ ^ n) ≤ c * n := by
      rw [Real.log_pow]; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith
  · have h := GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow D.host.E χ Λ s hχ.1 hΛ (by
      simp only [Complex.natCast_re]; have : (2 : ℝ) ≤ s := by exact_mod_cast h2
      linarith)
    have h4 : Real.log ‖Λ s‖ ≤ c * n := by
      calc Real.log ‖Λ s‖ ≤ Real.log (‖riemannZeta (3 / 2)‖ ^ n) := Real.log_le_log hpos h
        _ = n * Real.log ‖riemannZeta (3 / 2)‖ := Real.log_pow _ _
        _ ≤ c * n := by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith

end GlobalTheory.SqTop

end
