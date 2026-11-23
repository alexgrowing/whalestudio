import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open DiscreteGroups.T1.G
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

private theorem pow_mul_exp_neg_le (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ N * Real.exp (-r) ≤ N.factorial * Real.exp 1 := by
  have h := Real.pow_div_factorial_le_exp (1 + r) (by linarith) N
  rw [div_le_iff₀ (by exact_mod_cast N.factorial_pos)] at h
  have e : Real.exp r * Real.exp (-r) = 1 := by rw [← Real.exp_add]; simp
  calc (1 + r) ^ N * Real.exp (-r) ≤ (Real.exp (1 + r) * N.factorial) * Real.exp (-r) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = N.factorial * Real.exp 1 * (Real.exp r * Real.exp (-r)) := by rw [Real.exp_add]; ring
    _ = N.factorial * Real.exp 1 := by rw [e, mul_one]

private theorem point_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hB : Basic) (hS : Sizes)
    (hn : 1 ≤ n) {π : CuspSub E n} (hθ : ThetaFix π) {ψ : Sm E n} (hψ : ψ ∈ π.V) (M : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R ρ : ℝ, 0 ≤ R → ∀ x : H E n 0, |ldet x| ≤ R → ρ ≤ r0 x →
      ‖ψ.1 x.1‖ ≤ A * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) * wt x ^ (-(2 * M : ℤ)) := by
  obtain ⟨h1, h2, -⟩ := hB E n hn
  obtain ⟨c, hc0, hc⟩ := hS E n hn
  have hA := hθ.1 ψ hψ
  obtain ⟨C₀, hC₀⟩ := Dcy.cp_decay ψ (π.cusp ψ hψ) hA 0 (L + 1)
  set a : ℝ := redSize (1 : GA E 0) with ha
  have ha0 : 0 ≤ a := Dcy.redSize_nonneg _
  set c₁ : ℝ := 2 + a + c with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set C : ℝ := max C₀ 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  set K : ℝ := ((2 * M).factorial : ℝ) * Real.exp 1 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨C * c₁ ^ (2 * M) * K, by positivity, fun R ρ hR x hx hρ => ?_⟩
  obtain ⟨hs, -, hr⟩ := hc x
  set r : ℝ := r0 x with hrdef
  set y : H E n 0 := ac E n (-ldet x) * x with hy
  have hy0 : ldet y = 0 := by rw [hy, h2, h1]; ring
  have hψy : ψ.1 y.1 = ψ.1 x.1 := hA _ _
  have hdec : ‖ψ.1 x.1‖ ≤ C * Real.exp (-((L + 1) * r)) := by
    have h := hC₀ y.1 (by
      have : |ldet y| ≤ 0 := by rw [hy0]; simp
      exact this)
    rw [hψy] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hx2 : x.2 = 1 := Units.ext (Subsingleton.elim _ _)
  have hw : wt x = 1 + redSize x.1 + a := by rw [wt, hx2]
  have hrs := Dcy.redSize_nonneg x.1
  have hw1 : 1 ≤ wt x := by rw [hw]; linarith
  have hP : 1 ≤ (1 + r) * (1 + R) := by nlinarith [mul_nonneg hr hR]
  have hwle : wt x ≤ c₁ * ((1 + r) * (1 + R)) := by
    have h3 : c * (1 + |ldet x|) ≤ c * (1 + R) := mul_le_mul_of_nonneg_left (by linarith) hc0
    have h4 : 1 + R ≤ (1 + r) * (1 + R) := by nlinarith [mul_nonneg hr hR]
    have h5 : 1 + r ≤ (1 + r) * (1 + R) := by nlinarith [mul_nonneg hr hR]
    have h6 : c * (1 + R) ≤ c * ((1 + r) * (1 + R)) := mul_le_mul_of_nonneg_left h4 hc0
    have h7 : (1 + a) * 1 ≤ (1 + a) * ((1 + r) * (1 + R)) := mul_le_mul_of_nonneg_left hP (by linarith)
    rw [hw, hc₁]
    nlinarith
  have hexp : Real.exp (-((L + 1) * r)) ≤ Real.exp (-(L * ρ)) * Real.exp (-r) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hρ hL]
  have hpow : wt x ^ (2 * M) ≤ c₁ ^ (2 * M) * ((1 + r) ^ (2 * M) * (1 + R) ^ (2 * M)) := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hwle _
  have hwpos : 0 < wt x ^ (2 * M) := pow_pos (by linarith) _
  have hz : wt x ^ (-(2 * M : ℤ)) = (wt x ^ (2 * M))⁻¹ := by
    rw [_root_.zpow_neg]
    congr 1
  have hr1 : 0 ≤ 1 + r := by linarith
  have hR1 : 0 ≤ 1 + R := by linarith
  have hmain : ‖ψ.1 x.1‖ * wt x ^ (2 * M) ≤ C * c₁ ^ (2 * M) * K * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) := by
    have hq := pow_mul_exp_neg_le (2 * M) hr
    calc ‖ψ.1 x.1‖ * wt x ^ (2 * M)
        ≤ (C * (Real.exp (-(L * ρ)) * Real.exp (-r))) *
            (c₁ ^ (2 * M) * ((1 + r) ^ (2 * M) * (1 + R) ^ (2 * M))) :=
          mul_le_mul (hdec.trans (mul_le_mul_of_nonneg_left hexp hC0)) hpow hwpos.le (by positivity)
      _ = C * c₁ ^ (2 * M) * ((1 + r) ^ (2 * M) * Real.exp (-r)) * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) := by ring
      _ ≤ C * c₁ ^ (2 * M) * K * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) := by
          gcongr
  rw [hz, ← div_eq_mul_inv, le_div_iff₀ hwpos]
  exact hmain

theorem domInt_pf : Basic → Sizes → DomInt := by
  intro hB hS E _ _ _ n hn D π hθ ψ hψ Ω hΩ
  refine ⟨2 * (2 * n), fun L hL => ?_⟩
  obtain ⟨A, hA0, hA⟩ := point_bound hB hS hn hθ hψ (2 * n) L hL
  have hI := wtCount E n 0 D Ω hΩ (2 * n) (by omega)
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (wt x ^ (-(2 * ((2 * n : ℕ) : ℤ)))) * cnt (ratH E n 0) Ω x ∂D.ν with hIdef
  refine ⟨A * I.toReal, mul_nonneg hA0 ENNReal.toReal_nonneg, fun R ρ hR => ?_⟩
  set B : ℝ := A * (1 + R) ^ (2 * (2 * n)) * Real.exp (-(L * ρ)) with hBdef
  have hR1 : 0 ≤ 1 + R := by linarith
  have hB0 : 0 ≤ B := by positivity
  calc ∫⁻ x, {x | |ldet x| ≤ R ∧ ρ ≤ r0 x}.indicator (fun x => ‖ψ.1 x.1‖ₑ * cnt (ratH E n 0) Ω x) x ∂D.ν
      ≤ ∫⁻ x, ENNReal.ofReal B * (ENNReal.ofReal (wt x ^ (-(2 * ((2 * n : ℕ) : ℤ)))) * cnt (ratH E n 0) Ω x) ∂D.ν := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ {x : H E n 0 | |ldet x| ≤ R ∧ ρ ≤ r0 x}
        · rw [Set.indicator_of_mem hx, ← mul_assoc, ← ENNReal.ofReal_mul hB0, ← ofReal_norm]
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hA R ρ hR x hx.1 hx.2)) _
        · rw [Set.indicator_of_notMem hx]
          exact zero_le
    _ = ENNReal.ofReal B * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (A * I.toReal * (1 + R) ^ (2 * (2 * n)) * Real.exp (-(L * ρ))) := by
        rw [show A * I.toReal * (1 + R) ^ (2 * (2 * n)) * Real.exp (-(L * ρ)) = B * I.toReal by rw [hBdef]; ring,
          ENNReal.ofReal_mul hB0, ENNReal.ofReal_toReal hI]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
