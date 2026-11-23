import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
private theorem deg_finrank_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (x : GA E n)
    (W : Submodule E (Fin n → E)) (hW : Module.finrank E W = 0) : deg x W = 0 := by
  have key : ∀ (k : ℕ) (M : Matrix (Fin n) (Fin k) E), k = 0 → degM x M = 0 := by
    rintro k M rfl
    exact degM_zero x M
  exact key _ _ hW

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
private theorem logSize_inv' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (h : GA E n) :
    logSize (h⁻¹ : GA E n) = logSize h := by
  simp only [logSize, inv_inv]
  exact add_comm _ _

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
private theorem tau_le_prof {n k : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (h1 : 1 ≤ k) (hk : k ≤ n) : τ ≤ prof n τ k := by
  have a : (1 : ℝ) ≤ k := by exact_mod_cast h1
  have b : (k : ℝ) ≤ n := by exact_mod_cast hk
  have c : (1 : ℝ) ≤ 2 * n + 1 - k := by linarith
  have d : (1 : ℝ) ≤ (k : ℝ) * (2 * n + 1 - k) := by nlinarith
  have e : τ * 1 ≤ τ * ((k : ℝ) * (2 * n + 1 - k)) := mul_le_mul_of_nonneg_left d hτ
  simp only [prof]
  nlinarith

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.inCut_pf :
    InCut := by
  intro E _ _ _ n
  obtain ⟨C, hC0, hC⟩ := E1.degRight E n
  obtain ⟨B, hB⟩ := (D1.degBdd E n).1 (1 : GA E n)
  have hB' : ∀ W, deg (1 : GA E n) W ≤ B := fun W => hB ⟨W, rfl⟩
  set A : ℝ := deg (1 : GA E n) ⊤ with hA
  refine ⟨|B| + |A| + 2 * C + 1, by positivity, fun τ g hτ => ?_⟩
  have hr : 0 ≤ redSize g := ((E1.redBasic E n).2.1 g).1
  have hcr : C * redSize g ≤ (|B| + |A| + 2 * C + 1) * redSize g := by
    apply mul_le_mul_of_nonneg_right _ hr
    have := abs_nonneg B
    have := abs_nonneg A
    linarith
  have hexp : (|B| + |A| + 2 * C + 1) * (1 + redSize g) =
      (|B| + |A| + 2 * C + 1) + (|B| + |A| + 2 * C + 1) * redSize g := by ring
  have hBa := le_abs_self B
  have hAa := neg_abs_le A
  have hBn := abs_nonneg B
  have hAn := abs_nonneg A
  have hτ0 : 0 ≤ τ := by
    have : 0 ≤ (|B| + |A| + 2 * C + 1) * redSize g := mul_nonneg (by positivity) hr
    linarith
  obtain ⟨γ, hγ⟩ : ∃ γ : GL (Fin n) E, logSize (ratGL E n γ * g) < redSize g + 1 :=
    exists_lt_of_ciInf_lt (lt_add_one (redSize g))
  have hinv := ((E1.mahler_holds E n τ).2.1 γ g)
  refine hinv.1 ?_
  set h : GA E n := ratGL E n γ * g with hh
  have hup : ∀ W, deg h W ≤ B + C * (2 + redSize g) := by
    intro W
    have s := hC 1 h W
    rw [one_mul] at s
    have t : C * (1 + logSize h) ≤ C * (2 + redSize g) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    linarith [hB' W]
  refine ⟨fun W => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Module.finrank E W) with h0 | h1
    · rw [deg_finrank_zero h W h0, h0]
      simp [prof]
    · have hk : Module.finrank E W ≤ n := by
        have := Submodule.finrank_le W
        simpa using this
      refine le_trans (hup W) (le_trans ?_ (tau_le_prof hτ0 h1 hk))
      linarith
  · have s := hC h (h⁻¹ : GA E n) ⊤
    rw [mul_inv_cancel, logSize_inv'] at s
    have t : C * (1 + logSize h) ≤ C * (2 + redSize g) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    linarith
