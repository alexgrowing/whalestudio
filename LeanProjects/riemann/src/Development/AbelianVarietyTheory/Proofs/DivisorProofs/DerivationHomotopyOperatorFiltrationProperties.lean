import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationContractionLieDerivativeDeRhamRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractionLieDerivativeDivPowerCompatFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBasStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.HotFil

theorem hot_fil : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B) (e : ℕ → B) (N : ℕ), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → (∀ k, e k ∈ fil δ k) → (∀ x y, hot v e N (x + y) = hot v e N x + hot v e N y) ∧ (∀ b, hot v e N (algebraMap B (DR R B) b) = 0) ∧ (∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], hot v e N x ∈ ⋀[B]^j Ω[B⁄R]) ∧ (∀ x ∈ rel R δ, hot v e N x ∈ rel R δ) ∧ ∀ n, ∀ x ∈ filDR R δ n, hot v e N x ∈ filDR R δ (n + 1) := by
  intro R B _ _ _ J δ v e N hv he
  obtain ⟨hc0, -, -, -, -, hcdeg⟩ := (GlobalTheory.T.derivationContraction_lieDerivative_deRham_rules).1 R B v
  obtain ⟨-, -, -, -, -, hldeg⟩ := (GlobalTheory.T.derivationContraction_lieDerivative_deRham_rules).2 R B v
  have hrel := (GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules).1
  have hfil := (GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules).2
  obtain ⟨-, -, -, -, hfil0, hanti, hsmul⟩ := (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).1 R B J δ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [hot, map_add, smul_add, Finset.sum_add_distrib]
  · intro b
    simp only [hot, hc0, map_zero, smul_zero, Finset.sum_const_zero]
  · intro j x hx
    have hc := hcdeg j x hx
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ ⋀[B]^j Ω[B⁄R] := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact hldeg j _ ih
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (hk k)
  · intro x hx
    have hc := (hrel R B J δ v hv x hx).1
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ rel R δ := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact (hrel R B J δ v hv _ ih).2
    refine Ideal.sum_mem _ fun k _ ↦ ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hk k)
  · intro n x hx
    have hc := (hfil R B J δ v hv n).1 x hx
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ filDR R δ (n - k) := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        rcases Nat.eq_zero_or_pos (n - k) with h0 | hpos
        · have : n - (k + 1) = 0 := by omega
          rw [this, hfil0]
          exact Submodule.mem_top
        · have h1 : n - k = (n - (k + 1)) + 1 := by omega
          rw [h1] at ih
          exact (hfil R B J δ v hv (n - (k + 1))).2.2 _ ih
    refine Ideal.sum_mem _ fun k _ ↦ ?_
    have hek : (-1) ^ k * e (k + 1) ∈ fil δ (k + 1) := Ideal.mul_mem_left _ _ (he (k + 1))
    exact hanti (n + 1) ((k + 1) + (n - k)) (by omega) (hsmul (k + 1) (n - k) _ hek _ (hk k))

end GlobalTheory.PDForm.HotFil
