import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Formalism.LandauZeroFreeBounds.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteBox
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedExplicitFormula
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.ExplicitFormulaClosed

theorem exists_open_eq_closed (f : ℂ → ℂ) (T : ℝ)
    (hfin : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - 0| ≤ T + 1 ∧ f ρ = 0}.Finite) :
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
      {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - 0| ≤ T ∧ f ρ = 0} =
        {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ f ρ = 0} := by
  have h1 : ∀ᶠ T' in 𝓝[>] T, ∀ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - 0| ≤ T + 1 ∧ f ρ = 0},
      T < |ρ.im| → T' < |ρ.im| := by
    rw [Filter.eventually_all_finite hfin]
    intro ρ _
    by_cases h : T < |ρ.im|
    · exact ((eventually_lt_nhds h).filter_mono nhdsWithin_le_nhds).mono fun _ h' _ => h'
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' h
  have h2 : ∀ᶠ T' in 𝓝[>] T, T' < T + 1 :=
    (eventually_lt_nhds (by linarith)).filter_mono nhdsWithin_le_nhds
  have h3 : ∀ᶠ T' in 𝓝[>] T, T < T' := self_mem_nhdsWithin
  obtain ⟨T', a1, a2, a3⟩ := (h1.and (h2.and h3)).exists
  refine ⟨T', a3.le, a2.le, ?_⟩
  ext ρ
  simp only [Set.mem_setOf_eq, sub_zero] at a1 ⊢
  constructor
  · rintro ⟨b0, b1, b2, b3⟩
    exact ⟨b0, b1, by linarith, b3⟩
  · rintro ⟨b0, b1, b2, b3⟩
    refine ⟨b0, b1, ?_, b3⟩
    by_contra h
    have := a1 ρ ⟨b0, b1, by linarith, b3⟩ (not_le.1 h)
    linarith

theorem explicit_formula_closed : ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ‖GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  obtain ⟨C₂, hC₂, h₂⟩ := GlobalTheory.ZeroBand.zeros_band
  refine ⟨C₁ + C₂, fun q _ χ hχ u T hT hu => ?_⟩
  obtain ⟨T', hT1, hT2, hset⟩ := exists_open_eq_closed (DirichletCharacter.LFunction χ) T
    (GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult q χ 0 (T + 1)).1
  have e1 := (h₁ q χ hχ u T hT hu).2
  have e2 := (h₂ q χ hχ u T T' hT hu hT1 hT2).2
  have hz : zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ) =
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ DirichletCharacter.LFunction χ ρ = 0},
        ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ) := by
    rw [← hset]; rfl
  have hF := (GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  have hsub : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ DirichletCharacter.LFunction χ ρ = 0} ⊆
      zerosIn χ 0 1 := by
    rintro ρ ⟨b0, b1, b2, b3⟩
    exact ⟨b0, b1, by rw [sub_zero]; exact b2.le, b3⟩
  have hZ : ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧
        DirichletCharacter.LFunction χ ρ = 0},
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ ≤
      zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
    unfold zsumR
    rw [finsum_mem_eq_finite_toFinset_sum _ hF, finsum_mem_eq_finite_toFinset_sum _ (hF.subset hsub)]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun ρ _ => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Set.Finite.toFinset_subset_toFinset.2 hsub)
        fun ρ _ _ => by positivity)
    rw [mul_one_div]; rfl
  have hZ0 : 0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) :=
    finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hB : 0 ≤ Real.log (q * u) := Real.log_nonneg (by nlinarith)
  have key : ∀ P Z Z' : ℂ, ‖P + Z'‖ ≤ ‖P + Z‖ + ‖Z' - Z‖ := by
    intro P Z Z'
    have : P + Z' = (P + Z) + (Z' - Z) := by ring
    rw [this]
    exact norm_add_le _ _
  rw [hz]
  refine (key _ _ _).trans ((add_le_add e1 e2).trans ?_)
  generalize (∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧
        DirichletCharacter.LFunction χ ρ = 0},
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) = Z at hZ ⊢
  generalize zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) = Z' at hZ hZ0 ⊢
  generalize u * Real.log (q * u * T) ^ 2 / T = A
  generalize Real.log (q * u) = B at hB ⊢
  have a1 : C₁ * (A + B + Z) ≤ C₁ * (A + B + Z') := mul_le_mul_of_nonneg_left (by linarith) hC₁.le
  have a2 : C₂ * A ≤ C₂ * (A + B + Z') := mul_le_mul_of_nonneg_left (by linarith) hC₂.le
  nlinarith

end GlobalTheory.ExplicitFormulaClosed
