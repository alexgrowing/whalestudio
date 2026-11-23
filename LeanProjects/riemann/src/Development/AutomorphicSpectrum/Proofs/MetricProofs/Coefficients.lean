import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationHeightIndependenceStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GapEqWeightSubNextStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FormPolyIsHomogeneousAndEval
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AbsCoeffProdXLeOne
import Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB.Top

theorem abs_limNum_sub_le {D : ℕ} {σ : Type} {S : AnSys D σ} {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} (Re Re' : Realis S P) (II : IntersectionSystem)
    (w : Fin (D + 1) → σ) (B : ℝ) (ht : 0 < S.t₀)
    (h1 : Tendsto (fun t => Re.num II t w) (𝓝[>] 0) (𝓝 (Re.limNum II w)))
    (h2 : Tendsto (fun t => Re'.num II t w) (𝓝[>] 0) (𝓝 (Re'.limNum II w)))
    (hb : ∀ t, 0 < t → t ≤ S.t₀ → |Re.num II t w - Re'.num II t w| ≤ B) :
    |Re.limNum II w - Re'.limNum II w| ≤ B := by
  refine le_of_tendsto (h1.sub h2).abs ?_
  filter_upwards [Ioc_mem_nhdsGT ht] with t ht'
  exact hb t ht'.1 ht'.2

theorem coefficients : Coefficients := by
  intro hI D N Ψ _ S thH hth
  obtain ⟨C₂', hC⟩ := GlobalTheory.T.realisation_height_independence hI D (Option (Ψ × Fin N)) S thH hth
  obtain ⟨Cst, hW, hWS⟩ := GlobalTheory.T.weighted_polynomial_homogeneous_coeff_bound Ψ N (D + 1)
  have ht : 0 < S.t₀ := (S.reg none).1
  refine ⟨Cst * ((Fintype.card (Option (Ψ × Fin N)) : ℝ) ^ (D + 1)) * C₂',
    fun II hII K _ ι _ P Re => ?_⟩
  obtain ⟨C₃, s₀, -, hag⟩ := GlobalTheory.T.agreement_positive hI D (Option (Ψ × Fin N)) S 0 ht
  have hPB : ∀ R : Realis S P, R.PBs II = toWtS (formPoly (D + 1) (R.limNum II)) := fun R => rfl
  have hPBwt : ∀ R : Realis S P,
      R.PBwt II = toWt (formPoly (D + 1) fun w => R.limNum II (some ∘ w)) := fun R => rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hPB]
    exact (hWS _ 0 (formPoly_isHomogeneous_and_eval _ _ _).1).1
  · rw [hPBwt]
    exact (hW _ 0 (formPoly_isHomogeneous_and_eval _ _ _).1).1
  · rw [hPB, hPBwt]
    exact (poly_s_zero Ψ N (D + 1)).1 _
  · intro Re' T α H hdeg hT hH hpot hvc hnef
    have hb := hC II hII K ι P Re Re' T α H hdeg hT hH hpot hvc hnef
    have hlim : ∀ w, |Re.limNum II w - Re'.limNum II w| ≤ C₂' * ∑ p ∈ T, α p * Real.log p :=
      fun w => abs_limNum_sub_le Re Re' II w _ ht ((hag II hII K ι P Re).1 w)
        ((hag II hII K ι P Re').1 w) fun t h0 h1 => hb t h0 h1 w
    have hB0 : 0 ≤ C₂' * ∑ p ∈ T, α p * Real.log p := (abs_nonneg _).trans (hlim fun _ => none)
    have hcard : ((Fintype.card (Ψ × Fin N) : ℝ)) ^ (D + 1) * (C₂' * ∑ p ∈ T, α p * Real.log p) ≤
        ((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) * (C₂' * ∑ p ∈ T, α p * Real.log p) := by
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _) hB0
      rw [Fintype.card_option]
      push_cast
      linarith
    constructor
    · have hhom := ((formPoly_isHomogeneous_and_eval (Option (Ψ × Fin N)) (D + 1) (Re.limNum II)).1).sub
        ((formPoly_isHomogeneous_and_eval (Option (Ψ × Fin N)) (D + 1) (Re'.limNum II)).1)
      have hco : ∀ m, |coeff m (formPoly (D + 1) (Re.limNum II) - formPoly (D + 1) (Re'.limNum II))| ≤
          ((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) * (C₂' * ∑ p ∈ T, α p * Real.log p) :=
        fun m => by
          rw [coeff_sub]
          exact (formPoly_sub_bound _ _ _ _ _ hlim).1 m
      intro m
      rw [hPB, hPB, ← coeff_sub, ← map_sub]
      calc _ ≤ Cst * (((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) *
            (C₂' * ∑ p ∈ T, α p * Real.log p)) := (hWS _ _ hhom).2 hco m
        _ = _ := by ring
    · have hhom := ((formPoly_isHomogeneous_and_eval (Ψ × Fin N) (D + 1)
          (fun w => Re.limNum II (some ∘ w))).1).sub
        ((formPoly_isHomogeneous_and_eval (Ψ × Fin N) (D + 1) (fun w => Re'.limNum II (some ∘ w))).1)
      have hco : ∀ m, |coeff m (formPoly (D + 1) (fun w => Re.limNum II (some ∘ w)) -
          formPoly (D + 1) (fun w => Re'.limNum II (some ∘ w)))| ≤
          ((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) * (C₂' * ∑ p ∈ T, α p * Real.log p) :=
        fun m => by
          rw [coeff_sub]
          exact ((formPoly_sub_bound _ _ _ _ _ fun w => hlim (some ∘ w)).1 m).trans hcard
      intro m
      rw [hPBwt, hPBwt, ← coeff_sub, ← map_sub]
      calc _ ≤ Cst * (((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) *
            (C₂' * ∑ p ∈ T, α p * Real.log p)) := (hW _ _ hhom).2 hco m
        _ = _ := by ring

end GlobalTheory.CompanionTheory.Ar.PB.Top
