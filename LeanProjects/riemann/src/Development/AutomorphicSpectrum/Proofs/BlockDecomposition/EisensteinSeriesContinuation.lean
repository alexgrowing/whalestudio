import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightContinuousPosStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatSectionGrowthBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesConvergentStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CompanionTheory.SiegelEis

theorem rpow_le_add_rpow {A u c d : ℝ} (hA : 0 < A) (hc : c ≤ u) (hd : u ≤ d) :
    A ^ u ≤ A ^ c + A ^ d := by
  rcases le_total 1 A with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h hd
    have := Real.rpow_nonneg hA.le c
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hA h hc
    have := Real.rpow_nonneg hA.le d
    linarith

theorem differentiable_cpow_term {A : ℝ} (hA : 0 < A) (s₁ w : ℂ) :
    Differentiable ℂ (fun s : ℂ => (A : ℂ) ^ (s - s₁) * w) := by
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  exact ((differentiable_id.sub_const s₁).const_cpow (Or.inl hA')).mul_const w

theorem eis_half_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ Ê : ℂ → G2 σ Y → ℂ, ∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧ ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re} := by
  intro F E _ _ _ _ _ σ B n Y r s' hB hn hY b K a hb hK hH χ s₁ f hf
  have hKc := GlobalTheory.T.isCompact_standard_maximal F E σ B n Y r s' hB hn hY b K a hb hK hH
  obtain ⟨-, hpos⟩ := GlobalTheory.T.height_function_continuous_pos' F E σ B n Y r s' hB hn hY b K a hb hK hH
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.flat_section_growth_bound K a hKc hH hpos χ s₁ f hf
  obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.T.eisenstein_series_convergent F E σ B n Y r s' hB hn hY b K a hb hK hH
  have hC : ∀ s x, ‖flat a f s₁ s x‖ ≤ max C₀ 0 * a x ^ (s.re + (n : ℝ) / 2) := fun s x =>
    (hC₀ s x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hpos x).le _))
  have hsum : ∀ σ' : ℝ, σ₀ < σ' → ∀ x, Summable fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ' := by
    intro σ' h x
    obtain ⟨C', N, h'⟩ := hσ₀ σ' h
    exact (h' x).1
  refine ⟨fun s x => ∑' q, eisTerm (flat a f s₁ s) x q, σ₀ - (n : ℝ) / 2, ?_, ?_⟩
  · intro s hs x
    apply Summable.hasSum
    have hg := (hsum (s.re + (n : ℝ) / 2) (by linarith) x).mul_left (max C₀ 0)
    first
      | exact Summable.of_norm_bounded _ hg (fun q => hC s _)
      | exact Summable.of_norm_bounded hg (fun q => hC s _)
  · intro x s₀ hs₀
    have hs₀' : σ₀ - (n : ℝ) / 2 < s₀.re := hs₀
    set c := (σ₀ - (n : ℝ) / 2 + s₀.re) / 2 with hc
    set d := s₀.re + 1 with hd
    have hU : IsOpen {s : ℂ | c < s.re ∧ s.re < d} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
    have hmem : {s : ℂ | c < s.re ∧ s.re < d} ∈ 𝓝 s₀ :=
      hU.mem_nhds ⟨by linarith, by linarith⟩
    have hg : Summable fun q : Cos σ Y => max C₀ 0 * (a ((Quotient.out q).1 * x) ^ (c + (n : ℝ) / 2) +
        a ((Quotient.out q).1 * x) ^ (d + (n : ℝ) / 2)) :=
      ((hsum _ (by linarith) x).add (hsum _ (by linarith) x)).mul_left (max C₀ 0)
    have hD : DifferentiableOn ℂ (fun s => ∑' q, eisTerm (flat a f s₁ s) x q) {s : ℂ | c < s.re ∧ s.re < d} := by
      refine Complex.differentiableOn_tsum_of_summable_norm (F := fun q s => eisTerm (flat a f s₁ s) x q) hg
        (fun q => ?_) hU (fun q s hs => ?_)
      · exact (differentiable_cpow_term (hpos _) s₁ (f ((Quotient.out q).1 * x))).differentiableOn
      · refine (hC s _).trans (mul_le_mul_of_nonneg_left (rpow_le_add_rpow (hpos _) ?_ ?_) (le_max_right _ _))
        · linarith [hs.1]
        · linarith [hs.2]
    exact (hD.differentiableAt hmem).differentiableWithinAt

end GlobalTheory.CompanionTheory.SiegelEis
