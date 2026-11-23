import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocAlg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicDecompositionUpperHalfSpaceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivGaussianExponentialAtZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivIntegralGaussianExponentialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivEqOfEqOnRealSegmentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatCellParabolicUnipotentFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicParameterIntegralGaussianBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInjectiveMatrixSpaceStatement

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Kdil

open PositivityTheory.Rg.Sw.Glob (actZ)
open Matrix

variable {n : ℕ}

theorem up_decomp_pf (p : GR n) (hp : (mR p).toBlocks₂₁ = 0) :
    ∃ (nb ma : GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧ mR nb = nU b ∧ mR ma = mLoc a ∧
      p = nb * ma ∧ actZ p (Complex.I • 1) = b + Complex.I • (a * aᴴ) :=
  GlobalTheory.T.parabolic_decomposition_upper_half_space n p hp

theorem fam_deriv_pf (m : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (r : ℕ) :
    iteratedDeriv r (fun z => fam m X z v) 0 = fP ((dil (2 * Real.pi) X ^ r) 1) v :=
  (GlobalTheory.T.iteratedDeriv_gaussian_exponential_at_zero m n X v).2 r

theorem fam_int_hol_pf (m : ℕ) (X : Fin n → ℝ) (K : (Fin m → Fin n → ℂ) → ℂ) (hK : Continuous K)
    (hK1 : ∀ v, ‖K v‖ ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * fam m X z v) (Metric.ball 0 ρ) ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * fam m X z v) 0 =
        ∫ v, K v * iteratedDeriv r (fun z => fam m X z v) 0 :=
  GlobalTheory.T.iteratedDeriv_integral_gaussian_exponential m n X K hK hK1

theorem iteratedDeriv_eq_of_real_pf {f g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hf : DifferentiableOn ℂ f (Metric.ball 0 ρ))
    (hg : DifferentiableOn ℂ g (Metric.ball 0 ρ)) (hfg : ∀ s : ℝ, |s| < ρ → f s = g s) (r : ℕ) :
    iteratedDeriv r f 0 = iteratedDeriv r g 0 :=
  GlobalTheory.T.iteratedDeriv_eq_of_eq_on_real_segment f g ρ hρ hf hg hfg r

theorem dcell_pf (y : GR n) (hy : ((mR y).toBlocks₂₂).det ≠ 0) :
    ∃ (p nbb : GR n) (c : Matrix (Fin n) (Fin n) ℂ), (mR p).toBlocks₂₁ = 0 ∧ cᴴ = c ∧ mR nbb = nbLoc c ∧ y = p * nbb :=
  GlobalTheory.T.bruhat_cell_parabolic_unipotent_factorization n y hy

theorem hol_int_pf {m : ℕ} (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hd : ∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ))
    (hc : ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2) (Metric.ball 0 ρ ×ˢ Set.univ))
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * sq v))
    (K : (Fin m → Fin n → ℂ) → ℂ) (hK : Continuous K) (hK1 : ∀ v, ‖K v‖ ≤ 1) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 = ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧
        Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧
        ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤ C' * Real.exp (-δ * sq v) :=
  GlobalTheory.T.holomorphic_parameter_integral_gaussian_bound m n Φ ρ C δ hρ hδ hd hc hb K hK hK1

theorem ft_uniq_pf {m : ℕ} (s : ℂ) (hs : s ≠ 0) (g : (Fin m → Fin n → ℂ) → ℂ) (hg : Continuous g) (hgi : Integrable g)
    (h0 : ∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I *
      ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) : g = 0 :=
  GlobalTheory.T.fourier_injective_matrix_space m n s hs g hg hgi h0

theorem up_decomp_closed : type_of% @up_decomp_pf := @up_decomp_pf

theorem fam_deriv_closed : type_of% @fam_deriv_pf := @fam_deriv_pf

theorem fam_int_hol_closed : type_of% @fam_int_hol_pf := @fam_int_hol_pf

theorem iteratedDeriv_eq_of_real_closed : type_of% @iteratedDeriv_eq_of_real_pf := @iteratedDeriv_eq_of_real_pf

theorem dcell_closed : type_of% @dcell_pf := @dcell_pf

theorem hol_int_closed : type_of% @hol_int_pf := @hol_int_pf

theorem ft_uniq_closed : type_of% @ft_uniq_pf := @ft_uniq_pf

end PositivityTheory.SiegelWeilFormula.Kdil

end
