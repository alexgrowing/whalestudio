import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicFixedDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarThetaRationalExpansionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFourierIndexRationalPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierIndexRationalPairValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RatMovedAlg

theorem scalar_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∀ (κ : ℂ) (F : WO (GlobalTheory.Grid.neg A) WW → ℂ), GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac F →
        X.ω t (γ, γ') X.vac = κ • F → IsAlgebraic ℚ κ := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2 κ F hF e
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_fourier_index_rational_pair hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2
  obtain ⟨Ω, hΩ, hJ⟩ := GlobalTheory.T.period_algebraic_fixed_degree hP hI hL hX (Finsupp.mapDomain Prod.fst k)
  obtain ⟨n', c', k', hc', hk', he'⟩ := GlobalTheory.T.fourier_index_rational_pair_value hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2 k
  have hψ : IsStdChar D W.ψ (-1) := (hX.is.weil t).std
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hv : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW X.vac := hX.is.isVac.2.theta
  have h0 : heisO W.ψ (GlobalTheory.Grid.neg A) WW 0 X.vac = X.vac := by
    funext w; simp [heisO, symplOH, symplO, hO]
  have alg : ∀ x : ℂ, IsAlgebraic ℚ x ↔ x ∈ algebraicClosure ℚ ℂ := fun x => (mem_algebraicClosure_iff).symm

  have hg : IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
    rw [he', Finset.sum_div, alg]
    refine sum_mem fun p _ => ?_
    rw [mul_div_assoc]
    refine mul_mem ((alg _).1 (hc' p)) ((alg _).1 ?_)
    have := hJ 0 (by simp) (k' p) (hk' p)
    rwa [h0] at this

  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  have hsum : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 =
      ∑ p, c p * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 := by
    rw [GlobalTheory.SpecFac.pureTensorO_sum hψ hθ _ _ _ _ Finset.univ c _
      (fun p _ => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv (w p))]
    simp [Finset.sum_apply]
  have hF' : IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
    rw [hsum, Finset.sum_div, alg]
    refine sum_mem fun p _ => ?_
    rw [mul_div_assoc]
    exact mul_mem ((alg _).1 (hc p)) ((alg _).1 (hJ (w p) (hw p) k rfl))
  have hsm : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 = κ * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 := by
    rw [e, GlobalTheory.FiniteFock.pureTensorO_smul]; rfl
  have hne : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 ≠ 0 := by
    intro h0'; rw [h0', mul_zero] at hsm; exact hk hsm
  have hκ : κ = (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 / Ω) / (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
    rw [hsm]; field_simp
  rw [hκ, alg]
  exact div_mem ((alg _).1 hg) ((alg _).1 hF')

theorem rat_algComb : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (γ, γ') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2
  obtain ⟨κ, F, hF, e⟩ := GlobalTheory.T.exists_scalar_theta_rational_expansion hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2
  have hk := scalar_algebraic hP hI hL hX t γ hγ a ha γ' hγ' a' ha' h1 h2 κ F hF e
  obtain ⟨n, c, w, hc, hw, he⟩ := hF.smul hk
  exact ⟨n, c, w, hc, hw, e.trans he⟩

end GlobalTheory.RatMovedAlg

end
