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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaarLiftedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDegreeBoundFourierLiftedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicLiftedKernelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.BotFormulaI'

theorem exists_period_I'_eq_algebraic_sum : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ (n : ℕ) (c z : Fin n → ℂ), (∀ l, IsAlgebraic ℚ (c l)) ∧
      (∀ l, ∃ (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (h' : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (U : GlobalTheory.NormSum.Tup D P.a P.d P.n),
        z l = P.coord h' U) ∧
      X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h = Ω * ∑ l, c l * z l := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  obtain ⟨v, N, z, w, κ, hv, hz, hw, hκ1, hκ2, hcls⟩ := GlobalTheory.T.exists_weighted_average_haar_lifted hP hI hL hX
  obtain ⟨n, hproj⟩ := GlobalTheory.T.exists_degree_bound_fourier_lifted hP hI hL hX
  obtain ⟨Ω, hΩ, hdict⟩ := GlobalTheory.T.period_algebraic_lifted_kernel hP hI hL hX n
  obtain ⟨δ, hδ⟩ := GlobalTheory.NormSum.exists_crv_top D
  obtain ⟨t0, ht0⟩ := ((hI D).t0Ex ⊤ δ hδ).1
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  refine ⟨(v : ℂ) * Ω, mul_ne_zero hv' hΩ, fun t h hh k => ?_⟩
  choose m r U hr heq using fun l => hproj κ hκ1 hκ2 t (z l) (hz l) h hh k
  set S : ℂ := ∑ l, ((w l : ℂ))⁻¹ * ∑ p, r l p * (X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D (U l p)) h (z l) / Ω) with hSdef
  have hval : X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h = (v : ℂ) * Ω * S := by
    rw [hcls t _ h hh, hSdef]
    simp only [heq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro p _
    field_simp
  have hS : IsAlgebraic ℚ S := by
    rw [← mem_algebraicClosure_iff] at *
    refine sum_mem fun l _ => mul_mem (inv_mem ?_) (sum_mem fun p _ => mul_mem ?_ ?_)
    · rw [mem_algebraicClosure_iff]
      simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) ((w l : ℚ)))
    · rw [mem_algebraicClosure_iff]; exact hr l p
    · rw [mem_algebraicClosure_iff]; exact hdict t (z l) (hz l) h hh (U l p)
  refine ⟨1, fun _ => S, fun _ => 1, fun _ => hS,
    fun _ => ⟨δ, t0, 1, GlobalTheory.NormSum.RankZero.pair0 hδ ht0, 1, fun τ j => j.elim0,
      ((GlobalTheory.NormSum.RankZero.normSumPairRankZeroOfCurve_coord_norm hδ ht0).1 _ _).symm⟩, ?_⟩
  rw [hval]
  simp

end GlobalTheory.BotFormulaI'
