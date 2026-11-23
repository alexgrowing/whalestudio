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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTrianglePeriodExpansionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumPairCoordinateAlgebraicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.BotAlgI'

theorem classSums'_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  obtain ⟨Ω, hΩ, H⟩ := GlobalTheory.T.bottom_triangle_period_expansion hP hI hL hX
  refine ⟨Ω, hΩ, fun t h hh k => ?_⟩
  obtain ⟨n, c, z, hc, hz, he⟩ := H t h hh k
  rw [he, mul_div_cancel_left₀ _ hΩ]
  have hz' : ∀ l, IsAlgebraic ℚ (z l) := fun l => by
    obtain ⟨δ, t0, Q, P, h', U, e⟩ := hz l
    rw [e]; exact GlobalTheory.T.norm_sum_pair_coordinate_algebraic hP hI D δ t0 Q P h' U
  have : ∀ l, (c l * z l) ∈ algebraicClosure ℚ ℂ := fun l =>
    mul_mem (mem_algebraicClosure_iff.2 (hc l)) (mem_algebraicClosure_iff.2 (hz' l))
  exact mem_algebraicClosure_iff.1 (sum_mem fun l _ => this l)

end GlobalTheory.BotAlgI'
