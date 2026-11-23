import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieWordExpansionUniform
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecompAtZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpace
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIffStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFinAtZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasCtpId
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_word_expansion_uniform : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (φ : GA D N.V → ℂ) (S : GA D N.V → List (List (Mx N.V.rank))) (v : GA D N.V → ℕ → N.M.H τ) (ℓ : GA D N.V → ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : GA D N.V → ℕ → ℝ), (∀ x, Words (lieSet (N.M.ε τ)) (S x)) → (∀ x, Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) (S x)) → (∀ x, Expn (N.M.ε τ) (N.M.σ τ) (S x) (v x) (ℓ x) (C x) (res θ N.V τ (N.M.fr τ) φ x)) → ∀ (c : N.M.H τ) (ψ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GA D N.V → ℂ), (∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Moves θ N.V τ (N.M.ε τ) (N.M.σ τ) (N.M.fr τ) (fun w => ⟪c, w⟫_ℂ • (u : N.M.H τ)) φ (ψ u)) → (∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u) ∧ (∀ u u', ψ (u + u') = ψ u + ψ u') ∧ (∀ (z : ℂ) u, ψ (z • u) = z • ψ u) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = N.M.rep τ k u → ψ w = rTr N.V (atTau θ N.V τ k) (ψ u)) ∧ (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = dRep (N.M.rep τ) X u → ψ w = Rder θ N.V τ X (ψ u)) := by
  first | exact @GlobalTheory.PlaceDecomp.rankOne_values_gkMap | exact GlobalTheory.PlaceDecomp.rankOne_values_gkMap | (intros; apply GlobalTheory.PlaceDecomp.rankOne_values_gkMap <;> assumption)
