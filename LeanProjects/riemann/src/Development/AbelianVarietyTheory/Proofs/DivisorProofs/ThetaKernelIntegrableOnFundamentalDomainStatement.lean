import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelIntegrableOnFundamentalDomain
import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_integrableOn_fundamentalDomain : GlobalTheory.Published.SiegelSetUnitary → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (χ χ' : (Formalism.L2.Theta.AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω →
    ∀ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p) → p < M.rank →
    ∀ ν 𝓕, IsHaarFD M ν 𝓕 → ∀ Φ, IsThetaFunO ψ (sgn ε M) X Φ → ∀ τ₀ : D.what₂.Tau,
    (∀ (g : GA D M) (h : GA D X) (S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec (sgn ε M) S₀ r) (μ' : Measure (Mx D X.rank r))
      (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' →
      ∀ (x : Mx D X.rank r) (i : Fin r), (∀ j, compAt θ τ₀ x j i = 0) → d.mixS X ψ μ' 𝓕' (ω (g, h) Φ) x 0 = 0) →
    ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν := by
  first | exact @GlobalTheory.ThetaCuspInteg.integrableOn_thetaKO | exact GlobalTheory.ThetaCuspInteg.integrableOn_thetaKO | (intros; apply GlobalTheory.ThetaCuspInteg.integrableOn_thetaKO <;> assumption)
