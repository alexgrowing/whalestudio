import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
import Formalism.RealPlaceAnalysis.StatementE

noncomputable section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaDens

variable {D : D7}

def Sobolev₂ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T S' T' : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (μ' : Measure (WO S' T')) (𝓕' : Set (WO S' T')) (Z : (WO S T → ℂ) → WO S' T' → ℂ) : Prop :=
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ U' : AddSubgroup (WO S' T'), IsOpen (U' : Set (WO S' T')) ∧
    (∀ f ∈ thetaLevel ψ S T U, Z f ∈ thetaLevel ψ S' T' U') ∧
    ∀ d : ℕ, ∃ (d' : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, sobO ψ θ μ' 𝓕' d (Z f) ≤ C * sobO ψ θ μ 𝓕 d' f

theorem sobCont_id (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) :
    Sobolev₂ ψ θ μ 𝓕 μ 𝓕 id := fun U hU => ⟨U, hU, fun _ h => h, fun d => ⟨d, 1, fun _ _ => by simp⟩⟩

def SobBdd (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (L : (WO S T → ℂ) → GA D S → ℝ≥0∞) : Prop :=
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ K : Set (GA D S), IsCompact K →
    ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, ∀ x ∈ K, L f x ≤ C * sobO ψ θ μ 𝓕 d f

def evalAt {A : Type} [Ring A] [Algebra ℂ A] (a : ℕ → A) (z : MvPolynomial ℕ ℂ) : A :=
  ∑ k ∈ z.support, z.coeff k • ((Multiset.toList (Finsupp.toMultiset k)).map a).prod

def IsCap (N : ℕ) (u : ℂ) (z : MvPolynomial ℕ ℂ) : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (E : Fin N → Fin N → A), Formalism.REAL.GlRel E →
    Formalism.REAL.qdet E u = evalAt (GlobalTheory.SmoothForms.gelfA E) z

def wt (m r : ℕ) (t : ℂ) (i : Fin m) : ℂ := if (i : ℕ) < r then -t else if (i : ℕ) + r < m then 0 else t

def lineMean {S T : HSp D} (ξ : Matrix (Fin T.rank) (Fin 1) D.host.E) (μ : Measure (Mx D 1 S.rank))
    (𝓕 : Set (Mx D 1 S.rank)) (f : WO S T → ℂ) : ℂ :=
  ∫ x in 𝓕, f ((rat ξ : Mx D T.rank 1) ⬝ x) ∂μ

end GlobalTheory.ThetaDens

end
