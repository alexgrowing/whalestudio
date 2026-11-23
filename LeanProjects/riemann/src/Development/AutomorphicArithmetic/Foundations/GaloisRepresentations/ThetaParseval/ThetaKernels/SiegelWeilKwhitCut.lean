import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def IsLevi_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : Prop :=
  ∃ t u : GL (Fin d.n) (AE F E), inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1
def IsPureT_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) : Prop :=
  ∃ (P : InfinitePlace F → PX d.m d.n)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ),
    (∀ v, IsLocallyConstant (g v) ∧ HasCompactSupport (g v)) ∧
    (∀ᶠ v in cofinite, g v = Set.indicator {c | ∀ k, c k ∈ v.adicCompletionIntegers F} 1) ∧
    d.T Φ = fun X => (∏ w, fP (P w) (R.loc w X)) *
      ∏ᶠ v, g v (fun k => HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd X k).2)
def PureSpan_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ, d.KFin Φ → d.T Φ ∈ R.fock →
    ∃ (k : ℕ) (c : Fin k → ℂ) (Φs : Fin k → d.Fn), (∀ i, d.KFin (Φs i) ∧ _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureT_k R (Φs i)) ∧ Φ = ∑ i, c i • Φs i
def CellFormula_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) ν, d.IsCov ν → ∀ ε w, d.IsW ε w → ∀ Φ ∈ d.sch, ∀ (g x : d.G) (β : Mx F E d.n d.n),
    inFrame d.b g = Matrix.fromBlocks 1 β 0 1 →
      d.sec0 Φ (w * g * x) = ∫ Z, d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram Z Z))) * d.T (d.om x Φ) Z ∂ν
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
