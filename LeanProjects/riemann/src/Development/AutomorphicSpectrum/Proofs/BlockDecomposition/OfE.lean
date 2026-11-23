import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSetsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionPreservesHaarLocalStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarEqProductLocalMeasures
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def Psi (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (Y : Fin 1 → Fin 1 → AF F ⊗[F] E) : ℝ≥0∞ :=
  {Y : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin Y) ∈ A v}.indicator
    (fun Y => ENNReal.ofReal (φ (projInf Y))) Y

def Th (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (y : (AF F ⊗[F] E)ˣ) : ℝ≥0∞ :=
  ∑' X : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _),
    Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X.1 a i))

def ofF : (AF F)ˣ →* (AF F ⊗[F] E)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : AF F →ₐ[F] AF F ⊗[F] E).toMonoidHom

def ofE : Eˣ →* (AF F ⊗[F] E)ˣ := Units.map (inclR (AF F)).toMonoidHom

end

def cV {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    AF F ⊗[F] E →ₐ[F] Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).comp
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))

def cI {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] :
    AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E :=
  Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)

def ue {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E) (h : HA R σ J) : (R ⊗[F] E)ˣ :=
  Matrix.GeneralLinearGroup.det (HA.mat R σ J h)

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
