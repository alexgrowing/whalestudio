import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWhittakerDiagonalNorm
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComponentRationalIdeleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionDiagonalStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_whittaker_diagonal_norm : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
    L.W (dg2 (nv v κ) 1 * g) = cW L κ * mp (nv v κ) (1 / 2) * locI L g κ := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.SplitW.split_alt | exact GlobalTheory.CompanionTheory.FexTheta.SplitW.split_alt | (intros; apply GlobalTheory.CompanionTheory.FexTheta.SplitW.split_alt <;> assumption)
