import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecialDatumCentralCharacterAtZero
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_datum_central_character_at_zero : ∀ (K : Type) [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → m.IsSp → ∀ (a : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)), m.val (dg2 a a * g) 0 = om0 m a * m.val g 0 := by
  first | exact @GlobalTheory.CompanionTheory.CenTheta.val_zero_central_sp | exact GlobalTheory.CompanionTheory.CenTheta.val_zero_central_sp | (intros; apply GlobalTheory.CompanionTheory.CenTheta.val_zero_central_sp <;> assumption)
