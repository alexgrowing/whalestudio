import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharSkewHermitianNormScale
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrOfIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinatesGroupLaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipoten
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectHaarMeasureProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSkewA
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addHaarChar_skewHermitian_normScale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) [LocallyCompactSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [SecondCountableTopology (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [MeasurableSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [BorelSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] (l : (AF F ⊗[F] E)ˣ) (L : GlobalTheory.ResidueEisenstein.ModConj.skewA σ j ≃ₜ+ GlobalTheory.ResidueEisenstein.ModConj.skewA σ j), (∀ s, (L s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) = ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))) → addEquivAddHaarChar L = absE F E l ^ (j * j) := by
  first | exact @GlobalTheory.ResidueEisenstein.ModConj.addEquivAddHaarChar_skewA_scale | exact GlobalTheory.ResidueEisenstein.ModConj.addEquivAddHaarChar_skewA_scale | (intros; apply GlobalTheory.ResidueEisenstein.ModConj.addEquivAddHaarChar_skewA_scale <;> assumption)
