import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterIffIsCuspidalGLnFiniteField
import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V → (GlobalTheory.GLq.IsCusp (fun x => V.character x) ↔ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V) := by
  first | exact @GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal | exact GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal | (intros; apply GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal <;> assumption)
