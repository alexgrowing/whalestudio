import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterOfPolynomialOfCuspidalLabel
import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidalCharacterOfPolynomial_of_cuspidalLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : Formalism.L2.NT.IsGenSys L.gen), t = L.teich → ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → GlobalTheory.GLq.IsCusp (fun x => V.character x) → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (Formalism.L2.NT.convC t ht L.gen hζ) V P → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) := by
  first | exact @GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel | exact GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel | (intros; apply GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel <;> assumption)
