import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGlLocalComponentExponentLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDetProdConstAt
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.DetProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_gl_local_component_exponent_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (τ : GlobalTheory.CuspRep.CuspSub E n)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))) (x x' : ℕ)
    (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ), GlobalTheory.Published.GenericityGL → 1 ≤ n → τ.IsLocComp w ρ → IsUnramAt w χ₁ →
    IsUnramAt w χ₂ → IsDetProdConstAt w x x' χ₁ χ₂ ρ.ρ → x ≤ 1 ∧ x' ≤ 1 := by
  first | exact @GlobalTheory.ThK.DetProd.blocks_le_one_of_isLocComp | exact GlobalTheory.ThK.DetProd.blocks_le_one_of_isLocComp | (intros; apply GlobalTheory.ThK.DetProd.blocks_le_one_of_isLocComp <;> assumption)
