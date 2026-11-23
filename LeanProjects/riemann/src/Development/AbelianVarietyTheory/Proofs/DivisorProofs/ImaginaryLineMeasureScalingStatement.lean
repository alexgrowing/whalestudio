import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImaginaryLineMeasureScaling
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemImLine

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imaginary_line_measure_scaling : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (l : (AE F E)ˣ) [IsTopologicalAddGroup (GlobalTheory.UnipConj.imLine σ)] [LocallyCompactSpace (GlobalTheory.UnipConj.imLine σ)]
    [MeasurableSpace (GlobalTheory.UnipConj.imLine σ)] [BorelSpace (GlobalTheory.UnipConj.imLine σ)]
    (Bl : GlobalTheory.UnipConj.imLine σ ≃ₜ+ GlobalTheory.UnipConj.imLine σ),
    (∀ t, (Bl t : AE F E) = l.1 * cA σ l.1 * t) → addEquivAddHaarChar Bl = absE F E l := by
  first | exact @GlobalTheory.UnipConj.LineModulus.addEquivAddHaarChar_imLine | exact GlobalTheory.UnipConj.LineModulus.addEquivAddHaarChar_imLine | (intros; apply GlobalTheory.UnipConj.LineModulus.addEquivAddHaarChar_imLine <;> assumption)
