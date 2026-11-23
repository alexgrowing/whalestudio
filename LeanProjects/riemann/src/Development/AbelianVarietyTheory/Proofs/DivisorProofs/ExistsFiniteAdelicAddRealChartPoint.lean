import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF

theorem exists_realZero_add_iotaVF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ)
    (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E), IsChartF θ ι →
      ∀ w : WOF F E nS nT, ∃ (u : WOF F E nS nT) (v : IxF F nS nT → ℂ), u.map (infPartF F E) = 0 ∧ w = u + iotaVF ι v := by
  intro F E _ _ _ _ _ nS nT θ ι hι w
  refine ⟨w - iotaVF ι (piWF θ w), piWF θ w, ?_, by abel⟩
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  set a := infPartF F E ((w - iotaVF ι (piWF θ w)) i j) with ha
  have hθ : ∀ w', θ w' a = 0 := by
    intro w'
    rw [ha, Matrix.sub_apply, map_sub, map_sub]
    simp only [iotaVF, piWF, Matrix.of_apply]
    rw [hι.comp]
    exact sub_self _
  have h0 := hι.ext (Formalism.L2.Fam.ThC.pairE a 0) (Formalism.L2.Fam.ThC.snd_pairE a 0) (by
    intro w'
    have : infPartF F E (Formalism.L2.Fam.ThC.pairE a 0) = a := Formalism.L2.Fam.ThC.fst_pairE a 0
    rw [this]; exact hθ w')
  have : infPartF F E (Formalism.L2.Fam.ThC.pairE a 0) = a := Formalism.L2.Fam.ThC.fst_pairE a 0
  rw [← this, h0, map_zero]

end GlobalTheory.RealWeilF
