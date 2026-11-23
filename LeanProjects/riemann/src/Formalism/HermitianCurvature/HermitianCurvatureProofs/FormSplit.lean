import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferWordEntriesMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelIntegrandAestronglyMeasurable

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Split

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem form_split (μ : Measure (Mt k r)) (l : Fin r) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ)
    (hint : Integrable (fun c' : Cf r l.castSucc =>
      ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (x a) (y a) (glue l.castSucc c c'))) :
    form μ l.castSucc x y c =
      ∫ t : ℂ, ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * form μ l.succ x y (Function.update c l t) := by
  set f : Cf r l.castSucc → ℂ := fun c' =>
    ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (x a) (y a) (glue l.castSucc c c') with hf
  have hmp := coordinate_split_measurePreserving (r := r) l
  have hform : form μ l.castSucc x y c = ∫ c', f c' := rfl
  have h1 : ∫ c', f c' = ∫ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) := by
    rw [← hmp.integral_comp' (fun p => f ((coordinateSplit (r := r) l).symm p))]
    simp only [MeasurableEquiv.symm_apply_apply]
  have hval : ∀ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) = ((‖p.1‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      (((∏ j, ‖p.2 j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (x a) (y a) (glue l.succ (Function.update c l p.1) p.2)) := by
    intro p
    have hw := weight_coordinate_split (r := r) l ((coordinateSplit (r := r) l).symm p)
    have hg := glue_coordinate_split (r := r) l c ((coordinateSplit (r := r) l).symm p)
    simp only [MeasurableEquiv.apply_symm_apply] at hw hg
    simp only [hf]
    rw [hw, hg, Complex.ofReal_mul, mul_assoc]
  have hF : Integrable (fun p : ℂ × Cf r l.succ => f ((coordinateSplit (r := r) l).symm p)) (volume.prod volume) := by
    have := (hmp.symm.integrable_comp_emb (coordinateSplit (r := r) l).symm.measurableEmbedding (g := f)).mpr hint
    exact this
  rw [hform, h1, show (volume : Measure (ℂ × Cf r l.succ)) = volume.prod volume from rfl,
    integral_prod _ hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [hval]
  rw [integral_const_mul]
  rfl

end Split

end Formalism.FourierDecayAlt.P5.HerA
