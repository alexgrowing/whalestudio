import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.JSWPos

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem continuous_colU (r : ℕ) : Continuous (GlobalTheory.JSW.colU (E := E) (a := a) r) := by
  have hM : Continuous fun x : Fin a → Cinf E =>
      Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) :=
    continuous_matrix fun i j => by
      simp only [Matrix.of_apply]
      split_ifs
      · exact continuous_apply i
      · exact continuous_const
  exact Units.continuous_iff.2 ⟨continuous_const.add hM, continuous_const.sub hM⟩

theorem colConv_mem_bddForms {ω : HChar E} {F : GA E a → ℂ} (h : F ∈ bddForms E a ω) (r : ℕ)
    (f : SchwartzMap (Fin a → Cinf E) ℂ) : GlobalTheory.JSW.colConv r f F ∈ bddForms E a ω := by
  haveI : (volume : Measure (Fin a → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨C, hC⟩ := h.2.2.2
  have hfi : Integrable (fun x => f x) (volume : Measure (Fin a → Cinf E)) := f.integrable
  have hu : Continuous fun x : Fin a → Cinf E => infGL E a (GlobalTheory.JSW.colU r x) :=
    GlobalTheory.CuspQuot.continuous_infGL.comp (continuous_colU r)
  have hj : Continuous fun p : GA E a × (Fin a → Cinf E) => f p.2 * F (p.1 * infGL E a (GlobalTheory.JSW.colU r p.2)) :=
    (f.continuous.comp continuous_snd).mul (h.1.comp (continuous_fst.mul (hu.comp continuous_snd)))
  refine ⟨?_, fun γ g => ?_, fun z g => ?_, ∫ x, ‖f x‖ * C, fun g => ?_⟩
  · exact continuous_of_dominated (bound := fun x => ‖f x‖ * C)
      (fun g => (hj.comp (Continuous.prodMk_right g)).aestronglyMeasurable)
      (fun g => .of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))
      (hfi.norm.mul_const C) (.of_forall fun x => hj.comp (Continuous.prodMk_left x))
  · simp only [GlobalTheory.JSW.colConv, mul_assoc, h.2.1]
  · simp only [GlobalTheory.JSW.colConv, mul_assoc, h.2.2.1]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  · exact norm_integral_le_of_norm_le (hfi.norm.mul_const C)
      (.of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))

theorem mspan_le_bddForms {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (h : π.HasCentChar ω) :
    GlobalTheory.JSW.mspan π ≤ bddForms E a ω := by
  refine sInf_le ⟨fun φ hφ => mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω h hφ,
    fun F hF k => mul_right_mem_bddForms hF k, fun F hF f hf => ?_, fun F hF r f => colConv_mem_bddForms hF r f⟩
  exact smoothing_mem_bddForms volume (isTest_of_isTestInf hf) hF

end GlobalTheory.JSWPos
