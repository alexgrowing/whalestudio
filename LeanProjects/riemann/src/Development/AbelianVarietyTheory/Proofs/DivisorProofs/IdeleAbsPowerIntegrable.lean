import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrablePowerNormCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LocTateInt

theorem integrableOn_absE_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (μ : Measure (idelesAt E (evFin F v))), μ.IsHaarMeasure → ∀ C : Set (Fv F v ⊗[F] E), IsCompact C → ∀ e : ℕ, 1 ≤ e →
      IntegrableOn (fun l : idelesAt E (evFin F v) => (absE F E l.1 : ℝ) ^ e)
        {l | ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ C} μ := by
  intro F E _ _ _ _ _ v μ hμ C hC e he
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  obtain ⟨μ₀, h₀, -⟩ := existsUnique_isNormE E v
  haveI := h₀.1
  haveI := t2Space_Fv_tensor (E := E) v
  obtain ⟨c, -, hc⟩ := haar_idelesAt_eq_smul μ μ₀
  have hm : MeasurableSet {l : idelesAt E (evFin F v) |
      ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ C} :=
    (hC.isClosed.preimage (Units.continuous_val.comp (idelesAtEquiv E v).continuous)).measurableSet
  rw [← integrable_indicator_iff hm, hc]
  refine Integrable.smul_measure ?_ ENNReal.coe_ne_top
  have hfun : {l : idelesAt E (evFin F v) |
      ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ C}.indicator
        (fun l : idelesAt E (evFin F v) => (absE F E l.1 : ℝ) ^ e) =
      fun l : idelesAt E (evFin F v) => C.indicator (fun _ => ((absE F E l.1 : ℝ)) ^ e) (compFin F E v l.1) := by
    funext l
    by_cases h : compFin F E v l.1 ∈ C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show l ∈ _ from h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show l ∉ _ from h)]
  rw [hfun]
  exact integrable_indicator_absE_pow v μ₀ h₀ C hC e he

end GlobalTheory.LocTateInt
