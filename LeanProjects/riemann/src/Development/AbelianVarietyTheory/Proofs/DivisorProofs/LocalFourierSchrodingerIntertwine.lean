import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeylFour

theorem schr_fourV_loc : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl F) (κ : Type) [Fintype κ]
    (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    fourV ψ v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (w.2, -w.1) (fourV ψ v φ) := by
  intro F _ _ ψ _ v κ _ w φ
  haveI hOc : CompactSpace (v.adicCompletionIntegers F) :=
    GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  haveI : LocallyCompactSpace (Fv F v) :=
    (isCompact_iff_compactSpace.2 hOc).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem (v.adicCompletionIntegers F)))
  haveI : SecondCountableTopology (Fv F v) := by
    have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    have : TopologicalSpace.SeparableSpace (Fv F v) :=
      ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
        IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
    exact UniformSpace.secondCountable_of_separable (Fv F v)
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hinv : (measV ψ v).IsAddLeftInvariant ∧ SigmaFinite (measV ψ v) := by
    unfold measV
    split_ifs with h
    · haveI := h.choose_spec.1
      exact ⟨inferInstance, inferInstance⟩
    · exact ⟨⟨fun g => by simp⟩, inferInstance⟩
  haveI := hinv.1
  haveI := hinv.2
  have h2 : (⅟2 : Fv F v) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  funext y
  simp only [fourV, schr]
  set χ := GlobalTheory.LatVac.psiAt ψ v
  set μ := Measure.pi fun _ : κ => measV ψ v
  let g : (κ → Fv F v) → ℂ := fun x =>
    χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ x * χ ((x - w.1) ⬝ᵥ y)
  have hg : ∀ x, χ (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ (x + w.1) * χ (x ⬝ᵥ y) = g (x + w.1) := by
    intro x; simp only [g, add_sub_cancel_right]
  simp_rw [hg]
  rw [integral_add_right_eq_self g w.1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [g]
  have key : (x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) + (x - w.1) ⬝ᵥ y =
      y ⬝ᵥ (-w.1) + ⅟(2 : Fv F v) * (w.2 ⬝ᵥ (-w.1)) + x ⬝ᵥ (y + w.2) := by
    simp only [sub_dotProduct, dotProduct_add, dotProduct_neg]
    rw [dotProduct_comm y w.1, dotProduct_comm w.2 w.1]
    linear_combination (w.1 ⬝ᵥ w.2) * h2
  calc χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ x * χ ((x - w.1) ⬝ᵥ y)
      = φ x * (χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * χ ((x - w.1) ⬝ᵥ y)) := by ring
    _ = φ x * χ (y ⬝ᵥ (-w.1) + ⅟(2 : Fv F v) * (w.2 ⬝ᵥ (-w.1)) + x ⬝ᵥ (y + w.2)) := by
      rw [← AddChar.map_add_eq_mul, key]
    _ = _ := by rw [AddChar.map_add_eq_mul]; ring

end GlobalTheory.WeylFour
