import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix
open scoped nonZeroDivisors

noncomputable section

namespace KLinesLineDegree

variable {K : Type} [Field K] {n : ℕ}

theorem genIndex_map_of_injective {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G')
    (hf : Function.Injective f) (A B : AddSubgroup G) :
    genIndex (A.map f) (B.map f) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.relIndex_map_map_of_injective _ _ hf]

theorem single_injective (x : Fin n) :
    Function.Injective (AddMonoidHom.single (fun _ : Fin n => K) x) := by
  intro s t h
  simpa using congrFun h x

theorem inter_line (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (x : Fin n) :
    (idealLattice a ⊓ (Submodule.span K
        (Set.range fun _ : Fin 1 => (Pi.single x 1 : Fin n → K))).restrictScalars (𝓞 K)).toAddSubgroup =
      ((a x : Submodule (𝓞 K) K).toAddSubgroup).map (AddMonoidHom.single (fun _ : Fin n => K) x) := by
  ext v
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf, Submodule.restrictScalars_mem,
    Set.range_const, Submodule.mem_span_singleton, AddSubgroup.mem_map, AddMonoidHom.single_apply]
  constructor
  · rintro ⟨hv, t, rfl⟩
    refine ⟨t, ?_, ?_⟩
    · have h := (Submodule.mem_pi.mp hv) x (Set.mem_univ _)
      simpa using h
    · rw [← Pi.single_smul', smul_eq_mul, mul_one]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, t, ?_⟩
    · rw [idealLattice, Submodule.mem_pi]
      intro y _
      by_cases hy : y = x
      · subst hy
        simpa using ht
      · simp only [Pi.single_apply, hy, if_false]
        exact zero_mem _
    · rw [← Pi.single_smul', smul_eq_mul, mul_one]

theorem span_line (x : Fin n) :
    (Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => (Pi.single x 1 : Fin n → K))).toAddSubgroup =
      ((1 : Submodule (𝓞 K) K).toAddSubgroup).map (AddMonoidHom.single (fun _ : Fin n => K) x) := by
  ext v
  simp only [Submodule.mem_toAddSubgroup, Set.range_const, Submodule.mem_span_singleton,
    AddSubgroup.mem_map, Submodule.mem_one, AddMonoidHom.single_apply]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨algebraMap (𝓞 K) K y, ⟨y, rfl⟩, by rw [← Pi.single_smul', Algebra.smul_def, mul_one]⟩
  · rintro ⟨t, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, by rw [← Pi.single_smul', Algebra.smul_def, mul_one]⟩

theorem gram_line (d : (K →+* ℂ) → Fin n → ℝ) (σ : K →+* ℂ) (x : Fin n) :
    (gramAt (diagMetric d σ) σ (fun _ : Fin 1 => (Pi.single x 1 : Fin n → K))).det.re = d σ x := by
  rw [Matrix.det_unique]
  simp [gramAt, diagMetric, embVec, dotProduct, Matrix.mulVec_diagonal, Pi.single_apply]

end KLinesLineDegree

open KLinesLineDegree in

theorem LinesLineDegree.proof : LinesLineDegree.Statement := by
  intro K _ _ n a d x
  unfold subDegree idealIndex
  rw [inter_line, span_line, genIndex_map_of_injective _ (single_injective x)]
  simp only [gram_line]

end

end GroundTheory.Heights₂.Heights
