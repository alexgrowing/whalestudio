import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.LeftTranslate
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ArchSliceUAction
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.HasModerateGrowthZero
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Translation
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.SmoothKZ
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStructure

open NumberField IsDedekindDomain Topology Filter Set MeasureTheory
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction

theorem archPart_infEmb (a : archGroup K n) : archPart (infEmb K n a) = a := by
  simp only [archPart, prodEquiv_infEmb, ContinuousMulEquiv.apply_symm_apply]

theorem archCompact_eq_image :
    (archCompact K n : Set (archGroup K n)) =
      archPart '' (maxCompact (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) := by
  ext a
  constructor
  · intro ha
    exact ⟨infEmb K n a, ha, archPart_infEmb a⟩
  · rintro ⟨k, hk, rfl⟩
    exact archPart_mem_archCompact hk

variable (K n) in

theorem isCompact_archCompact : IsCompact (archCompact K n : Set (archGroup K n)) := by
  rw [archCompact_eq_image]
  exact isCompact_maxCompact.image ((archEquiv K n).continuous.comp
    (continuous_fst.comp (AdelicGLn.prodEquiv K n).continuous))

theorem isArchSmooth_one : IsArchSmooth (1 : AdelicGLn.AdelicGL K n → ℂ) := fun _ => by
  letI := (isExpLieAlgebra K n).chartedSpace
  exact contMDiff_const

def oneSmooth : archSmooth K n := ⟨1, isArchSmooth_one⟩

theorem unipMeasure_unipFundamentalDomain (r : ℕ) :
    unipMeasure K n r (unipFundamentalDomain K n r) = 1 := by
  rw [unipMeasure, unipFundamentalDomain, Measure.pi_pi]
  simp [GroundTheory.Global.adeleMeasure_fundamentalSet]

end AutomorphicForm

end

end GroundTheory.Automorphic
