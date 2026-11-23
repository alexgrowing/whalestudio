import Mathlib
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Lattice
import GroundTheory.GlobalFields.LocalAtPlace

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology

noncomputable section

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

def vecCoordsHomeomorph : (ι → R ⊗[K] E) ≃ₜ (ι → κ → R) :=
  Homeomorph.piCongrRight fun _ => tensorCoordsHomeomorph R b

theorem stdLattice_eq_preimage (O : Subring R) :
    stdLattice ι R b O = vecCoordsHomeomorph R b ⁻¹'
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (O : Set R) := by
  ext x
  simp only [stdLattice, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    true_implies, SetLike.mem_coe]
  rfl

theorem isOpen_stdLattice {O : Subring R} (hO : IsOpen (O : Set R)) :
    IsOpen (stdLattice ι R b O) := by
  rw [stdLattice_eq_preimage]
  exact (vecCoordsHomeomorph R b).continuous.isOpen_preimage _
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hO)

theorem isCompact_stdLattice {O : Subring R} (hO : IsCompact (O : Set R)) :
    IsCompact (stdLattice ι R b O) := by
  rw [stdLattice_eq_preimage]
  exact (vecCoordsHomeomorph R b).isCompact_preimage.2
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO)

theorem continuous_unitaryMat_mulVec :
    Continuous fun p : unitaryPoints K E H R × (ι → R ⊗[K] E) => unitaryMat p.1 *ᵥ p.2 := by
  have h1 : Continuous fun p : unitaryPoints K E H R × (ι → R ⊗[K] E) => unitaryMat p.1 :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_fst
  exact h1.matrix_mulVec continuous_snd

section NumberField

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [CommRing E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E] {H : Matrix ι ι E} (b : Basis κ K E)
  (v : HeightOneSpectrum (𝓞 K))

end NumberField

end

end GroundTheory.Automorphic
