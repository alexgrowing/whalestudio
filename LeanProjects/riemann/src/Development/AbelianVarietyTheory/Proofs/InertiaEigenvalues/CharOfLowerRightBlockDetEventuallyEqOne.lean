import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockType

theorem blockChar_eventually_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ → ∃ U : Set (GL (Fin (r + t)) k), IsOpen U ∧ (1 : GL (Fin (r + t)) k) ∈ U ∧ ∀ g ∈ U, GlobalTheory.BlockType.blockChar χ g = 1 := by
  intro k _ _ _ _ r t χ hχ
  have hval : Topology.IsOpenEmbedding (Units.val : kˣ → k) := IsOpenUnits.isOpenEmbedding_unitsVal
  have hV : IsOpen ((Units.val : kˣ → k) '' (χ.ker : Set kˣ)) := hval.isOpenMap _ hχ
  have hd : Continuous fun g : GL (Fin (r + t)) k =>
      (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det :=
    (Units.continuous_val.matrix_submatrix _ _).matrix_det
  refine ⟨(fun g : GL (Fin (r + t)) k => (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ⁻¹'
      ((Units.val : kˣ → k) '' (χ.ker : Set kˣ)), hV.preimage hd, ?_, ?_⟩
  · refine ⟨1, χ.ker.one_mem, ?_⟩
    simp only [Units.val_one]
    rw [Matrix.submatrix_one _ (Fin.natAdd_injective t r), Matrix.det_one]
  · rintro g ⟨u, hu, he⟩
    rw [blockChar_eq χ g u he, MonoidHom.mem_ker.1 hu, Units.val_one]

end GlobalTheory.BlockType
