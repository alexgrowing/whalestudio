import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompactRepField

theorem exists_hom_of_entries_mem {F E Γ : Type} [Field F] [Field E] [Algebra F E] [Group Γ]
    {a : ℕ} (r : Γ →* GL (Fin a) E) (K : IntermediateField F E)
    (h : ∀ g i j, (r g : Matrix (Fin a) (Fin a) E) i j ∈ K) :
    ∃ r₁ : Γ →* GL (Fin a) ↥K, ∀ g i j,
      ((r₁ g : Matrix (Fin a) (Fin a) ↥K) i j : E) = (r g : Matrix (Fin a) (Fin a) E) i j := by
  let m : Γ →* Matrix (Fin a) (Fin a) ↥K :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, h g i j⟩
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  exact ⟨m.toHomUnits, fun g i j => rfl⟩

theorem exists_continuous_model :
    ∀ (D : D7) (l : ℕ) [Fact l.Prime] (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → ∀ L₀ : FinExt l, ∃ (LL' : FinExt l) (_ : L₀.1 ≤ LL'.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1), Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1)) ∧ mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₁ = ρ := by
  intro D l _ a ρ hρ L₀
  obtain ⟨L, hL, h⟩ := exists_finExt_entries_mem l (G D.host.E D.nd.Om) a ρ hρ L₀
  obtain ⟨ρ₁, h₁⟩ := exists_hom_of_entries_mem ρ L.1 h
  refine ⟨L, hL, ρ₁, ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    refine continuous_induced_rng.2 ?_
    exact (hρ.matrix_elem i j).congr fun g => (h₁ g i j).symm
  · refine MonoidHom.ext fun g => Units.ext ?_
    ext i j
    exact h₁ g i j

end GlobalTheory.CompactRepField
