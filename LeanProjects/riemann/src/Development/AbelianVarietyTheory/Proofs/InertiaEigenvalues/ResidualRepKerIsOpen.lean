import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem isOpen_ker_map_of_isOpen_ker {Γ A B : Type} [Group Γ] [TopologicalSpace Γ] [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] {n : ℕ} (f : A →+* B) (hf : IsOpen ((RingHom.ker f : Ideal A) : Set A))
    (ρ : Γ →* GL (Fin n) A) (hρ : Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) A))) :
    IsOpen (((Matrix.GeneralLinearGroup.map f).comp ρ).ker : Set Γ) := by
  classical

  let U : Set (Matrix (Fin n) (Fin n) A) :=
    {M | ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) A) i j ∈ RingHom.ker f}
  have hU : IsOpen U := by
    have : U = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) A =>
        M i j - (1 : Matrix (Fin n) (Fin n) A) i j) ⁻¹' ((RingHom.ker f : Ideal A) : Set A) := by
      ext M; simp [U]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hf.preimage ((continuous_id.matrix_elem i j).sub continuous_const)

  have hker : (((Matrix.GeneralLinearGroup.map f).comp ρ).ker : Set Γ) =
      (fun g => ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) A)) ⁻¹' U := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, Set.mem_preimage, U,
      Set.mem_ofPred_eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    rw [Units.ext_iff]
    change f.mapMatrix ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) A) =
      ((1 : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) ↔ _
    rw [Units.val_one, ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hker]
  exact hU.preimage hρ

theorem redF_ker_isOpen (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i))
    (hρ : Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))) :
    IsOpen ((redF D i ρ).ker : Set (G D.host.E D.nd.Om)) := by

  have hk : ((RingHom.ker ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) : Ideal (D.nd.O i)) :
      Set (D.nd.O i)) = (IsLocalRing.maximalIdeal (D.nd.O i) : Set (D.nd.O i)) := by
    ext x
    simp [RingHom.mem_ker, IsLocalRing.residue_eq_zero_iff]
  have hm : IsOpen (IsLocalRing.maximalIdeal (D.nd.O i) : Set (D.nd.O i)) := by
    simpa using (isAdic_iff.mp (D.nd.O_adic i)).1 1
  exact isOpen_ker_map_of_isOpen_ker _ (hk ▸ hm) ρ hρ

end GlobalTheory.TypeLeaf
