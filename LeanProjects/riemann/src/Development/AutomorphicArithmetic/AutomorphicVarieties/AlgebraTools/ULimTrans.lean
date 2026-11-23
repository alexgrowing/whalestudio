import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimKer

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.trans_ker :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ), F ≤ atTop → ∀ (I : ℕ → Ideal R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (a b : Ideal R), a.FG → Antitone I → ∀ h : b ≤ a,
      Function.Surjective (ULim.map F (I := fun j => b ⊔ I j) (I' := fun j => a ⊔ I j) (M := M) (fun _ => sup_le_sup_right h _) fun _ => LinearMap.id) ∧
      LinearMap.ker (ULim.map F (I := fun j => b ⊔ I j) (I' := fun j => a ⊔ I j) (M := M) (fun _ => sup_le_sup_right h _) fun _ => LinearMap.id) = a • ⊤ ∧
      (a • ⊤ : Submodule R (ULim F (fun j => a ⊔ I j) M)) = ⊥ := by
  intro R _ F hF I M _ _ a b ha hI h
  have hI1 : Antitone fun j => b ⊔ I j := fun i j hij => sup_le_sup_left (hI hij) b
  have hI2 : Antitone fun j => a ⊔ I j := fun i j hij => sup_le_sup_left (hI hij) a
  have e1 : ∀ j, a ⊔ (b ⊔ I j) = a ⊔ I j := fun j => by rw [← sup_assoc, sup_eq_left.mpr h]
  have e2 : ∀ j, a ⊔ (a ⊔ I j) = a ⊔ I j := fun j => by rw [← sup_assoc, sup_idem]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F (fun j => a ⊔ I j) M y
    exact ⟨ULim.mk F (fun j => b ⊔ I j) M p, by rw [ULim.map_mk]; rfl⟩
  · ext x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F (fun j => b ⊔ I j) M x
    rw [LinearMap.mem_ker, ULim.map_mk, ULim.mk_eq_zero, ULim.mem_smul_top_iff R F hF _ M a ha hI1]
    simp only [LinearMap.id_apply, e1]
  · refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F (fun j => a ⊔ I j) M x
    rw [ULim.mem_smul_top_iff R F hF _ M a ha hI2] at hx
    rw [Submodule.mem_bot, ULim.mk_eq_zero]
    simpa only [e2] using hx
