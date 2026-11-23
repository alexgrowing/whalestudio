import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAdjoints

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR MvPolynomial

namespace GlobalTheory.HoweR

theorem adjZ_Eab_of_isLeft {p q : ℕ} {a b : Ix p q} (h : a.isLeft = b.isLeft) :
    adjZ (Eab a b) = Eab b a := by
  have hs : sameBlock a b := by
    rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]
  ext i j
  rw [GlobalTheory.FockAdj.adjZ_apply]
  simp only [Eab, Matrix.single_apply]
  by_cases e : a = j ∧ b = i
  · obtain ⟨rfl, rfl⟩ := e
    simp [hs]
  · have e' : ¬ (b = i ∧ a = j) := fun ⟨h1, h2⟩ => e ⟨h2, h1⟩
    simp [e, e']

theorem isKC_Eab_of_isLeft {p q : ℕ} {a b : Ix p q} (h : a.isLeft = b.isLeft) : IsKC (Eab a b) := by
  intro i j hij
  simp only [Eab, Matrix.single_apply]
  rw [if_neg]
  rintro ⟨rfl, rfl⟩
  apply hij
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem fock_locU : ∀ P Q R S : ℕ, LocU (fun a : Ix R S => a.isLeft) (units (fockAct2 P Q R S)) := by
  intro P Q R S t
  classical
  obtain ⟨ι, hι, hinj⟩ := GlobalTheory.FischerParts.exists_fockIP (Ln P Q R S)
  refine ⟨restrictTotalDegree (Ln P Q R S) ℂ (t.sup totalDegree), fun x hx => ?_, ?_⟩
  · rw [mem_restrictTotalDegree]
    exact Finset.le_sup hx
  refine ⟨inferInstance, fun a b hab u hu => ?_, ((innerₛₗ ℂ).comp ι).compl₂ ι, fun x _ y _ => ?_,
    fun x _ hx => ?_, fun a b hab x _ y _ => ?_⟩
  · exact GlobalTheory.DegKeep.stable_restrict _ (Eab a b) (isKC_Eab_of_isLeft hab) u hu
  · simp [inner_conj_symm]
  · have hx' : ι x ≠ 0 := fun h0 => hx (hinj (h0.trans (map_zero ι).symm))
    have := (re_inner_self_pos (𝕜 := ℂ)).2 hx'
    simpa using this
  · have := (GlobalTheory.FockAdj.fock_adjoints P Q R S _ ι hι).2.2 (Eab a b) x y
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, innerₛₗ_apply_apply, units]
    rw [this, adjZ_Eab_of_isLeft hab]

end GlobalTheory.HoweR
