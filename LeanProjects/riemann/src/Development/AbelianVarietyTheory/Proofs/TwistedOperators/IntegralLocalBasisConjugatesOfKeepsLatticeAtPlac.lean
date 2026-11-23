import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.IntKeepConj

theorem mulVec_conj_col {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (π : R →+* S)
    (b : GL (Fin d) S) (A : Matrix (Fin d) (Fin d) R) (z : Fin d → R) (k : Fin d)
    (hz : (fun j => π (z j)) = (b : Matrix (Fin d) (Fin d) S) *ᵥ Pi.single k 1) :
    (((b⁻¹ : GL (Fin d) S) : Matrix (Fin d) (Fin d) S) *ᵥ fun j => π ((A *ᵥ z) j)) =
      fun i => (((b⁻¹ : GL (Fin d) S) : Matrix (Fin d) (Fin d) S) * A.map π *
        (b : Matrix (Fin d) (Fin d) S)) i k := by
  have h1 : (fun j => π ((A *ᵥ z) j)) = A.map π *ᵥ (fun j => π (z j)) := by
    funext j; exact RingHom.map_mulVec π A z j
  rw [h1, hz, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  funext i
  simp [Matrix.mulVec_single]

theorem single_mem {F : Type} [Field F] [NumberField F] (v : Pl F) {d : ℕ} (k i : Fin d) :
    (Pi.single k (1 : Fv F v) : Fin d → Fv F v) i ∈ v.adicCompletionIntegers F := by
  by_cases h : i = k
  · subst h; simp only [Pi.single_eq_same]; exact (v.adicCompletionIntegers F).one_mem
  · rw [Pi.single_eq_of_ne h]; exact (v.adicCompletionIntegers F).zero_mem

end GlobalTheory.IntKeepConj

open GlobalTheory.IntKeepConj in
theorem GlobalTheory.IntKeepConj.conj_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (W : Spc F E d) (v : Pl F) (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
        v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
        v.adicCompletionIntegers F)) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ A : Matrix (Fin d) (Fin d) (AE F E), (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) → (∀ i j, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) ∧ (∀ i j, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) := by
  intro F E _ _ _ _ _ d W v π₁ π₂ b₁ b₂ hchar hsurj A hA
  constructor
  · intro i k
    choose z hzA hz1 hz2 using fun j => hsurj (((b₁ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1) j) 0
    have hzL : z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [hchar]
      refine ⟨?_, ?_, ?_⟩
      · intro u hu; funext j; exact hzA j u hu
      · intro i'
        have e : (fun j => π₁ (z j)) = (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1 := funext hz1
        rw [e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        exact single_mem v k i'
      · intro i'
        have e : (fun j => π₂ (z j)) = 0 := funext hz2
        rw [e, Matrix.mulVec_zero]; exact (v.adicCompletionIntegers F).zero_mem
    have h := ((hchar _).1 (hA z hzL)).2.1 i
    rw [mulVec_conj_col π₁ b₁ A z k (funext hz1)] at h
    exact h
  · intro i k
    choose z hzA hz1 hz2 using fun j => hsurj 0 (((b₂ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1) j)
    have hzL : z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [hchar]
      refine ⟨?_, ?_, ?_⟩
      · intro u hu; funext j; exact hzA j u hu
      · intro i'
        have e : (fun j => π₁ (z j)) = 0 := funext hz1
        rw [e, Matrix.mulVec_zero]; exact (v.adicCompletionIntegers F).zero_mem
      · intro i'
        have e : (fun j => π₂ (z j)) = (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1 := funext hz2
        rw [e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        exact single_mem v k i'
    have h := ((hchar _).1 (hA z hzL)).2.2 i
    rw [mulVec_conj_col π₂ b₂ A z k (funext hz2)] at h
    exact h
