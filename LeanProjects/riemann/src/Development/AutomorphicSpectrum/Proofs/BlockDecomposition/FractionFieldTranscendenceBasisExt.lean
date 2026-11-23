import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimeDvdNotUnit
set_option backward.isDefEq.respectTransparency false
open MvPolynomial

namespace GlobalTheory.CompanionTheory.TraceJac

theorem det_completed_eq_minor {L : Type*} [Field L] {d m : ℕ} (κ : Fin m ↪ Fin d)
    (E : Fin d → L → L) (τ : Fin d → L) (hE : ∀ k j, E k (τ j) = if k = j then 1 else 0)
    (β : Fin m → L) :
    let e : Fin m ⊕ ↥(Set.range κ)ᶜ ≃ Fin d :=
      (Equiv.sumCongr (Equiv.ofInjective κ κ.injective) (Equiv.refl _)).trans
        (Equiv.Set.sumCompl (Set.range κ))
    (Matrix.of fun k l => E k ((Sum.elim β (fun j : ↥(Set.range κ)ᶜ => τ j)) (e.symm l))).det =
      (Matrix.of fun k l => E (κ k) (β l)).det := by
  classical
  intro e
  have he1 : ∀ i, e (Sum.inl i) = κ i := fun i => by simp [e]
  have he2 : ∀ j : ↥(Set.range κ)ᶜ, e (Sum.inr j) = j := fun j => by simp [e]
  rw [← Matrix.det_submatrix_equiv_self e]
  have hblock : (Matrix.of fun k l =>
      E k ((Sum.elim β (fun j : ↥(Set.range κ)ᶜ => τ j)) (e.symm l))).submatrix e e =
      Matrix.fromBlocks (Matrix.of fun k l => E (κ k) (β l)) 0
        (Matrix.of fun (j : ↥(Set.range κ)ᶜ) l => E j (β l)) 1 := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.symm_apply_apply]
    rcases x with i | j <;> rcases y with i' | j'
    · simp [he1]
    · have hne : κ i ≠ (j' : Fin d) := fun h => j'.2 ⟨i, h⟩
      simp [he1, hE, hne]
    · simp [he2]
    · have : ((j : Fin d) = j') ↔ j = j' := Subtype.ext_iff.symm
      simp [he2, hE, Matrix.one_apply, this]
  rw [hblock, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

theorem trace_minor_mem : ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (A : Type) [CommRing A] [IsDomain A] [Algebra K A] (t : Fin d → A), Function.Injective (MvPolynomial.aeval t : MvPolynomial (Fin d) K →ₐ[K] A) → (∀ a : A, ∃ f g : MvPolynomial (Fin d) K, IsUnit (MvPolynomial.aeval t g) ∧ a * MvPolynomial.aeval t g = MvPolynomial.aeval t f) → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ∀ (F L : Type) [Field F] [Field L] [Algebra A F] [IsFractionRing A F] [Algebra B L] [IsFractionRing B L] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower K B L] (D : Fin d → Derivation K L L), (∀ k j, D k (algebraMap A L (t j)) = if k = j then 1 else 0) → ∀ (m : ℕ) (κ : Fin m ↪ Fin d) (c : B) (b : Fin m → B), ∃ a : A, algebraMap A F a = Algebra.trace F L (algebraMap B L c * (Matrix.of fun k l => D (κ k) (algebraMap B L (b l))).det) := by
  intro K _ _ d A _ _ _ t ht hloc B _ _ _ _ _ _ hB F L _ _ _ _ _ _ _ _ _ _ _ _ D hD m κ c b
  classical
  let e : Fin m ⊕ ↥(Set.range κ)ᶜ ≃ Fin d :=
    (Equiv.sumCongr (Equiv.ofInjective κ κ.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range κ))
  let b' : Fin d → B := fun l =>
    (Sum.elim b (fun j : ↥(Set.range κ)ᶜ => algebraMap A B (t j))) (e.symm l)
  obtain ⟨a, ha⟩ := trace_jacobian_mem K d A t ht hloc B hB F L D hD c b'
  refine ⟨a, ha.trans ?_⟩
  have hdet := det_completed_eq_minor κ (fun k x => D k x) (fun j => algebraMap A L (t j)) hD
    (fun l => algebraMap B L (b l))
  have hmat : (Matrix.of fun k l => D k (algebraMap B L (b' l))) =
      Matrix.of fun k l => D k ((Sum.elim (fun l => algebraMap B L (b l))
        (fun j : ↥(Set.range κ)ᶜ => algebraMap A L (t j))) (e.symm l)) := by
    ext k l
    simp only [Matrix.of_apply, b']
    rcases e.symm l with i | j
    · simp
    · simp [← IsScalarTower.algebraMap_apply A B L]
  rw [hmat]
  exact congrArg (fun x => Algebra.trace F L (algebraMap B L c * x)) hdet

end GlobalTheory.CompanionTheory.TraceJac
