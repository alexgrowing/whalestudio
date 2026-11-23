import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCompHomogeneousIsHomogeneousStatement
open IsLocalRing

namespace GlobalTheory

theorem c_one_of_finite_extension : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], (∀ (n d : ℕ) (f : MvPolynomial (Fin n) K), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0) → (∀ (n d : ℕ) (f : MvPolynomial (Fin n) L), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → L, x ≠ 0 ∧ MvPolynomial.eval x f = 0) := by
  intro K L _ _ _ _ hK n d f hf hd hdn
  obtain ⟨F, hFh, hFe⟩ := GlobalTheory.T.exists_isHomogeneous_eval_eq_norm K L n d f hf
  have hm0 : 0 < Module.finrank K L := Module.finrank_pos
  let e : Fin n × Fin (Module.finrank K L) ≃ Fin (n * Module.finrank K L) := finProdFinEquiv
  have hG : (MvPolynomial.rename e F).IsHomogeneous (d * Module.finrank K L) := hFh.rename_isHomogeneous
  obtain ⟨z, hz0, hz⟩ := hK (n * Module.finrank K L) (d * Module.finrank K L) (MvPolynomial.rename e F) hG
    (Nat.mul_pos hd hm0) (Nat.mul_lt_mul_of_pos_right hdn hm0)
  set y : Fin n × Fin (Module.finrank K L) → K := z ∘ e with hy
  rw [MvPolynomial.eval_rename] at hz
  have hy0 : y ≠ 0 := by
    intro h
    apply hz0
    funext k
    have := congrFun h (e.symm k)
    simpa [hy] using this
  refine ⟨fun i => ∑ j, algebraMap K L (y (i, j)) * Module.finBasis K L j, ?_, ?_⟩
  · intro hx
    apply hy0
    funext ⟨i, j⟩
    have hi := congrFun hx i
    simp only [Pi.zero_apply] at hi
    have hli := (Module.finBasis K L).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have := hli (fun j => y (i, j)) (by simpa [Algebra.smul_def] using hi) j
    simpa using this
  · have := hFe y
    rw [hz] at this
    exact (Algebra.norm_eq_zero_iff (R := K)).mp this.symm

end GlobalTheory
