import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.TorsorTrace

theorem injective_trace_galoisData : ∀ (F D : Type) [CommRing F] [CommRing D] [Algebra F D] (q : ℕ) [NeZero q]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[F] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor F D q act →
    Function.Injective (algebraMap F D) ∧
    (∃ τ : D →ₗ[F] F, ∀ d : D, algebraMap F D (τ d) = ∑ g, act g d) ∧
    ∃ (n : ℕ) (x y : Fin n → D), ∀ g, ∑ i, x i * act g (y i) = if g = 1 then 1 else 0 := by
  intro F D _ _ _ q _ act h
  obtain ⟨_, _, hff, hbij⟩ := h
  have hinj : Function.Injective (algebraMap F D) := FaithfulSMul.algebraMap_injective F D
  refine ⟨hinj, ?_, ?_⟩
  · have hex : ∀ d : D, ∃ c : F, algebraMap F D c = ∑ g, act g d := by
      intro d
      have hfix : ∀ k, act k (∑ g, act g d) = ∑ g, act g d := by
        intro k
        rw [map_sum]
        refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ ?_
        intro g
        simp [map_mul]
      have h1 : (∑ g, act g d) ⊗ₜ[F] (1 : D) = (1 : D) ⊗ₜ[F] (∑ g, act g d) := by
        apply hbij.1
        rw [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul,
          map_one, map_one, mul_one, one_mul]
        funext k
        exact (hfix k).symm
      have := (Algebra.IsEffective.of_faithfullyFlat F D (∑ g, act g d)).1 (by
        rw [Algebra.TensorProduct.includeLeftSubRight_apply, h1, sub_self])
      obtain ⟨c, hc⟩ := this
      exact ⟨c, hc⟩
    choose t ht using hex
    refine ⟨{ toFun := t, map_add' := ?_, map_smul' := ?_ }, ht⟩
    · intro a b
      apply hinj
      simp [ht, Finset.sum_add_distrib]
    · intro a b
      apply hinj
      rw [RingHom.id_apply, smul_eq_mul, map_mul, ht, ht, ← Algebra.smul_def, Finset.smul_sum]
      simp
  · obtain ⟨z, hz⟩ := hbij.2 (fun g => if g = 1 then 1 else 0)
    obtain ⟨n, x, y, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
    refine ⟨n, x, y, fun g => ?_⟩
    have := congrFun hz g
    rw [map_sum, Finset.sum_apply] at this
    exact this

end GlobalTheory.TorsorTrace
