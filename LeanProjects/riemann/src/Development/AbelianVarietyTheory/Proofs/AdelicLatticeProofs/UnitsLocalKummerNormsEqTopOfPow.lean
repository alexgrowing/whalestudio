import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitNormEqOfAlgHom
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem kNorm_eq_top_of_pow : ∀ (p : ℕ) (F L : Type) [Field F] [Field L] [CharZero L] (φ : F →+* L) (δ : F) (r : L), 0 < p → δ ≠ 0 → r ^ p = φ δ → kNorm p φ δ = ⊤ := by
  intro p F L _ _ _ φ δ r hp hδ hr
  have hφ : φ δ ≠ 0 := (map_ne_zero φ).2 hδ
  have hsep : (X ^ p - C (φ δ) : L[X]).Separable :=
    separable_X_pow_sub_C (φ δ) (Nat.cast_ne_zero.2 hp.ne') hφ
  have hm : (X ^ p - C (φ δ) : L[X]).Monic := monic_X_pow_sub_C _ hp.ne'
  have : IsReduced (AdjoinRoot (X ^ p - C (φ δ) : L[X])) :=
    (Ideal.isRadical_iff_quotient_reduced _).1
      (isRadical_iff_span_singleton.1 hsep.squarefree.isRadical)
  have : Module.Finite L (AdjoinRoot (X ^ p - C (φ δ) : L[X])) :=
    (AdjoinRoot.powerBasis' hm).finite
  let ψ : AdjoinRoot (X ^ p - C (φ δ) : L[X]) →ₐ[L] L :=
    AdjoinRoot.liftAlgHom _ (AlgHom.id L L) r (by simp [hr])
  rw [eq_top_iff]
  intro x _
  rw [mem_kNorm]
  exact GlobalTheory.CNorm.exists_unit_norm_eq_of_algHom L _ ψ (φ (x : F)) ((map_ne_zero φ).2 x.ne_zero)

end GlobalTheory.CNorm
