import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral
import Formalism.PadicSubsetSums.StableGradedCounts.TWCentralIdempotentIntegral

namespace Formalism.IrreducibleCountingLemmas.TW

theorem asAlgebraHom_apply_eq_sum {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (x : MonoidAlgebra K G) (v : V) :
    ρ.asAlgebraHom x v = ∑ g ∈ x.coeff.support, x.coeff g • ρ g v := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum,
    LinearMap.sum_apply]
  rfl

theorem truncation_operator_holds : CutOperator := by
  intro O K _ _ _ _ _ _ _ G _ _ V _ _ _ _ ρ Msup U ψU e hM he hc v hv hψ
  have hcomm : ∀ (g : G) (x : MonoidAlgebra K G) (w : V), (∀ y, x * y = y * x) →
      ρ g (ρ.asAlgebraHom x w) = ρ.asAlgebraHom x (ρ g w) := by
    intro g x w hx
    rw [← Representation.asAlgebraHom_single_one ρ g, ← Module.End.mul_apply, ← map_mul,
      ← Module.End.mul_apply, ← map_mul, hx]
  have hcA : ∀ y : MonoidAlgebra K G,
      ((Fintype.card G : K) • e) * y = y * ((Fintype.card G : K) • e) := by
    intro y
    rw [smul_mul_assoc, mul_smul_comm, hc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [asAlgebraHom_apply_eq_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    have hint : IsIntegral ℤ ((Fintype.card G : K) * e.coeff g) :=
      central_idempotent_integral_twist K G e he hc g
    have hintO : IsIntegral O ((Fintype.card G : K) * e.coeff g) := hint.tower_top
    obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.1 hintO
    have : ((Fintype.card G : K) • e).coeff g = algebraMap O K o := by
      rw [ho, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    rw [this, algebraMap_smul]
    exact Msup.smul_mem o (hM g v hv)
  · intro u
    rw [hcomm _ _ _ hcA, hψ u, map_smul]
  · rw [← Module.End.mul_apply, ← map_mul, mul_smul_comm, he]
  · intro hev
    rw [map_smul, LinearMap.smul_apply, hev]
  · intro T hT
    rw [asAlgebraHom_apply_eq_sum, asAlgebraHom_apply_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, hT]

end Formalism.IrreducibleCountingLemmas.TW
