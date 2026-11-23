import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsDimX
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Algebra MvPolynomial TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar)

theorem DimX.ringKrullDim_localization_int (B : Type) [CommRing B] [IsDomain B]
    [inst : Algebra ℤ B] [Algebra.FiniteType ℤ B] (hinj : Function.Injective (algebraMap ℤ B)) (t : ℕ)
    (ht : trdeg ℤ B = t) :
    ringKrullDim (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ))) = t := by
  obtain rfl : inst = Ring.toIntAlgebra B := Subsingleton.elim _ _
  let : Algebra B (ℚ ⊗[ℤ] B) := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)
  have hM : M ≤ nonZeroDivisors B := by
    rintro _ ⟨m, hm, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    exact nonZeroDivisors.ne_zero hm (hinj (h.trans (map_zero _).symm))
  have : IsLocalization M (ℚ ⊗[ℤ] B) := IsLocalization.tensorRight _ _
  have : IsDomain (ℚ ⊗[ℤ] B) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM

  have hBL : Function.Injective (algebraMap B (ℚ ⊗[ℤ] B)) := IsLocalization.injective _ hM
  have : FaithfulSMul B (ℚ ⊗[ℤ] B) := (faithfulSMul_iff_algebraMap_injective _ _).2 hBL
  have : FaithfulSMul ℤ B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : FaithfulSMul ℤ ℚ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ℤ ℚ).injective_int
  have : FaithfulSMul ℚ (ℚ ⊗[ℤ] B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ℚ (ℚ ⊗[ℤ] B)).injective
  have := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (ℚ ⊗[ℤ] B))
    ((algebraMap B (ℚ ⊗[ℤ] B)).comp (algebraMap ℤ B)))
  have := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (ℚ ⊗[ℤ] B))
    ((algebraMap ℚ (ℚ ⊗[ℤ] B)).comp (algebraMap ℤ ℚ)))
  have : Algebra.IsAlgebraic B (ℚ ⊗[ℤ] B) := IsLocalization.isAlgebraic _ M
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have h1 := trdeg_add_eq ℤ B (A := ℚ ⊗[ℤ] B)
  have h2 := trdeg_add_eq ℤ ℚ (A := ℚ ⊗[ℤ] B)
  rw [trdeg_eq_zero (R := B) (A := ℚ ⊗[ℤ] B), add_zero] at h1
  rw [trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add] at h2
  have htL : trdeg ℚ (ℚ ⊗[ℤ] B) = t := by rw [h2, ← h1, ht]

  rw [← ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field (K := ℚ) (A := ℚ ⊗[ℤ] B) t htL]
  exact ringKrullDim_eq_of_ringEquiv
    (IsLocalization.algEquiv M (Localization M) (ℚ ⊗[ℤ] B)).toRingEquiv

theorem DimX.proof : DimX.Statement := by
  intro K _ ι _ P n hP
  obtain ⟨-, ⟨hPp, -, -⟩, hhor, hdim⟩ := hP
  have := hPp

  have hinj : Function.Injective (algebraMap ℤ (MRing ι ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    have hm' : m ∈ P.comap (C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, ← hm]
      exact congrArg (fun f : ℤ →+* MRing ι ⧸ P => f m)
        (RingHom.ext_int ((Ideal.Quotient.mk P).comp C) (algebraMap ℤ (MRing ι ⧸ P)))
    rw [hhor, Ideal.mem_bot] at hm'
    exact hm'

  have : Algebra.FiniteType ℤ (MRing ι ⧸ P) :=
    .of_surjective (Ideal.Quotient.mkₐ ℤ P) (Ideal.Quotient.mkₐ_surjective ℤ P)
  have hfin : trdeg ℤ (MRing ι ⧸ P) < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp hfin
  have hB := IntDomainDim.proof (MRing ι ⧸ P) hinj
  rw [ht, Cardinal.toENat_nat, hdim] at hB
  have htn : t = n + Fintype.card K := by
    have h1 : ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) = ((t + 1 : ℕ) : WithBot ℕ∞) := by
      exact_mod_cast hB
    have h2 : n + 1 + Fintype.card K = t + 1 := by exact_mod_cast h1
    omega
  rw [← htn]
  exact DimX.ringKrullDim_localization_int (MRing ι ⧸ P) hinj t ht

end GroundTheory.Heights₂.Heights
