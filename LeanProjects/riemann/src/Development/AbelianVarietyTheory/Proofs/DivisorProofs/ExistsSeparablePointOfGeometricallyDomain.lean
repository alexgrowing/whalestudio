import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedAdjoin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSeparablePointOfSeparableClosurePoinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndepOnPowOfIsDomainTensorPurelyInseparablStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAlgHomAdjoinIntegralRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinHomExtendOfDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveElementSeparabilityCertificateStatement

open scoped TensorProduct

namespace GlobalTheory.SepPoint

theorem exists_sepBasis (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    (hB : Algebra.FiniteType k B)
    (hH : ∀ p : ℕ, p.Prime → CharP k p → ∀ s : Finset (FractionRing B),
      LinearIndepOn k _root_.id (s : Set (FractionRing B)) →
        LinearIndepOn k (· ^ p) (s : Set (FractionRing B))) :
    ∃ s : Finset (FractionRing B), IsTranscendenceBasis k ((↑) : s → FractionRing B) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set (FractionRing B)))
        (FractionRing B) := by
  haveI : Algebra.EssFiniteType k B := inferInstance
  haveI : Algebra.EssFiniteType B (FractionRing B) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType k (FractionRing B) := Algebra.EssFiniteType.comp k B _
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField k _
  · haveI : ExpChar k p := .prime hp.out
    exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      p hp.out (hH p hp.out hpk)

theorem core (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : IsTranscendenceBasis k ((↑) : s → F))
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F)
    (B : Subalgebra k F) (hB : B.FG) : Nonempty (B →ₐ[k] SeparableClosure k) := by
  obtain ⟨T, rfl⟩ := hB
  haveI : IsIntegrallyClosed (Algebra.adjoin k (s : Set F)) := isIntegrallyClosed_adjoin k F s hs.1
  obtain ⟨θ, hθ, H, hH0, U, V, hUV, hT⟩ := GlobalTheory.T.exists_primitive_element_separability_certificate k F s hs hsep T
  obtain ⟨ev, hev⟩ := exists_ev k F s hs.1 H hH0
  let R := Algebra.adjoin k (s : Set F)
  let f := minpoly R θ
  let e : R →+* SeparableClosure k := (ev : R →+* SeparableClosure k)
  have hmon : f.Monic := minpoly.monic hθ
  have hsepa : (f.map e).Separable := by
    have h1 := congrArg (Polynomial.map e) hUV
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at h1
    refine ⟨Polynomial.C (e H)⁻¹ * U.map e, Polynomial.C (e H)⁻¹ * V.map e, ?_⟩
    rw [Polynomial.derivative_map, mul_assoc, mul_assoc, ← mul_add, h1, ← Polynomial.C_mul,
      inv_mul_cancel₀ (show e H ≠ 0 from hev), Polynomial.C_1]
  have hdeg : (f.map e).degree ≠ 0 := by
    rw [hmon.degree_map]
    exact (minpoly.degree_pos hθ).ne'
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root _ hdeg hsepa
  have hr' : Polynomial.eval₂ (ev : R →+* SeparableClosure k) r f = 0 := by
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at hr
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_algHom_adjoin_extend_of_isIntegral_root k F (SeparableClosure k) R θ hθ ev r hr'
  have hHS : (H : F) ∈ Algebra.adjoin k (insert θ (R : Set F)) :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ H.2)
  exact GlobalTheory.T.nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero k F (SeparableClosure k) _ ψ ⟨H, hHS⟩
    (by rw [hψ _ H.2 hHS]; exact hev) (T : Set F) hT

theorem exists_sepPoint : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B],
    Algebra.FiniteType k B →
    (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K →
      IsDomain (K ⊗[k] B)) →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  intro k B _ _ _ hB hK
  haveI : IsDomain (k ⊗[k] B) := hK k inferInstance inferInstance
  haveI : IsDomain B := (Algebra.TensorProduct.lid k B).symm.toMulEquiv.isDomain
  obtain ⟨s, hs, hsep⟩ := exists_sepBasis k B hB
    (fun p hp hpk => GlobalTheory.T.linearIndepOn_frob_pow_of_isDomain_tensor_insep k B p hp hpk hK)
  let g : B →ₐ[k] FractionRing B := IsScalarTower.toAlgHom k B (FractionRing B)
  have hfg : g.range.FG := by
    rw [← Algebra.map_top]
    exact hB.out.map g
  obtain ⟨ψ⟩ := core k (FractionRing B) s hs hsep g.range hfg
  exact GlobalTheory.T.exists_finite_separable_point_of_separableClosure_point' k B hB ⟨ψ.comp g.rangeRestrict⟩

end GlobalTheory.SepPoint
