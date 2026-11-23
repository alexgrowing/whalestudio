import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import GroundTheory.LocalFields.FiniteExtension
import GroundTheory.AutomorphicForms.HermitianClassification
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NegOneMemNormOfValuationEqStatement

open scoped TensorProduct

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.NormSign

theorem exists_valuativeRel_of_normed : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F],
    ∃ _ : ValuativeRel F, IsNonarchimedeanLocalField F ∧ ∀ x y : F, x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  intro F _ _ _
  letI rel : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  have hc : (NormedField.valuation (K := F)).Compatible := Valuation.Compatible.ofValuation _
  refine ⟨rel, ?_, fun x y => Iff.rfl⟩
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := inferInstance, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := F))
      (fun {s} => (NormedField.toValued (K := F)).is_topological_valuation s)
  · rw [ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := F))]
    infer_instance

theorem norm_one_tmul {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L] [Algebra R L]
    [FiniteDimensional R L] (x : L) :
    Algebra.norm B ((1 : B) ⊗ₜ[R] x) = algebraMap R B (Algebra.norm R x) := by
  have h : Algebra.lmul B (B ⊗[R] L) ((1 : B) ⊗ₜ[R] x) = (Algebra.lmul R L x).baseChange B := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b z
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.norm_apply, h, LinearMap.det_baseChange, Algebra.norm_apply]

theorem norm_algebraMap_of_isPushout : ∀ (F E K L : Type) [Field F] [Field E] [Field K] [CommRing L] [Algebra F E] [Algebra F K] [Algebra F L]
    [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L] [FiniteDimensional F E],
    Algebra.IsPushout F E K L → ∀ z : E, Algebra.norm K (algebraMap E L z) = algebraMap F K (Algebra.norm F z) := by
  intro F E K L _ _ _ _ _ _ _ _ _ _ _ _ h z
  haveI := h.symm
  have he : Algebra.IsPushout.equiv F K E L ((1 : K) ⊗ₜ[F] z) = algebraMap E L z := by
    simp [Algebra.IsPushout.equiv_tmul]
  rw [← he, Algebra.norm_eq_of_algEquiv, norm_one_tmul]

theorem mul_norm_of_not_norm (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] [Field L] [Algebra K L] (h2 : Module.finrank K L = 2)
    (s t : Kˣ) (hs : ¬ ∃ y : L, Algebra.norm K y = s) (ht : ¬ ∃ y : L, Algebra.norm K y = t) :
    ∃ y : L, Algebra.norm K y = ((s * t : Kˣ) : K) := by
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have hN := GroundTheory.Automorphic.natCard_quotient_range_normUnits_eq_two (F := K) (E := L)
  have ht' : t ∉ (GroundTheory.LocalField.normUnits K L).range := fun h =>
    ht ((GroundTheory.Automorphic.mem_range_normUnits_iff t).1 h)
  rcases GroundTheory.Automorphic.mem_or_mul_inv_mem_of_natCard_eq_two hN ht' s with h | h
  · exact absurd ((GroundTheory.Automorphic.mem_range_normUnits_iff s).1 h) hs
  · obtain ⟨z, hz⟩ := (GroundTheory.Automorphic.mem_range_normUnits_iff _).1 h
    refine ⟨z * algebraMap K L (t : K), ?_⟩
    rw [map_mul, hz, Algebra.norm_algebraMap, h2]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    have := t.ne_zero
    field_simp

theorem norms_of_isField {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) :
    A.NL 0 = 0 ∧
    (∀ s t : A.Kˣ, (¬ ∃ y, A.NL y = s) → (¬ ∃ y, A.NL y = t) → ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K)) ∧
      ∃ y, A.NL y = ((-1 : A.Kˣ) : A.K) := by
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  haveI := hU.ultraF
  haveI := hU.ultraE
  haveI := hU.lcF
  haveI := hU.lcE
  haveI := hU.charZero
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hU.finrank_eq
  have hKL : Module.finrank A.K A.L = 2 := by
    haveI := A.push.symm
    rw [← (Algebra.IsPushout.equiv F A.K E A.L).toLinearEquiv.finrank_eq, Module.finrank_baseChange,
      hU.finrank_eq]
  haveI : CharZero A.K := charZero_of_injective_algebraMap (algebraMap F A.K).injective
  obtain ⟨vF, hFloc, hFv⟩ := exists_valuativeRel_of_normed F
  refine ⟨?_, ?_⟩
  · haveI : FiniteDimensional A.K A.L := Module.finite_of_finrank_eq_succ hKL
    exact Algebra.norm_zero (R := A.K) (S := A.L)
  constructor
  · intro s t hs ht
    obtain ⟨vK, tK, hKloc, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension F A.K
    exact @mul_norm_of_not_norm A.K A.L _ vK tK hKloc _ _ _ hKL s t hs ht
  · obtain ⟨vE, hEloc, hEv⟩ := exists_valuativeRel_of_normed E
    haveI : ValuativeExtension F E := ⟨fun a b => by rw [hEv, hFv, norm_algebraMap', norm_algebraMap']⟩
    obtain ⟨z, hz⟩ := GlobalTheory.T.exists_norm_eq_neg_one_of_unramified_values F E (fun y => by
      obtain ⟨x, hx⟩ := hU.unram y
      exact ⟨x, by rw [hEv, norm_algebraMap', hx], by rw [hEv, norm_algebraMap', hx]⟩)
    refine ⟨algebraMap E A.L z, ?_⟩
    have := norm_algebraMap_of_isPushout F E A.K A.L A.push z
    simp only [Et.NL, this, hz, map_neg, map_one, Units.val_neg, Units.val_one]

theorem omega_mul_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → (∀ s t : A.Kˣ, ω ((s * t : A.Kˣ) : A.K) = ω s * ω t) ∧ ω ((-1 : A.Kˣ) : A.K) = 1 := by
  classical
  intro F E _ _ _ _ _ A ψ x μ ω h
  obtain ⟨hK, hL, -, -, hω⟩ := h
  obtain ⟨hzero, hprod, hneg⟩ := norms_of_isField A hK hL
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  have hmul : ∀ s t : A.Kˣ, (∃ y, A.NL y = s) → (∃ y, A.NL y = t) → ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K) := by
    rintro s t ⟨y, hy⟩ ⟨y', hy'⟩
    exact ⟨y * y', by simp only [Et.NL] at hy hy' ⊢; rw [map_mul, hy, hy', Units.val_mul]⟩
  have hdiv : ∀ s t : A.Kˣ, (∃ y, A.NL y = s) → (∃ y, A.NL y = ((s * t : A.Kˣ) : A.K)) → ∃ y, A.NL y = t := by
    rintro s t ⟨y, hy⟩ ⟨y', hy'⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [hzero] at hy
      exact s.ne_zero hy.symm
    refine ⟨y' * y⁻¹, ?_⟩
    have h1 : A.NL y * A.NL y⁻¹ = 1 := by
      simp only [Et.NL]; rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
    simp only [Et.NL] at hy hy' h1 ⊢
    rw [map_mul, hy', Units.val_mul]
    rw [hy] at h1
    calc (s : A.K) * t * (Algebra.norm A.K) y⁻¹ = t * ((s : A.K) * (Algebra.norm A.K) y⁻¹) := by ring
      _ = t := by rw [h1, mul_one]
  have hval : ∀ s : A.Kˣ, ω s = if ∃ y, A.NL y = s then 1 else -1 := by
    intro s
    split_ifs with hs
    · exact (hω s).1 hs
    · exact (hω s).2 hs
  refine ⟨fun s t => ?_, by rw [hval, if_pos hneg]⟩
  rw [hval s, hval t, hval (s * t)]
  by_cases hs : ∃ y, A.NL y = s <;> by_cases ht : ∃ y, A.NL y = t
  · rw [if_pos hs, if_pos ht, if_pos (hmul s t hs ht)]; ring
  · rw [if_pos hs, if_neg ht, if_neg (fun h => ht (hdiv s t hs h))]; ring
  · have hst : ¬ ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K) := fun h => hs (hdiv t s ht (by rwa [mul_comm]))
    rw [if_neg hs, if_pos ht, if_neg hst]; ring
  · rw [if_neg hs, if_neg ht, if_pos (hprod s t hs ht)]; ring

end GlobalTheory.JR.WeilQuad.NormSign
