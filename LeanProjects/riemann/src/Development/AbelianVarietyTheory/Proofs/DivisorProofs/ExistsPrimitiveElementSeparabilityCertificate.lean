import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedAdjoin

open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

namespace GlobalTheory.SepPoint

theorem exists_clear_poly {k F : Type} [Field k] [Field F] [Algebra k F] (s : Set F)
    (p : (IntermediateField.adjoin k s)[X]) :
    ∃ q : (Algebra.adjoin k s)[X], ∃ b : Algebra.adjoin k s, b ≠ 0 ∧
      q.map (algebraMap (Algebra.adjoin k s) (IntermediateField.adjoin k s)) =
        C (algebraMap (Algebra.adjoin k s) (IntermediateField.adjoin k s) b) * p := by
  obtain ⟨b, hb, h⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors (Algebra.adjoin k s)) p
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors (Algebra.adjoin k s)) p, b,
    nonZeroDivisors.ne_zero hb, ?_⟩
  rw [h, ← IsScalarTower.algebraMap_smul (IntermediateField.adjoin k s) b p, Polynomial.smul_eq_C_mul]

theorem aeval_mem_adjoin_insert {k F : Type} [Field k] [Field F] [Algebra k F]
    (R : Subalgebra k F) (θ : F) (g : R[X]) :
    aeval θ g ∈ Algebra.adjoin k (insert θ (R : Set F)) := by
  rw [aeval_eq_sum_range]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (g.coeff i).2))
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) _)

theorem exists_common_mul_mem {k F : Type} [Field k] [Field F] [Algebra k F]
    (R S : Subalgebra k F) (hRS : R ≤ S) (T : Finset F)
    (h : ∀ x ∈ T, ∃ b : R, b ≠ 0 ∧ (b : F) * x ∈ S) :
    ∃ B : R, B ≠ 0 ∧ ∀ x ∈ T, (B : F) * x ∈ S := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a T ha ih =>
    obtain ⟨B, hB, hBT⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
    obtain ⟨b, hb, hba⟩ := h a (Finset.mem_insert_self a T)
    refine ⟨b * B, mul_ne_zero hb hB, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · have : ((b * B : R) : F) * x = (B : F) * ((b : F) * x) := by push_cast; ring
      rw [this]; exact S.mul_mem (hRS B.2) hba
    · have : ((b * B : R) : F) * x = (b : F) * ((B : F) * x) := by push_cast; ring
      rw [this]; exact S.mul_mem (hRS b.2) (hBT x hx)

end GlobalTheory.SepPoint

namespace GlobalTheory.SepPoint

theorem exists_primitive_sep_certificate (k F : Type) [Field k] [Field F] [Algebra k F]
    (s : Finset F) (hs : IsTranscendenceBasis k ((↑) : s → F))
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F) (T : Finset F) :
    ∃ θ : F, IsIntegral (Algebra.adjoin k (s : Set F)) θ ∧
      ∃ H : Algebra.adjoin k (s : Set F), H ≠ 0 ∧
        ∃ U V : Polynomial (Algebra.adjoin k (s : Set F)),
          U * minpoly (Algebra.adjoin k (s : Set F)) θ +
              V * Polynomial.derivative (minpoly (Algebra.adjoin k (s : Set F)) θ) =
            Polynomial.C H ∧
          ∀ x ∈ T, (H : F) * x ∈
            Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)) := by
  classical
  haveI hIC := isIntegrallyClosed_adjoin k F s hs.1
  have hr : Set.range ((↑) : s → F) = (s : Set F) := Subtype.range_coe
  have halg : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set F)) F := by
    have := hs.isAlgebraic
    rw [hr] at this
    exact this

  let E := IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) (T : Set F)
  haveI : FiniteDimensional (IntermediateField.adjoin k (s : Set F)) E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsSeparable.isIntegral _ x
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) E :=
    Algebra.isSeparable_tower_bot_of_isSeparable _ E F
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (IntermediateField.adjoin k (s : Set F)) E
  have hE : E = IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) {(α : F)} := by
    rw [← IntermediateField.lift_adjoin_simple, hα, IntermediateField.lift_top]

  obtain ⟨c, hc, hcint⟩ := IsAlgebraic.exists_integral_multiple (halg.isAlgebraic (α : F))
  set θ : F := c • (α : F) with hθdef
  refine ⟨θ, hcint, ?_⟩

  have hmin : minpoly (IntermediateField.adjoin k (s : Set F)) θ =
      (minpoly (Algebra.adjoin k (s : Set F)) θ).map
        (algebraMap (Algebra.adjoin k (s : Set F)) (IntermediateField.adjoin k (s : Set F))) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' _ hcint
  have hsepθ : (minpoly (IntermediateField.adjoin k (s : Set F)) θ).Separable :=
    Algebra.IsSeparable.isSeparable _ θ
  obtain ⟨u, v, huv⟩ := hsepθ
  obtain ⟨u', b₁, hb₁, hu'⟩ := exists_clear_poly (k := k) (s : Set F) u
  obtain ⟨v', b₂, hb₂, hv'⟩ := exists_clear_poly (k := k) (s : Set F) v

  have hden : ∀ x ∈ T, ∃ b : Algebra.adjoin k (s : Set F), b ≠ 0 ∧ (b : F) * x ∈
      Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)) := by
    intro x hx
    have hxE : x ∈ E := IntermediateField.subset_adjoin _ _ hx
    rw [hE] at hxE
    have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
    have hcmem : (c : F) ∈ IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) {θ} :=
      IntermediateField.algebraMap_mem _
        (algebraMap (Algebra.adjoin k (s : Set F)) (IntermediateField.adjoin k (s : Set F)) c)
    have hαmem : (α : F) ∈ IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) {θ} := by
      have : (α : F) = (c : F)⁻¹ * θ := by
        show (α : F) = (c : F)⁻¹ * ((c : F) * (α : F))
        rw [← mul_assoc, inv_mul_cancel₀ hcF, one_mul]
      rw [this]
      exact mul_mem (inv_mem hcmem) (IntermediateField.mem_adjoin_simple_self _ _)
    have hxθ := IntermediateField.adjoin_simple_le_iff.mpr hαmem hxE
    have hθint : IsIntegral (IntermediateField.adjoin k (s : Set F)) θ :=
      Algebra.IsSeparable.isIntegral _ θ
    have hxθ' : x ∈ (IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) {θ}).toSubalgebra :=
      hxθ
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hxθ'
    obtain ⟨g, hg⟩ := hxθ'
    obtain ⟨q, b, hb, hq⟩ := exists_clear_poly (k := k) (s : Set F) g
    refine ⟨b, hb, ?_⟩
    have : (b : F) * x = aeval θ q := by
      rw [← hg, ← Polynomial.aeval_map_algebraMap (IntermediateField.adjoin k (s : Set F)) θ q, hq,
        Polynomial.aeval_mul, Polynomial.aeval_C]
      rfl
    rw [this]
    exact aeval_mem_adjoin_insert _ θ q
  obtain ⟨B, hB, hBT⟩ := exists_common_mul_mem (Algebra.adjoin k (s : Set F))
    (Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)))
    (fun y hy => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hy)) T hden
  refine ⟨b₁ * b₂ * B, mul_ne_zero (mul_ne_zero hb₁ hb₂) hB, C (b₂ * B) * u', C (b₁ * B) * v', ?_, ?_⟩
  · apply Polynomial.map_injective
      (algebraMap (Algebra.adjoin k (s : Set F)) (IntermediateField.adjoin k (s : Set F)))
      (IsFractionRing.injective _ _)
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← Polynomial.derivative_map,
      ← hmin, hu', hv', map_mul]
    linear_combination (C (algebraMap _ (IntermediateField.adjoin k (s : Set F)) b₁) *
      C (algebraMap _ (IntermediateField.adjoin k (s : Set F)) b₂) *
      C (algebraMap _ (IntermediateField.adjoin k (s : Set F)) B)) * huv
  · intro x hx
    have : ((b₁ * b₂ * B : Algebra.adjoin k (s : Set F)) : F) * x =
        ((b₁ * b₂ : Algebra.adjoin k (s : Set F)) : F) * ((B : F) * x) := by push_cast; ring
    rw [this]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (b₁ * b₂).2))
      (hBT x hx)

end GlobalTheory.SepPoint
