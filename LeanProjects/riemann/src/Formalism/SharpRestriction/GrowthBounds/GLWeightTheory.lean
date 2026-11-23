import Formalism.SharpRestriction.GrowthBounds.RootWeights.MahPadicGeOfDvd
import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemBoundedDegreeExponentsIff
import Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialExpansionCoeffZeroOfDeg
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationBoundDetPowerFactor
import Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivativeValuationBounds
import Formalism.SharpRestriction.GrowthBounds.RootWeights.GenericMatrixEvaluationDet
import Formalism.SharpRestriction.GrowthBounds.RootWeights.FrameChangePreservesMultidegree
import Formalism.SharpRestriction.GrowthBounds.RootWeights.AlgHomFixesSupportedPolynomials
import Formalism.SharpRestriction.GrowthBounds.RootWeights.PositivityConditionHolds
import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionExtremalFormula
import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicLatticeCorollary
import Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedWeightLemmaOfReducibility
import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralPolynomialsEnvelopingStable
import Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedModuleWeightLemmaPartB
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm
import Formalism.SharpRestriction.GrowthBounds.RootWeights.LoweringSpanHighestComponentIntegral
import Formalism.SharpRestriction.GrowthBounds.RootWeights.LinfAdjointLeEllWtHighest
import Formalism.SharpRestriction.GrowthBounds.RootWeights.LatticeTheoremOfAdmitted
import Formalism.SharpRestriction.GrowthBounds.RootWeights.LatticeTheoremSingleRepLinf
import Formalism.SharpRestriction.GrowthBounds.RootWeights.DenominatorLemmaWithoutProjector
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExtremalProjectorOfReducibility

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem exponent_condition_holds (D : Formalism.BasicNotions.D7) : adm3 D := by
  intro p hp m k b hkm hb
  haveI : Fact p.Prime := ⟨hp⟩
  exact padicValNat_choose hkm hb

theorem key_positivity_condition (D : Formalism.BasicNotions.D7) : ArchimedeanSignatureMatching D := by
  intro A _ _ _ σ w hw F G h
  have hp : Prime w := UniqueFactorizationMonoid.irreducible_iff_prime.mp hw
  haveI : (Ideal.span {w}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp

  have key : ∀ H : MvPolynomial σ A,
      C w ∣ H ↔ MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {w})) H = 0 := by
    intro H
    rw [MvPolynomial.C_dvd_iff_dvd_coeff, MvPolynomial.ext_iff]
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
  rw [key] at h
  rw [map_mul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact Or.inl ((key F).mpr h1)
  · exact Or.inr ((key G).mpr h1)

private theorem sub_one_mod_eq_ite (a n : ℕ) (hn : 1 ≤ n) (ha : 1 ≤ a) :
    (a - 1) % n = if 1 ≤ a % n then a % n - 1 else n - 1 := by
  have hdiv := Nat.div_add_mod a n
  have hlt := Nat.mod_lt a (by omega : n > 0)
  generalize a % n = r at hdiv hlt ⊢
  generalize a / n = q at hdiv
  generalize hx : n * q = x at hdiv
  split_ifs with hr
  · have e : a - 1 = (r - 1) + x := by omega
    rw [e, ← hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · have hq : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hx
      omega
    obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    have hx' : x = n * q' + n := by rw [← hx, Nat.mul_succ]
    generalize hy : n * q' = y at hx'
    have e : a - 1 = (n - 1) + y := by omega
    rw [e, ← hy, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem true_derivative_digit_class (D : Formalism.BasicNotions.D7) : TrueDerivativeDigitClass D := by
  classical
  intro R _ σ P hP rho k F hF
  have hF' : ∀ m ∈ F.support, digitOfL P m = rho := fun m hm =>
    (show (↑F.support : Set (σ →₀ ℕ)) ⊆ {m | digitOfL P m = rho} from hF) hm
  rw [F.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [MvPolynomial.pderiv_monomial, DigitClassL, MvPolynomial.monomial_mem_restrictSupport]
  by_cases hmk : m k = 0
  · right
    simp [hmk]
  · left
    have hd := hF' m hm
    show digitOfL P (m - Finsupp.single k 1) = _
    funext j
    have hdj := congrFun hd j
    simp only [digitOfL] at hdj ⊢
    by_cases hjk : j = k
    · subst hjk
      rw [Function.update_self, Finsupp.tsub_apply, Finsupp.single_eq_same,
        sub_one_mod_eq_ite (m j) (P j) (hP j) (Nat.one_le_iff_ne_zero.mpr hmk), hdj]
    · rw [Function.update_of_ne hjk, Finsupp.tsub_apply]
      simp [Ne.symm hjk, hdj]

theorem unit_function_expansion (D : Formalism.BasicNotions.D7) : UnitFunctionExpansion D := mahler_decay_products_of D (fun p hp => hDec_of hp (hdU_proved hp)) (fun p hp => hMul_proved hp)

theorem lemma_five_two_first_holds (D : Formalism.BasicNotions.D7) : FactorialUnitDecomposition D := unit_function_mahler_decay_of D (fun p hp => hDec_of hp (hdU_proved hp)) (fun p hp => hMul_proved hp)
    (fun p hp => hUnit_of hp (hdU_proved hp))

theorem support_coprimality_lemma_holds (D : Formalism.BasicNotions.D7) : ConclusionE D := prvE_of_gl_operators_form_representation D (height_bound_of_weights hSupp_proved hCop_proved)

theorem section_five_lemmas_hold (D : Formalism.BasicNotions.D7) : UnitProductLemmas D := ⟨unit_function_expansion D, show FactorialUnitDecomposition D ∧ DegreeTruncationLemma D from ⟨lemma_five_two_first_holds D, degree_truncation D⟩⟩

theorem lattice_index_lemma_holds (D : Formalism.BasicNotions.D7) : DerivativeLemmaField D := show DerivativeValuationBound D ∧ DerivativeDigitExpansion D ∧ TrueDerivativeDigitClass D from ⟨derivative_valuation_bound D, derivative_digit_expansion D, true_derivative_digit_class D⟩

theorem valuation_field_of_adm2 (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : ValuationLemmaField D := show ValuationsAdditive D ∧ ShaLengthVersionTwo D from ⟨valuationsAdditive_D7 D, generated_weight_lemma_of_reducibility D h2 (valuationsAdditive_D7 D)⟩

theorem valuation_field (D : Formalism.BasicNotions.D7) : ValuationLemmaField D := valuation_field_of_adm2 D (weight_condition_from_integral_form D)

theorem invariant_projection_sup_norm_denominator (D : Formalism.BasicNotions.D7) : InvariantDenominatorLinftyBound := linf_lemma_without_projector D (weight_condition_from_integral_form D)

theorem invariantProjectionDenominator (D : Formalism.BasicNotions.D7) : InvariantProjectionDenominator := denominator_lemma_without_projector D (weight_condition_from_integral_form D)

theorem nabla_delta_comparison_field (D : Formalism.BasicNotions.D7) : NablaDeltaComparisonField D := integral_form_of_linf_lemma D (weight_condition_from_integral_form D) (invariant_projection_sup_norm_denominator D)

theorem isotypic_projector_theorem_field (D : Formalism.BasicNotions.D7) : IsotypicProjectorTheoremField D := isotypicProjectorTheoremField_of_linfty_bound D (weight_condition_from_integral_form D) (invariant_projection_sup_norm_denominator D)

theorem translate_corollary_field (D : Formalism.BasicNotions.D7) : TranslateCorollaryField D := isotypic_lattice_corollary D (weight_condition_from_integral_form D) (nabla_delta_comparison_field D)

theorem filtered_projector_corollary_field (D : Formalism.BasicNotions.D7) : FilteredProjectorCorollaryField D := polynomial_isotypic_lattice_corollary D (weight_condition_from_integral_form D) (isotypic_projector_theorem_field D)

def InvariantProductFormula : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
      [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ Inv : Module.End (KK O) V, IsInvProj E Inv →
        (∀ π : Module.End (KK O) V, IsWtProj E 0 π → ∀ ord, NormalOrder n ord →
          ∀ T : ℕ, Module.finrank (KK O) V ≤ T → Inv = pp E 0 ord T * π)

theorem invariant_projection_of_product_formula (D : Formalism.BasicNotions.D7) (h : InvariantProductFormula) : InvariantProjectionField D := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv
  exact ⟨h p n' O S hG n V E hE M hM hMQ Inv hInv, invariantProjectionDenominator D p n' O S hG n V E hE M hM hMQ Inv hInv⟩

theorem product_formula_of_extremal_projector (D : Formalism.BasicNotions.D7) (h5 : adm5 D) : InvariantProductFormula := by
  intro p n' O _ _ _ S hG n V _ _ _ _ _ E hE M hM hMQ Inv hInv π hπ ord hord T hT
  haveI := dvr_fraction_field_charZero_prime S hG.prime
  exact invariant_projection_extremal_formula D (weight_condition_from_integral_form D) h5 E hE Inv hInv π hπ ord hord T hT

theorem counting_statement_of_block_form (D : Formalism.BasicNotions.D7) (h : InvariantProductFormula) : Conclusion1 D := show ProjectionTheorems D ∧ ValuationLemmaField D ∧ ConclusionE D ∧ UnitProductLemmas D ∧ DerivativeLemmaField D from
    ⟨show InvariantProjectionField D ∧ NablaDeltaComparisonField D ∧ IsotypicProjectorTheoremField D ∧ TranslateCorollaryField D ∧ FilteredProjectorCorollaryField D from
      ⟨invariant_projection_of_product_formula D h, nabla_delta_comparison_field D, isotypic_projector_theorem_field D, translate_corollary_field D, filtered_projector_corollary_field D⟩,
     valuation_field D, support_coprimality_lemma_holds D, section_five_lemmas_hold D, lattice_index_lemma_holds D⟩

theorem part_one_of_extremal_projector (D : Formalism.BasicNotions.D7) (h5 : adm5 D) : Conclusion1 D := counting_statement_of_block_form D (product_formula_of_extremal_projector D h5)

theorem problem_holds (D : Formalism.BasicNotions.D7) : IntegralityFromMetric D := fun hA => part_one_of_extremal_projector D (show admitted D from hA).2.2.2.2

end Formalism.MainNotions.G.GLWeightTheory
