import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFunctionFieldFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace FunctionFieldFinite

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

def chartGens (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    Set (FractionRing (MRing ι F ⧸ P)) :=
  Set.range fun v => algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X v)) /
    algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩))

omit [Fintype K] [DecidableEq K] in

theorem range_chartMap (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    (chartMap P u).range = Algebra.adjoin F (chartGens P u) :=
  aeval_range _

theorem homFracDegZero_eq (hD : MChartDehomog.Statement.{u}) (P : Ideal (MRing ι F)) [P.IsPrime]
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    homFracDegZero P = IntermediateField.adjoin F (chartGens P u) := by
  apply le_antisymm
  · unfold homFracDegZero
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨b, f, g, hf, hg, -, rfl⟩
    have hm : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (chartMonomial u b)) ≠ 0 := by
      rw [chartMonomial, map_prod, map_prod]
      refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
      rw [map_pow, map_pow]
      refine pow_ne_zero _ ?_
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
      exact hu k
    have hr : ∀ p, chartMap P u p ∈ IntermediateField.adjoin F (chartGens P u) := fun p =>
      IntermediateField.algebra_adjoin_le_adjoin F _ (by rw [← range_chartMap]; exact ⟨p, rfl⟩)
    have key := div_mem (hr f) (hr g)
    rwa [hD F K ι P u hu f b hf, hD F K ι P u hu g b hg, div_div_div_cancel_right₀ hm] at key
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨v, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨blockWeight ι v, X v, X ⟨v.1, u v.1⟩,
      isWeightedHomogeneous_X _ _ _, isWeightedHomogeneous_X _ _ _, hu v.1, rfl⟩

open IntermediateField.algebraAdjoinAdjoin in

theorem trdeg_homFracDegZero (hD : MChartDehomog.Statement.{u}) (hT : MChartTrdeg.Statement.{u})
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime] (hP : IsMultiHomogIdeal P)
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    Algebra.trdeg F (homFracDegZero P) + Fintype.card K = Algebra.trdeg F (MRing ι F ⧸ P) := by
  rw [← hT F K ι P hP u hu, homFracDegZero_eq hD P u hu,
    GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F)
      (A := Algebra.adjoin F (chartGens P u)), ← range_chartMap]
  exact congrArg (· + _) (Ideal.quotientKerEquivRange (chartMap P u)).trdeg_eq.symm

theorem relDim_eq_trdeg (hD : MChartDehomog.Statement.{u}) (hT : MChartTrdeg.Statement.{u})
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime] (hP : IsMultiProjPrime P) :
    ∃ n : ℕ, Algebra.trdeg F (homFracDegZero P) = n ∧
      relDim P = (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  choose u hu using hP.relevant
  have h1 := trdeg_homFracDegZero hD hT P hP.multiHomog u hu
  obtain ⟨m, hdim, htr⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := F) (A := MRing ι F ⧸ P)
  rw [htr] at h1
  have hlt : Algebra.trdeg F (homFracDegZero P) < Cardinal.aleph0 :=
    lt_of_le_of_lt (h1 ▸ self_le_add_right _ _) (Cardinal.natCast_lt_aleph0 (n := m))
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hn] at h1
  have hnm : n + Fintype.card K = m := by exact_mod_cast h1
  refine ⟨n, hn, ?_⟩
  have hz : (((n + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) = n := by push_cast; ring
  rw [relDim, hdim, ← hnm, ← hz]
  rfl

end FunctionFieldFinite

open FunctionFieldFinite in

theorem FunctionFieldFinite.proof (hD : MChartDehomog.Statement.{u})
    (hT : MChartTrdeg.Statement.{u}) : FunctionFieldFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' hrel
  have := hP'.isPrime
  have hP := isMultiProjPrime_contractPrime j ι' hP'
  obtain ⟨n, hn, hrn⟩ := relDim_eq_trdeg hD hT (contractPrime j P') hP
  obtain ⟨n', hn', hrn'⟩ := relDim_eq_trdeg hD hT P' hP'
  have hnn : n = n' := by
    rw [hrel, hrn'] at hrn
    exact_mod_cast (WithTop.coe_injective (WithBot.coe_injective hrn)).symm
  set E := (homFracDegZero (contractPrime j P')).map (contractFracMap j P')
  set κ' := homFracDegZero P'
  have h : E ≤ κ' := map_homFracDegZero_le j ι' P'
  have hE : Algebra.trdeg F E = n :=
    (IntermediateField.equivMap _ (contractFracMap j P')).trdeg_eq.symm.trans hn
  let _ : Algebra E κ' := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E κ' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul E κ' :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IntermediateField.inclusion h).injective
  have : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).2 (algebraMap F E).injective
  have htow := trdeg_add_eq F E (A := κ')
  rw [hE, hn', ← hnn] at htow
  have hlt : Algebra.trdeg E κ' < Cardinal.aleph0 :=
    lt_of_le_of_lt (htow ▸ self_le_add_left _ _) (Cardinal.natCast_lt_aleph0 (n := n))
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hm] at htow
  have hm0 : m = 0 := by
    have : n + m = n := by exact_mod_cast htow
    omega
  have : Algebra.IsAlgebraic E κ' := trdeg_eq_zero_iff.mp (by rw [hm, hm0]; rfl)
  let g : κ' →ₐ[E] FractionRing (MRing ι' F ⧸ P') :=
    { (κ'.val : κ' →+* FractionRing (MRing ι' F ⧸ P')) with commutes' := fun _ => rfl }
  choose u hu using hP'.relevant
  have hκ' : κ' = IntermediateField.adjoin F (chartGens P' u) := homFracDegZero_eq hD P' u hu
  have hint : ∀ x ∈ chartGens P' u, IsIntegral E x := by
    intro x hx
    have hx' : x ∈ κ' := hκ' ▸ IntermediateField.subset_adjoin F _ hx
    have hy : IsAlgebraic E (⟨x, hx'⟩ : κ') := Algebra.IsAlgebraic.isAlgebraic _
    exact IsIntegral.map g hy.isIntegral
  have : Finite (chartGens P' u) := (Set.finite_range _).to_subtype
  have := IntermediateField.finiteDimensional_adjoin hint
  show IntermediateField.relfinrank E κ' ≠ 0
  rw [IntermediateField.relfinrank_eq_finrank_of_le h]
  have hext : IntermediateField.extendScalars h = IntermediateField.adjoin E (chartGens P' u) := by
    rw [← IntermediateField.extendScalars_adjoin (h.trans hκ'.le)]
    exact IntermediateField.ext fun x =>
      show x ∈ κ' ↔ x ∈ IntermediateField.adjoin F (chartGens P' u) by rw [hκ']
  rw [hext]
  exact Module.finrank_pos.ne'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
