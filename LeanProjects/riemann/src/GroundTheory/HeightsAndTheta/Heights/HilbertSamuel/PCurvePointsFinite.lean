import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCurvePointsFinite
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqSumMultihomogeneousComponents
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace CurvePointsFinite

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_eq_eval₂ {F : Type*} [CommRing F] {inst : Algebra ℤ F} (y : (Σ k, ι k) → F) (f : MRing ι) :
    @aeval ℤ F _ _ _ inst y f = eval₂ (Int.castRingHom F) y f := by
  rw [aeval_def]
  congr 1
  exact RingHom.ext_int _ _

def genericPt (W : Ideal (MRing ι)) [W.IsPrime] : (Σ k, ι k) → FractionRing (MRing ι ⧸ W) :=
  fun p ↦ algebraMap (MRing ι ⧸ W) _ (Ideal.Quotient.mk W (X p))

theorem aeval_genericPt (W : Ideal (MRing ι)) [W.IsPrime] (f : MRing ι) :
    aeval (genericPt W) f = algebraMap (MRing ι ⧸ W) _ (Ideal.Quotient.mk W f) := by
  have h : (aeval (genericPt W) : MRing ι →ₐ[ℤ] _).toRingHom =
      (algebraMap (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).comp (Ideal.Quotient.mk W) :=
    ringHom_ext (fun n ↦ by simp) (fun p ↦ by simp [genericPt])
  exact RingHom.congr_fun h f

theorem aeval_genericPt_eq_zero_iff (W : Ideal (MRing ι)) [W.IsPrime] (f : MRing ι) :
    aeval (genericPt W) f = 0 ↔ f ∈ W := by
  rw [aeval_genericPt, ← Ideal.Quotient.eq_zero_iff_mem]
  exact (IsFractionRing.injective (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).eq_iff' (map_zero _)

theorem mCoordIdeal_genericPt (W : Ideal (MRing ι)) [W.IsPrime] (hW : IsMultiHomogIdeal W) :
    mCoordIdeal (genericPt W) = W := by
  apply le_antisymm
  · intro f hf
    rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_sum_multihomogeneous_components f]
    refine Ideal.sum_mem _ fun b _ ↦ ?_
    have h1 := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2comp_mem (CoordinateConeArithVar.isMultiHomogIdeal _) b hf
    rw [mCoordIdeal, RingHom.mem_ker,
      ProjLine.mConeMap_eq_of_isMultiHomog _ (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_i2comp b f)] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact (aeval_genericPt_eq_zero_iff W _).1 (by
        have h' := MvPolynomial.C_eq_zero.1 h
        rw [aeval_eq_eval₂] at h' ⊢
        exact h')
    · exact absurd h (Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k))
  · obtain ⟨S, hS, hWS⟩ := hW
    calc W = Ideal.span S := hWS
      _ ≤ mCoordIdeal (genericPt W) := Ideal.span_le.2 fun f hf ↦ by
        obtain ⟨a, ha⟩ := hS f hf
        have hfW : f ∈ W := hWS ▸ Ideal.subset_span hf
        show f ∈ RingHom.ker (mConeMap (genericPt W))
        have h0 := (aeval_genericPt_eq_zero_iff W f).2 hfW
        rw [RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog _ ha]
        exact mul_eq_zero_of_left (MvPolynomial.C_eq_zero.2 (by
          rw [aeval_eq_eval₂] at h0 ⊢
          exact h0)) _

theorem charZero_fractionRing (W : Ideal (MRing ι)) [W.IsPrime] (hH : IsHorizontal W) :
    CharZero (FractionRing (MRing ι ⧸ W)) := by
  have hinj : Function.Injective (algebraMap ℤ (FractionRing (MRing ι ⧸ W))) := by
    have e : algebraMap ℤ (FractionRing (MRing ι ⧸ W)) =
        (algebraMap (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).comp (algebraMap ℤ (MRing ι ⧸ W)) :=
      RingHom.ext_int _ _
    rw [e]
    exact (IsFractionRing.injective (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).comp (CoordinateConeArithVar.algebraMap_injective W hH)
  exact charZero_of_injective_algebraMap hinj

end CurvePointsFinite

open CurvePointsFinite in

theorem CurvePointsFinite.proof : CurvePointsFinite.Statement := by
  intro K _ ι _ W hW
  have : W.IsPrime := hW.2.1.1
  have := charZero_fractionRing W hW.2.2.1
  have hEq := mCoordIdeal_genericPt W hW.2.1.2.1
  have hP : IsArithVar (mCoordIdeal (genericPt W)) 1 := by rw [hEq]; exact hW
  have hdeg := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.degC_eq hP
  rw [hEq, GroundTheory.Heights₂.Heights.degC_eq_card_projPts] at hdeg
  have := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_blockFnField hP
  set L := ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (genericPt W)
  set S : Set (FractionRing (MRing ι ⧸ W)) :=
    {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = genericPt W p / genericPt W q}
  have hSfin : S.Finite := (Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) ↦
      genericPt W pq.1 / genericPt W pq.2).subset fun t ⟨p, q, _, ht⟩ ↦ ⟨(p, q), ht.symm⟩
  have : Finite S := hSfin.to_subtype
  have hint : ∀ t ∈ S, IsIntegral ℚ t := fun t ht ↦
    ((Algebra.IsAlgebraic.isAlgebraic (⟨t, IntermediateField.subset_adjoin ℚ S ht⟩ : L)).isIntegral).map
      L.val
  have : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_adjoin hint
  have hpos : 0 < Nat.card (L →ₐ[ℚ] ℂ) := Nat.card_pos_iff.2 ⟨⟨IsAlgClosed.lift⟩, inferInstance⟩
  exact (Nat.card_pos_iff.1 (hdeg ▸ hpos)).2

end GroundTheory.Heights₂.Heights.HilbertSamuel
