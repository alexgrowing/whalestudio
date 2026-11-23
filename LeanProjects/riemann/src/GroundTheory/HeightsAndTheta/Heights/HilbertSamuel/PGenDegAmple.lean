import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMultiDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntersectionRecursion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace GenDegAmple

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem hilbFn_nonneg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (m : K → ℤ) : 0 ≤ hilbFn q m := by
  unfold hilbFn
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

theorem eventualValue_nonneg {K : Type} [Fintype K] (f : (K → ℤ) → ℤ) (hf : ∀ m, 0 ≤ f m) :
    0 ≤ eventualValue f := by
  unfold eventualValue
  split_ifs with h
  · obtain ⟨m, hm⟩ := h.choose_spec.exists
    rw [← hm]
    exact hf m
  · exact le_rfl

theorem unit_nonneg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (e : ℕ) : ∀ q : Ideal (MRing ι F), NumbersDVR.IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ r : Fin e → K, 0 ≤ intNum F q (fun j => unitDeg (r j)) := by
  induction e with
  | zero =>
    intro q _ _ r
    unfold intNum mixedDiff
    rw [List.ofFn_zero, List.foldr_nil]
    exact eventualValue_nonneg _ (hilbFn_nonneg q)
  | succ e ih =>
    intro q hq hd r
    obtain ⟨i, hX⟩ := hq.relevant (r 0)
    have hd' : ringKrullDim (MRing ι F ⧸ q) = ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := hd
    have hsplit : (fun j : Fin (e + 1) => unitDeg (r j)) =
        Matrix.vecCons (unitDeg (r 0)) (fun j : Fin e => unitDeg (r j.succ)) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
    rw [hsplit, IntersectionRecursion.proof F K ι q e hq hd' (r 0) i hX]
    refine finsum_nonneg fun W => ?_
    split_ifs with h
    · exact mul_nonneg (Int.natCast_nonneg _) (ih W h.1 h.2.2 _)
    · exact le_rfl

end GenDegAmple

theorem GenDegAmple.proof (hVar : GenericFibreVar.Statement) (hPos : MultiDegreePositive.Statement) :
    GenDegAmple.Statement := by
  intro K _ ι _ Ω _ y D d hV hd
  classical
  have hPV := hVar K ι Ω y D hV
  have hP := (Bridge.isMultiProjPrime_iff _).mpr hPV.1
  have hrel : FieldNumbers.relDim (KH.genIdeal y) = D := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hPV.2]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  set f := intNumMultilinear (KH.genIdeal y) D hP.multiHomog hP.relevant hrel with hf
  have hg : ∀ b, genDeg (mCoordIdeal y) D b = f (fun _ => b) := fun b => by
    rw [hf, intNumMultilinear_apply, genDeg]
    congr
  have hN : ∀ r : Fin D → K, 0 ≤ f (fun j => unitDeg (r j)) := fun r => by
    rw [hf, intNumMultilinear_apply]
    exact GenDegAmple.unit_nonneg D _ hP hPV.2 r
  have hH : 0 < f (fun _ => fun _ => (1 : ℤ)) := by
    rw [hf, intNumMultilinear_apply]
    exact hPos ℚ K ι _ D hP hPV.2
  have hsum : ∀ b : K → ℤ, (fun _ : Fin D => b) = fun _ => ∑ k, b k • unitDeg k := fun b => by
    funext _ k'
    simp [unitDeg, Finset.sum_apply, Pi.single_apply]
  have expand : ∀ b : K → ℤ,
      f (fun _ => b) = ∑ r : Fin D → K, (∏ j, b (r j)) * f (fun j => unitDeg (r j)) := fun b => by
    rw [hsum b, f.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [f.map_smul_univ (fun j => b (r j)) (fun j => unitDeg (r j)), smul_eq_mul]
  rw [hg, expand d]
  have hH' := hH
  rw [expand (fun _ => (1 : ℤ))] at hH'
  simp only [Finset.prod_const_one, one_mul] at hH'
  refine lt_of_lt_of_le hH' (Finset.sum_le_sum fun r _ => ?_)
  have hp : (1 : ℤ) ≤ ∏ j, d (r j) := by
    calc (1 : ℤ) = ∏ _j : Fin D, (1 : ℤ) := Finset.prod_const_one.symm
      _ ≤ ∏ j, d (r j) := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j _ => hd (r j))
  exact le_mul_of_one_le_left (hN r) hp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
