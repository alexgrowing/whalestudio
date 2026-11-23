import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartFiniteIrrel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurveFilt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartFiniteIrrelPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem ChartFiniteIrrel.proof : ChartFiniteIrrel.Statement.{u, v, w} := by
  intro K _ ι _ F _ V f i hV hf hirr
  classical
  let _ := MvPolynomial.weightedGradedAlgebra F (mw (ι := ι))
  let M : Ideal (MRingOver F ι) :=
    Ideal.span (weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => 1) : Set (MRingOver F ι))
  have hMrad : M ≤ (V ⊔ Ideal.span {f}).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    refine le_sInf fun W hW => Ideal.span_le.mpr fun x hx => ?_
    have h := hirr W hW
    simp only [IsRelevant, not_forall, not_exists, not_not] at h
    obtain ⟨k, hk⟩ := h
    exact weighted_le_of_irrel (e := fun _ => 1) hk le_rfl hx
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hMrad (IsNoetherian.noetherian M)
  have hA : ∀ t, N ≤ t → weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t) ≤
      (V ⊔ Ideal.span {f}).restrictScalars F := fun t ht _ hh =>
    hN (Ideal.pow_le_pow_right ht (ChartFiniteIrrel.weighted_le_pow t hh))
  have hVh : V.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι))) := by
    obtain ⟨S₀, hS₀, rfl⟩ := hV
    exact Ideal.homogeneous_span _ S₀ fun x hx =>
      let ⟨a, ha⟩ := hS₀ x hx; ⟨a, mem_weighted_of_isMultiHomog ha⟩
  let π := (Ideal.Quotient.mkₐ F (chartIdeal V i)).toLinearMap
  let B : ℕ → Submodule F (MRingOver F ι ⧸ chartIdeal V i) := fun t =>
    (weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t)).map π
  have hmono : ∀ t, B t ≤ B (t + 1) := by
    rintro t _ ⟨h, hh, rfl⟩
    refine ⟨h * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ (fun _ : K => 1) k,
      SetLike.mul_mem_graded hh (mem_weighted_of_isMultiHomog (isMultiHomog_coordProd i _)), ?_⟩
    simp [π, map_prod, mk_chartIdeal_X_self]
  have hstep : ∀ t, N ≤ t + 1 → B (t + 1) ≤ (B t).map (LinearMap.mulLeft F (π f)) := by
    rintro t ht _ ⟨h, hh, rfl⟩
    have h2 : h ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t + 1) ⊓
        (V ⊔ Ideal.span {f}).restrictScalars F := ⟨hh, hA _ ht hh⟩
    rw [sup_span_inf_eq' hVh (mem_weighted_of_isMultiHomog hf) (d := fun _ => t + 1) (fun _ => Nat.le_add_left 1 t),
      show ((fun _ : K => t + 1) - fun _ => 1) = fun _ => t from funext fun _ => by simp] at h2
    obtain ⟨v, ⟨-, hv⟩, _, ⟨g, hg, rfl⟩, rfl⟩ := Submodule.mem_sup.mp h2
    refine ⟨π g, ⟨g, hg, rfl⟩, ?_⟩
    have hv0 : Ideal.Quotient.mk (chartIdeal V i) v = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hv)
    simp [π, hv0]
  have heq : ∀ t, N ≤ t → B t = B (t + 1) := fun t ht =>
    Submodule.eq_of_le_of_finrank_le (hmono t)
      ((Submodule.finrank_mono (hstep t (by omega))).trans (Submodule.finrank_map_le _ _))
  have hconst : ∀ t, N ≤ t → B t = B N := fun t ht => by
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [← heq t ht, ih]
  have htop : B N = ⊤ := by
    refine eq_top_iff.mpr fun a _ => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨e₀, he₀⟩ := exists_homog_chart V i b
    obtain ⟨b', hb', hbb⟩ := he₀ (fun _ => N + ∑ k, e₀ k) fun k =>
      le_add_left (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    rw [← hconst _ (Nat.le_add_right _ _)]
    exact ⟨b', hb', hbb⟩
  rw [Module.finite_def, ← htop]
  exact Module.Finite.iff_fg.mp inferInstance

end GroundTheory.Heights₂.Heights.Targets
