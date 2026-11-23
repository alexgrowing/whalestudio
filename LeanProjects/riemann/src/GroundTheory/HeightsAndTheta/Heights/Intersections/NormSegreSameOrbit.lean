import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsChartRankAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOver
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherTer
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherMore
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

namespace PullbackDegreeCount

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem sameOrbit_self (z : (Σ k', ι' k') → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem sameOrbit_comp {a b c : (Σ k', ι' k') → ℂ} (h1 : SameOrbit a b) (h2 : SameOrbit b c) :
    SameOrbit a c := by
  obtain ⟨s, hs, rfl⟩ := h1
  obtain ⟨t, ht, rfl⟩ := h2
  exact ⟨fun k => s k * t k, fun k => mul_ne_zero (hs k) (ht k), by funext p; simp [mul_assoc]⟩

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem sameOrbit_flip {a b : (Σ k', ι' k') → ℂ} (h : SameOrbit a b) : SameOrbit b a := by
  obtain ⟨s, hs, rfl⟩ := h
  refine ⟨fun k => (s k)⁻¹, fun k => inv_ne_zero (hs k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hs p.1)]

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem normSegre_sameOrbit {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {z₁ z₂ : (Σ k', ι' k') → ℂ} (h : SameOrbit z₁ z₂) :
    (Ψ (segre fun p => z₁ (v p)) 0)⁻¹ • segre (fun p => z₁ (v p)) =
      (Ψ (segre fun p => z₂ (v p)) 0)⁻¹ • segre (fun p => z₂ (v p)) := by
  obtain ⟨c, hc, rfl⟩ := h
  have h1 : (fun p => c (v p).1 * z₂ (v p)) = fun p : Σ k, ι k => (c ∘ κ) p.1 * z₂ (v p) := by
    funext p
    rw [hv.2.2.1 p]
    rfl
  have hne : ∏ k, (c ∘ κ) k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc (κ k)
  rw [h1, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hne, mul_one]

omit [Fintype K'] in

theorem ncard_pullW_eq {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (w : ((k : K) → ι k) → ℂ)
    (hB : ∀ z' ∈ mcPts P', z' ∈ mcPts J' →
      (Ψ (segre fun p => z' (v p)) 0)⁻¹ • segre (fun p => z' (v p)) ≠ w) :
    {x | pullW R v Ψ x = w}.ncard = (ptsOver P' v Ψ w).ncard := by
  refine Set.ncard_congr (fun x _ => {z'' | SameOrbit z'' (R.lift x x)}) ?_ ?_ ?_
  · intro x hx
    exact ⟨R.lift x x, R.mem x x (R.mem_U x), rfl, hx⟩
  · intro x x' hx hx' h
    have hxB : R.lift x x ∉ mcPts J' := fun hJ => hB _ (R.mem x x (R.mem_U x)) hJ hx
    have hmem : R.lift x x ∈ {z'' | SameOrbit z'' (R.lift x' x')} := h ▸ sameOrbit_self _
    exact R.inj x x' hxB hmem
  · rintro O ⟨z', hz', rfl, hw⟩
    have hzB : z' ∉ mcPts J' := fun hJ => hB z' hz' hJ hw
    obtain ⟨x, hx⟩ := R.surj z' hz' hzB
    refine ⟨x, ?_, ?_⟩
    · show (Ψ (segre fun p => R.lift x x (v p)) 0)⁻¹ • segre (fun p => R.lift x x (v p)) = w
      rw [← hw]
      exact normSegre_sameOrbit hv Ψ hx
    · ext z''
      exact ⟨fun h => sameOrbit_comp h hx, fun h => sameOrbit_comp h (sameOrbit_flip hx)⟩

end PullbackDegreeCount

open PullbackDegreeCount in

theorem PullbackDegreeCount.proof (hDim : FibreDimStatement) (hRank : ChartRankAdjoin.Statement)
    (hCount : GenericPointsCount.Statement) (hB : PullbackVanishingOfNullCycle.Statement) (hBad : pullbackBadImage_holds.Statement) :
    PullbackDegreeCount.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' J' n G J R Ψ hv hP' hP hJ hΨ
  classical
  have hfib : IsProjVarF (fibreIdeal κ G) 0 := hDim K ι K' ι' κ v P' (n + 1) 0 G hv hP' hP
  choose i hi using hfib.1.2.2
  have hz : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0 := by
    intro k h0
    apply hi k
    rw [fibreIdeal, RingHom.mem_ker, aeval_X]
    exact h0
  have he : J (fibreIdeal κ G) 0 Fin.elim0 = (Module.finrank G.Φ (IntermediateField.adjoin G.Φ
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩)) : ℤ) := by
    rw [hJ.1 _ Fin.elim0 i hfib hi]
    exact congrArg _ (hRank (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) i hz hfib.1.2.1)
  have hN := measure_union_null (hB K ι K' ι' κ v P' J' n Ψ hv hP' hP hΨ R.homog R.nondeg)
    (hBad K ι K' ι' κ v P' J' n R Ψ hv hP' hP hΨ)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN, hCount K ι K' ι' κ v P' n G i Ψ hv hP' hP hΨ hz]
    with y hy hc
  intro w hw
  obtain ⟨-, -, -, hΨw⟩ := id hw
  have hset : ({x | pullQ R v Ψ x = y ∧ pullW R v Ψ x = w} \ pullBad R v Ψ) = {x | pullW R v Ψ x = w} := by
    ext x
    refine ⟨fun h => h.1.2, fun hx => ?_⟩
    have hx' : pullW R v Ψ x = w := hx
    have h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0 := by
      intro h0
      have h1 := congrFun hΨw 0
      rw [← hx', pullW, h0, inv_zero, zero_smul, map_zero] at h1
      simp at h1
    have hq : pullQ R v Ψ x = y := by
      funext m
      have h1 := congrFun hΨw m.succ
      rw [← hx', pullW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at h1
      rw [pullQ, ← h1, div_eq_inv_mul]
    exact ⟨⟨hq, hx'⟩, fun hbad => hy (Or.inr ⟨x, ⟨hbad, h0⟩, hq⟩)⟩
  rw [hset, ncard_pullW_eq hv R Ψ w fun z' hz' hJ' hzw => hy (Or.inl ⟨z', hz', hJ', hzw ▸ hw⟩), hc w hw, he]
