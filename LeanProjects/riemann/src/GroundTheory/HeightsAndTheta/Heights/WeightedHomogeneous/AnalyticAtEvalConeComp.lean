import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem analyticAt_evalCone_comp {ι : Type} [Fintype ι] {n : ι → ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (z : E → Cone n ℂ) (u₀ : E) (hz : ∀ k i, AnalyticAt ℂ (fun u ↦ z u k i) u₀)
    (f : MvPolynomial (Coord n) ℤ) : AnalyticAt ℂ (fun u ↦ evalCone (z u) f) u₀ := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h : (fun u ↦ evalCone (z u) (C a)) = fun _ ↦ ((a : ℤ) : ℂ) := by
      funext u; rw [evalCone, eval₂_C]; simp
    rw [h]; exact analyticAt_const
  | add p q hp hq =>
    have h : (fun u ↦ evalCone (z u) (p + q)) = fun u ↦ evalCone (z u) p + evalCone (z u) q := by
      funext u; simp [evalCone]
    rw [h]; exact hp.add hq
  | mul_X p v hp =>
    have h : (fun u ↦ evalCone (z u) (p * X v)) = fun u ↦ evalCone (z u) p * z u v.1 v.2 := by
      funext u; simp [evalCone]
    rw [h]; exact hp.mul (hz v.1 v.2)

theorem PlurisubharmonicMetric.proof (hPts : ConePoints.Statement) (hMet : ChartMetric.Statement) : PlurisubharmonicMetric.Statement := by
  intro ι _ _ n P D N hN d g hg r G δ hG e γ u₀ hγ hev
  have hw₀ : γ u₀ ∈ D.extPoints := hev.self_of_nhds
  obtain ⟨hz₀, la₀, hla₀, hrel₀⟩ := (hPts ι n P D d g hg).2 _ hw₀

  choose c hc using fun k ↦ Function.ne_iff.mp (hz₀.1 k)
  have hm₀ : evalCone (D.basePart₂ (γ u₀)) (chartMonomial c d) ≠ 0 := by
    simp only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

  obtain ⟨j, hj⟩ := Function.ne_iff.mp (hw₀.1 none)
  have hj' : D.newPart (γ u₀) j ≠ 0 := hj
  have hg₀ : evalCone (D.basePart₂ (γ u₀)) (g c j) ≠ 0 := by
    intro h0
    apply hj'
    rw [hrel₀ c hm₀ j, h0, mul_zero, zero_div]

  have hco : ∀ (o : Option ι) (i : Fin (D.extSizes o + 1)), AnalyticAt ℂ (fun u ↦ γ u o i) u₀ :=
    fun o i ↦ ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (D.extSizes o + 1) ↦ ℂ) i).analyticAt _).comp
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun o ↦ Fin (D.extSizes o + 1) → ℂ) o).analyticAt _).comp hγ)
  have hold : ∀ f, AnalyticAt ℂ (fun u ↦ evalCone (D.basePart₂ (γ u)) f) u₀ :=
    analyticAt_evalCone_comp (fun u ↦ D.basePart₂ (γ u)) u₀ fun k i ↦ hco (some k) i
  have hM := hold (chartMonomial c d)
  have hG' := hold (g c j)
  have hnew : AnalyticAt ℂ (fun u ↦ D.newPart (γ u) j) u₀ := hco none j
  refine ⟨fun u ↦ D.newPart (γ u) j * evalCone (D.basePart₂ (γ u)) (chartMonomial c d) /
      evalCone (D.basePart₂ (γ u)) (g c j), (hnew.mul hM).div hG' hg₀, ?_, ?_⟩
  · simp only
    rw [hrel₀ c hm₀ j]
    field_simp
    exact hla₀
  · filter_upwards [hev, hM.continuousAt.eventually_ne hm₀, hG'.continuousAt.eventually_ne hg₀]
      with u hu hmu hgu
    obtain ⟨_, la, _, hrel⟩ := (hPts ι n P D d g hg).2 _ hu
    have hla : D.newPart (γ u) j * evalCone (D.basePart₂ (γ u)) (chartMonomial c d) /
        evalCone (D.basePart₂ (γ u)) (g c j) = la := by
      rw [hrel c hmu j]
      field_simp
    rw [hla]
    exact (hMet ι n P D N hN d g hg r G δ hG).2 _ hu c la hmu (hrel c hmu)

end

end GroundTheory.Heights₂.Heights
