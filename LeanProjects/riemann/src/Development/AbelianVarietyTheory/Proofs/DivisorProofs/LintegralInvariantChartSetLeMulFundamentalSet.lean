import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.Unfold

theorem lintegral_chart_le_mul_fundSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x : Frame X.Ψ r) (FF A : Set (V (nd X))) (m : ℝ≥0∞) (Φ : Frame X.Ψ r → ℝ≥0∞), IsOrth X x0 → IsOrth X x → IsFundSet X x0 FF → MeasurableSet A → A ⊆ OmF X x → Measurable Φ → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x) → (∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) → (({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b}.encard : ℝ≥0∞) ≤ m) → ∫⁻ z in A, Φ (cpt X x z) ∂(muF X x) ≤ m * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  intro E _ _ _ r X x0 x FF A m Φ ho0 ho hF hA hAO hΦ hΓ hB hm
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hM := ReciprocityTheory.ChartRestriction.G.AR.Up.measInv_holds (E := E)
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  let ψ : Frame X.Ψ r → ℝ≥0∞ := (satFrames X x A).indicator Φ
  have hψ : Measurable ψ := hΦ.indicator (measurableSet_satFrames X ho hA hAO)
  have hψB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y := by
    intro y hy b hb
    simp only [ψ, Set.indicator, rmul_mem_satFrames_iff X x A _ hb, hB b hb y hy]
  have h1 : ∫⁻ z in A, Φ (cpt X x z) ∂muF X x = ∫⁻ z, ψ (cpt X x z) ∂muF X x := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun z => ?_
    simp only [ψ, Set.indicator, cpt_mem_satFrames_iff X ho]
  rw [h1, ← hM r X x0 x ho0 ho ψ hψ hψB, lintegral_unfold hM r X x0 ho0 FF hF ψ hψ hψB,
    ← lintegral_const_mul m (f := fun z => Φ (cpt X x0 z)) (hΦ.comp hc)]
  refine setLIntegral_mono ((hΦ.comp hc).const_mul m) fun z hz => ?_
  set y := cpt X x0 z with hy_def
  have hy : y ∈ X.dom := hF.2.1 hz
  let S : Set (GL (Fin r) E) := {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ b ∈ Bor X.Ψ r,
    lact γ (cpt X x z) = rmul (cpt X x z') b}
  let T : Set X.Γ := {γ | lact γ.1 y ∈ satFrames X x A}
  by_cases hT : T.Nonempty
  swap
  · have h0 : ∀ γ : X.Γ, ψ (lact γ.1 y) = 0 := fun γ =>
      Set.indicator_of_notMem (s := satFrames X x A) (fun h => hT ⟨γ, h⟩) Φ
    simp [h0]
  obtain ⟨γ0, hγ0⟩ := hT
  obtain ⟨z0, hz0, b0, hb0, e0⟩ := hγ0
  have hpt : ∀ γ : X.Γ, ψ (lact γ.1 y) ≤ T.indicator (fun _ => Φ y) γ := by
    intro γ
    by_cases hγ : γ ∈ T
    · rw [Set.indicator_of_mem hγ]
      show (satFrames X x A).indicator Φ _ ≤ _
      rw [Set.indicator_of_mem (s := satFrames X x A) hγ Φ, hΓ γ.1 γ.2 y hy]
    · rw [Set.indicator_of_notMem hγ]
      exact le_of_eq (Set.indicator_of_notMem (s := satFrames X x A) hγ Φ)
  have hTS : T.encard ≤ S.encard := by
    let f : X.Γ → GL (Fin r) E := fun γ => γ.1 * γ0.1⁻¹
    have hinj : Set.InjOn f T := fun a _ b _ h => Subtype.ext (mul_right_cancel h)
    rw [← hinj.encard_image]
    refine Set.encard_le_encard ?_
    rintro _ ⟨γ, ⟨z1, hz1, b1, hb1, e1⟩, rfl⟩
    refine ⟨X.Γ.mul_mem γ.2 (X.Γ.inv_mem γ0.2), z0, hz0, z1, hz1,
      rmul b1 (ExtFPf.invF X b0), ExtFPf.mul_mem X hb1 (ExtFPf.invF_mem X hb0), ?_⟩
    have e0' : cpt X x z0 = rmul (lact γ0.1 y) (ExtFPf.invF X b0) := by
      rw [e0, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb0, ExtFPf.rmul_oneF]
    show lact (γ.1 * γ0.1⁻¹) (cpt X x z0) = _
    rw [e0', FundSetPf.lact_rmul, FundSetPf.lact_mul, FundSetPf.lact_inv, e1, ExtFPf.rmul_assoc]
  calc ∑' γ : X.Γ, ψ (lact γ.1 y) ≤ ∑' γ : X.Γ, T.indicator (fun _ => Φ y) γ := ENNReal.tsum_le_tsum hpt
    _ = (T.encard : ℝ≥0∞) * Φ y := by rw [← tsum_subtype, ENNReal.tsum_set_const]
    _ ≤ m * Φ y := by
      gcongr
      exact le_trans (by exact_mod_cast hTS) hm

end GlobalTheory.Unfold
