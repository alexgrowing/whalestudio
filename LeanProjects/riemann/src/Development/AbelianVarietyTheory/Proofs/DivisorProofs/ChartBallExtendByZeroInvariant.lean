import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ChartBallExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def InOrbit (X : Data E r) (x : Frame X.Ψ r) (R : ℝ) (y : Frame X.Ψ r) : Prop :=
  ∃ z : V (nd X), ‖z‖ ≤ R ∧ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul (cpt X x z) b)

open Classical in

noncomputable def ext (X : Data E r) (x : Frame X.Ψ r) (R : ℝ) (η : V (nd X) → ℝ) (y : Frame X.Ψ r) : ℝ :=
  if h : InOrbit X x R y then η h.choose else 0

theorem uniq (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (ho : IsOrth X x)
    (hinj : ∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r,
      lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1)
    {γ γ' : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hγ' : γ' ∈ X.Γ) {b b' : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) {z z' : V (nd X)} (hz : ‖z‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (h : lact γ (rmul (cpt X x z) b) = lact γ' (rmul (cpt X x z') b')) : z = z' := by
  have h1 : lact (γ'⁻¹ * γ) (rmul (cpt X x z) b) = rmul (cpt X x z') b' := by
    rw [← IW.lact_lact, h, IW.lact_lact, inv_mul_cancel, IW.lact_one]
  have h2 : lact (γ'⁻¹ * γ) (cpt X x z) = rmul (cpt X x z') (IW.bmul X b' (IW.binv X b)) := by
    rw [← IW.rmul_rmul, ← h1, IW.lact_rmul, IW.rmul_binv X _ hb]
  have h3 := hinj _ (X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ) z z' hz hz' _
    (IW.bmul_mem X hb' (IW.binv_mem X hb)) h2
  rw [h3, IW.lact_one] at h1
  exact (KU.cpt_inj X ho hb hb' h1).1

theorem ext_val (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (ho : IsOrth X x)
    (hinj : ∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r,
      lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1)
    (η : V (nd X) → ℝ) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    {z : V (nd X)} (hz : ‖z‖ ≤ R) : ext X x R η (lact γ (rmul (cpt X x z) b)) = η z := by
  have hP : InOrbit X x R (lact γ (rmul (cpt X x z) b)) := ⟨z, hz, γ, hγ, b, hb, rfl⟩
  unfold ext
  rw [dif_pos hP]
  obtain ⟨hz', γ', hγ', b', hb', he⟩ := hP.choose_spec
  rw [uniq X ho hinj hγ' hγ hb' hb hz' hz he.symm]

theorem ext_zero (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (η : V (nd X) → ℝ) {y : Frame X.Ψ r}
    (hy : ¬ InOrbit X x R y) : ext X x R η y = 0 := by
  unfold ext
  rw [dif_neg hy]

end GlobalTheory.ChartBallExt

open GlobalTheory.ChartBallExt in

theorem GlobalTheory.chartBall_extend_by_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (R : ℝ), IsOrth X x → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) → ∀ η : V (nd X) → ℝ, ∃ ψ : Frame X.Ψ r → ℝ, (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) ∧ (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ R ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) ∧ (∀ γ ∈ X.Γ, ∀ y, ψ (lact γ y) = ψ y) ∧ (∀ y, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y) := by
  intro E _ _ _ r X x R ho _ hinj η
  refine ⟨ext X x R η, ?_, ?_, ?_, ?_⟩
  · intro γ hγ b hb z hz
    exact ext_val X ho hinj η hγ hb hz
  · intro y hy
    refine ext_zero X η ?_
    rintro ⟨z, hz, γ, hγ, b, hb, e⟩
    exact hy ⟨γ, hγ, b, hb, z, hz, e⟩
  · intro γ hγ y
    by_cases hy : InOrbit X x R y
    · obtain ⟨z, hz, γ0, hγ0, b, hb, rfl⟩ := hy
      rw [IW.lact_lact, ext_val X ho hinj η (X.Γ.mul_mem hγ hγ0) hb hz, ext_val X ho hinj η hγ0 hb hz]
    · have hy' : ¬ InOrbit X x R (lact γ y) := by
        rintro ⟨z, hz, γ0, hγ0, b, hb, e⟩
        refine hy ⟨z, hz, γ⁻¹ * γ0, X.Γ.mul_mem (X.Γ.inv_mem hγ) hγ0, b, hb, ?_⟩
        rw [← IW.lact_lact, ← e, IW.lact_lact, inv_mul_cancel, IW.lact_one]
      rw [ext_zero X η hy, ext_zero X η hy']
  · intro y b hb
    by_cases hy : InOrbit X x R y
    · obtain ⟨z, hz, γ0, hγ0, b0, hb0, rfl⟩ := hy
      rw [← IW.lact_rmul, IW.rmul_rmul, ext_val X ho hinj η hγ0 (IW.bmul_mem X hb0 hb) hz,
        ext_val X ho hinj η hγ0 hb0 hz]
    · have hy' : ¬ InOrbit X x R (rmul y b) := by
        rintro ⟨z, hz, γ0, hγ0, b0, hb0, e⟩
        refine hy ⟨z, hz, γ0, hγ0, IW.bmul X b0 (IW.binv X b), IW.bmul_mem X hb0 (IW.binv_mem X hb), ?_⟩
        rw [← IW.rmul_rmul, IW.lact_rmul, ← e, IW.rmul_binv X y hb]
      rw [ext_zero X η hy, ext_zero X η hy']
