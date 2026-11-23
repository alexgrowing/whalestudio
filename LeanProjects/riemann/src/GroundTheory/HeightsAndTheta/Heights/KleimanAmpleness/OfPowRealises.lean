import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastFurther
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisExtra
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem realises_tpow (hT : TensorRealises.Statement) (hB : BaseRealises.Statement)
    {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] [Algebra F Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
    (hmod : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) {β : K → ℤ}
    {Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)} (hQ : BundleRealises y k₀ Q β) :
    ∀ p : ℕ, BundleRealises y k₀ (Q.tpow p) (p • β)
  | 0 => by
    have h0 := hB F K ι Ω y k₀ N e _ rfl hmod 0
    rw [zero_smul] at h0
    rw [zero_smul]
    exact h0
  | p + 1 => by
    have h := hT F K ι Ω y k₀ N e hmod (Q.tpow p) Q (p • β) β (realises_tpow hT hB hmod hQ p) hQ
    rw [succ_nsmul]
    exact h

theorem ModelMulSecs.proof (hT : TensorRealises.Statement) (hB : BaseRealises.Statement) :
    ModelMulSecs.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ p j
  have h := realises_tpow hT hB hmod (β := β) (Q := Q) hQ p j
  rw [Kleiman.LineBundle.tpow_toSubSystem] at h
  exact h

theorem ModelMulSecs.of_powRealises (h : PowRealises.Statement) : ModelMulSecs.Statement :=
  fun F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ p j => h F K ι Ω y k₀ N e _ rfl hmod Q β hQ p j

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
