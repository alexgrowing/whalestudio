import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem kReg_conv : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)), KReg k → KReg k' → KReg (conv μ E k k') := by
  intro hL n _ _ μ _ E k k' hk hk'
  obtain ⟨hsub, -, -, -, hcG, -, -⟩ := hL n
  obtain ⟨hkc, R, hR⟩ := hk
  obtain ⟨hkc', R', hR'⟩ := hk'
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hmul : ∀ a ∈ GLs n, ∀ b ∈ GLs n, a * b ∈ GLs n := fun a ha b hb => by
    change (a * b).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero ha hb
  refine ⟨?_, R + R', fun x hx hlt => ?_⟩
  · have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
    have hci : Continuous (fun y : G n => (y⁻¹ : G n).val) := hcv.comp continuous_inv
    have h1 : ContinuousOn (fun p : Mat n × G n => k p.2.val) (GLs n ×ˢ Set.univ) :=
      hkc.comp (hcv.comp continuous_snd).continuousOn (fun p _ => hval p.2)
    have h2 : ContinuousOn (fun p : Mat n × G n => k' ((p.2⁻¹ : G n).val * p.1)) (GLs n ×ˢ Set.univ) :=
      hkc'.comp ((hci.comp continuous_snd).mul continuous_fst).continuousOn
        (fun p hp => hmul _ (hval _) _ hp.1)
    have h3 : ContinuousOn (Function.uncurry fun (x : Mat n) (y : G n) => k y.val * k' ((y⁻¹ : G n).val * x))
        (GLs n ×ˢ Set.univ) := h1.clm_comp h2
    exact continuousOn_integral_of_compact_support (hcG R) h3 (fun x y _ hy => by
      have : R < lg y.val := not_le.1 hy
      simp [hR _ (hval y) this])
  · have hz : ∀ y : G n, k y.val * k' ((y⁻¹ : G n).val * x) = 0 := fun y => by
      by_cases hy : R < lg y.val
      · simp [hR _ (hval y) hy]
      · have hm : (y⁻¹ : G n).val * x ∈ GLs n := hmul _ (hval _) _ hx
        have hle := hsub _ (hval y) _ hm
        have he : y.val * ((y⁻¹ : G n).val * x) = x := by
          rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
        rw [he] at hle
        have : R' < lg ((y⁻¹ : G n).val * x) := by linarith [not_lt.1 hy]
        rw [hR' _ hm this, mul_zero]
    change ∫ y : G n, k y.val * k' ((y⁻¹ : G n).val * x) ∂μ = 0
    rw [show (fun y : G n => k y.val * k' ((y⁻¹ : G n).val * x)) = fun _ => 0 from funext hz, integral_zero]

end GlobalTheory.CompanionTheory.WaveMult
