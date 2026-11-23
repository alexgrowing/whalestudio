import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem integral_conv_apply_eq {Γ V : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] (μ : Measure Γ) [μ.IsHaarMeasure]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F F' : Γ → (V →L[ℂ] V)) (φ : Γ → V) (hF : Continuous F) (hF' : Continuous F') (hφ : Continuous φ)
    (cF : HasCompactSupport F) (cF' : HasCompactSupport F') :
    ∫ z, (∫ y, F y * F' (y⁻¹ * z) ∂μ) (φ z) ∂μ = ∫ y, F y (∫ z, F' z (φ (y * z)) ∂μ) ∂μ := by
  have h1 : ∀ z, (∫ y, F y * F' (y⁻¹ * z) ∂μ) (φ z) = ∫ y, F y (F' (y⁻¹ * z) (φ z)) ∂μ := by
    intro z
    have hc : Continuous fun y => F y * F' (y⁻¹ * z) :=
      hF.mul (hF'.comp ((continuous_inv).mul continuous_const))
    have hs : HasCompactSupport fun y => F y * F' (y⁻¹ * z) :=
      HasCompactSupport.intro cF fun y hy => by
        simp [image_eq_zero_of_notMem_tsupport hy]
    have := ContinuousLinearMap.integral_apply (hc.integrable_of_hasCompactSupport (μ := μ) hs) (φ z)
    simpa using this
  simp_rw [h1]
  have hcont : Continuous (Function.uncurry fun (z y : Γ) => F y (F' (y⁻¹ * z) (φ z))) := by
    have a1 : Continuous fun p : Γ × Γ => F p.2 := hF.comp continuous_snd
    have a2 : Continuous fun p : Γ × Γ => F' (p.2⁻¹ * p.1) :=
      hF'.comp (continuous_snd.inv.mul continuous_fst)
    have a3 : Continuous fun p : Γ × Γ => φ p.1 := hφ.comp continuous_fst
    exact a1.clm_apply (a2.clm_apply a3)
  have hsupp : HasCompactSupport (Function.uncurry fun (z y : Γ) => F y (F' (y⁻¹ * z) (φ z))) := by
    have hK : IsCompact ((fun p : Γ × Γ => (p.1 * p.2, p.1)) '' (tsupport F ×ˢ tsupport F')) :=
      (IsCompact.prod cF cF').image ((continuous_fst.mul continuous_snd).prodMk continuous_fst)
    refine HasCompactSupport.intro hK ?_
    rintro ⟨z, y⟩ hzy
    by_cases hy : y ∈ tsupport F
    · by_cases hy' : y⁻¹ * z ∈ tsupport F'
      · exact absurd ⟨(y, y⁻¹ * z), ⟨hy, hy'⟩, by simp⟩ hzy
      · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy']
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy]
  rw [integral_integral_swap_of_hasCompactSupport hcont hsupp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change ∫ z, F y (F' (y⁻¹ * z) (φ z)) ∂μ = F y (∫ z, F' z (φ (y * z)) ∂μ)
  rw [← integral_mul_left_eq_self (fun z => F y (F' (y⁻¹ * z) (φ z))) y]
  simp only [inv_mul_cancel_left]
  have hc : Continuous fun z => F' z (φ (y * z)) :=
    hF'.clm_apply (hφ.comp (continuous_const.mul continuous_id))
  have hs : HasCompactSupport fun z => F' z (φ (y * z)) :=
    HasCompactSupport.intro cF' fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
  exact (F y).integral_comp_comm (hc.integrable_of_hasCompactSupport (μ := μ) hs)

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  (Matrix.isUnits_det_units y).ne_zero

theorem KReg.continuous_val {n : ℕ} {V : Type} [NormedAddCommGroup V] {k : Mat n → V} (hk : KReg k) :
    Continuous fun y : G n => k y.val :=
  hk.1.comp_continuous Units.continuous_val val_mem_GLs

theorem KReg.hasCompactSupport_val (hL : LgFacts) {n : ℕ} {V : Type} [NormedAddCommGroup V] {k : Mat n → V}
    (hk : KReg k) : HasCompactSupport fun y : G n => k y.val := by
  obtain ⟨R, hR⟩ := hk.2
  refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) fun y hy => ?_
  exact hR _ (val_mem_GLs y) (not_le.1 hy)

theorem act_conv : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), KReg k → KReg k' →
    ContinuousOn f (GLs n) → ∀ x ∈ GLs n, act μ E (conv μ E k k') f x = act μ E k (act μ E k' f) x := by
  intro hL n _ _ μ _ E k k' f hk hk' hf x hx
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨X, rfl⟩ : ∃ X : G n, X.val = x :=
    (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)
  have hφ : Continuous fun z : G n => f (X.val * z.val) :=
    hf.comp_continuous (continuous_const.mul Units.continuous_val) fun z => val_mem_GLs (X * z)
  have key := integral_conv_apply_eq μ (fun y : G n => k y.val) (fun y : G n => k' y.val)
    (fun z : G n => f (X.val * z.val)) hk.continuous_val hk'.continuous_val hφ
    (hk.hasCompactSupport_val hL) (hk'.hasCompactSupport_val hL)
  simp only [Units.val_mul, ← mul_assoc] at key
  exact key

end GlobalTheory.CompanionTheory.WaveMult
