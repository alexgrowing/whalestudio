import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace PositivityTheory.Rg.BcB.E2.P

namespace Speciso

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {S : Type}
  [TopologicalSpace S] [CompactSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]

def Lmap (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K)) (v : K) : C(S, ℂ) →ₗ[ℂ] K where
  toFun f := π f v
  map_add' f g := by simp
  map_smul' c f := by simp

lemma inner_L (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K)) (v : K) (ν : Measure S) [IsFiniteMeasure ν]
    (hν : ∀ f : C(S, ℂ), ∫ s, f s ∂ν = inner ℂ v (π f v)) (f : C(S, ℂ)) :
    inner ℂ (π f v) (π f v) =
      inner ℂ (ContinuousMap.toLp (E := ℂ) 2 ν ℂ f) (ContinuousMap.toLp (E := ℂ) 2 ν ℂ f) := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : inner ℂ (π f v) (π f v) = ∫ s, (star f * f) s ∂ν := by
    rw [hν, map_mul, map_star, ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  rw [h1]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := ν) f] with s hs
  rw [hs]
  simp [Complex.conj_mul']

lemma norm_L (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K)) (v : K) (ν : Measure S) [IsFiniteMeasure ν]
    (hν : ∀ f : C(S, ℂ), ∫ s, f s ∂ν = inner ℂ v (π f v)) (f : C(S, ℂ)) :
    ‖Lmap π v f‖ = ‖ContinuousMap.toLp (E := ℂ) 2 ν ℂ f‖ := by
  have h := congrArg RCLike.re (inner_L π v ν hν f)
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

end Speciso

open Speciso in
theorem speciso : SpecIso := by
  intro K _ _ _ S _ _ _ _ _ π v ν _ _ hν
  set e : C(S, ℂ) →L[ℂ] Lp ℂ 2 ν := ContinuousMap.toLp (E := ℂ) 2 ν ℂ with he
  have hd : DenseRange e := ContinuousMap.toLp_denseRange ℂ ν ℂ (p := 2) (by simp)
  have hcoe : ∀ g, (e g : S → ℂ) =ᵐ[ν] g := fun g =>
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := ν) g
  have hn : ∀ f, ‖Lmap π v f‖ = ‖e.toLinearMap f‖ := fun f => norm_L π v ν hν f
  have hb : ∃ C, ∀ f, ‖Lmap π v f‖ ≤ C * ‖e.toLinearMap f‖ := ⟨1, fun f => by rw [hn, one_mul]⟩
  have hdl : DenseRange e.toLinearMap := hd
  let V : Lp ℂ 2 ν →L[ℂ] K := (Lmap π v).extendOfNorm e.toLinearMap
  have hVe : ∀ f, V (e f) = π f v := fun f => LinearMap.extendOfNorm_eq hdl hb f
  refine ⟨V, fun h => ?_, fun f h h' hh' => ?_⟩
  · refine hd.induction_on (p := fun h => ‖V h‖ = ‖h‖) h
      (isClosed_eq (continuous_norm.comp V.continuous) continuous_norm) ?_
    intro g
    show ‖V (e g)‖ = ‖e g‖
    rw [hVe]
    exact hn g
  · let F : Lp ℂ ∞ ν := ContinuousMap.toLp (E := ℂ) ∞ ν ℂ f
    have hF : (F : S → ℂ) =ᵐ[ν] f := ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (μ := ν) f
    let M : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν := (ContinuousLinearMap.mul ℂ ℂ).holderL ν ∞ 2 2 F
    have hM : ∀ g, (M g : S → ℂ) =ᵐ[ν] fun s => f s * g s := by
      intro g
      have h1 : (M g : S → ℂ) =ᵐ[ν] fun s => (ContinuousLinearMap.mul ℂ ℂ) (F s) (g s) :=
        (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) F g
      filter_upwards [h1, hF] with s hs hFs
      rw [hs, ContinuousLinearMap.mul_apply', hFs]
    have key : ∀ g, V (M g) = π f (V g) := by
      intro g
      refine hd.induction_on (p := fun g => V (M g) = π f (V g)) g
        (isClosed_eq (V.continuous.comp M.continuous) ((π f).continuous.comp V.continuous)) ?_
      intro g
      have : M (e g) = e (f * g) := by
        apply Lp.ext
        filter_upwards [hM (e g), hcoe g, hcoe (f * g)] with s h1 h2 h3
        rw [h1, h2, h3]
        rfl
      show V (M (e g)) = π f (V (e g))
      rw [this, hVe, hVe, map_mul, ContinuousLinearMap.mul_apply]
    have : h' = M h := by
      apply Lp.ext
      filter_upwards [hh', hM h] with s h1 h2
      rw [h1, h2]
    rw [this, key]

end PositivityTheory.Rg.BcB.E2.P
