import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem differentiableOn_coeff_of_linearIndependent (n m g : ℕ) (U : Set (Fin n → ℂ))
    (d : Fin m → (Fin n → ℂ) → Fin g → ℂ) (x : (Fin n → ℂ) → Fin g → ℂ)
    (w : (Fin n → ℂ) → Fin m → ℂ) (hU : IsOpen U)
    (hd : ∀ b, DifferentiableOn ℂ (d b) U) (hx : DifferentiableOn ℂ x U)
    (hli : ∀ t ∈ U, LinearIndependent ℂ (fun b => d b t))
    (hw : ∀ t ∈ U, x t = ∑ b, w t b • d b t) : DifferentiableOn ℂ w U := by
  intro t₀ ht₀
  apply DifferentiableAt.differentiableWithinAt
  have hUn : U ∈ 𝓝 t₀ := hU.mem_nhds ht₀

  let φ : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ (fun b => d b t₀)
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have h0 := Fintype.linearIndependent_iff.1 (hli t₀ ht₀) v
      (by simpa [φ, Fintype.linearCombination_apply] using hv)
    exact funext h0
  obtain ⟨L0, hL0⟩ := φ.exists_leftInverse_of_injective hφ
  let L : (Fin g → ℂ) →L[ℂ] (Fin m → ℂ) := LinearMap.toContinuousLinearMap L0
  have hLd : ∀ b, L (d b t₀) = Pi.single b 1 := by
    intro b
    have h1 : φ (Pi.single b 1) = d b t₀ := by
      simp [φ, Fintype.linearCombination_apply, Pi.single_apply]
    have h2 := LinearMap.congr_fun hL0 (Pi.single b 1)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, h1] at h2
    exact h2
  let T : (Fin n → ℂ) → ((Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) := fun t =>
    ∑ b, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) b).smulRight (L (d b t))
  have hTapply : ∀ t v, T t v = ∑ b, v b • L (d b t) := by
    intro t v
    simp [T, ContinuousLinearMap.sum_apply]
  have hT0 : T t₀ = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    rw [hTapply]
    simp only [hLd]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hTd : DifferentiableAt ℂ T t₀ := by
    have hb : ∀ b ∈ (Finset.univ : Finset (Fin m)), DifferentiableAt ℂ (fun t =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) b).smulRight (L (d b t))) t₀ := by
      intro b _
      exact (ContinuousLinearMap.smulRightL ℂ (Fin m → ℂ) (Fin m → ℂ)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) b)).differentiableAt.comp t₀
        (L.differentiableAt.comp t₀ ((hd b).differentiableAt hUn))
    exact DifferentiableAt.fun_sum hb
  have hTu : ∀ᶠ t in 𝓝 t₀, IsUnit (T t) := by
    have hc : ContinuousAt T t₀ := hTd.continuousAt
    have : {u : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) | IsUnit u} ∈ 𝓝 (T t₀) := by
      rw [hT0]
      exact Units.isOpen.mem_nhds isUnit_one
    exact hc this
  have heq : w =ᶠ[𝓝 t₀] fun t => Ring.inverse (T t) (L (x t)) := by
    filter_upwards [hTu, hUn] with t hu ht
    obtain ⟨u, hu'⟩ := hu
    have h1 : L (x t) = T t (w t) := by
      rw [hw t ht, hTapply, map_sum]
      simp
    rw [h1, ← hu', Ring.inverse_unit, ← ContinuousLinearMap.mul_apply, u.inv_mul]
    rfl
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  have hinv : DifferentiableAt ℂ (fun t => Ring.inverse (T t)) t₀ := by
    have : DifferentiableAt ℂ Ring.inverse (T t₀) := by
      rw [hT0]
      exact differentiableAt_inverse isUnit_one
    exact this.comp t₀ hTd
  have hLx : DifferentiableAt ℂ (fun t => L (x t)) t₀ :=
    L.differentiableAt.comp t₀ (hx.differentiableAt hUn)
  exact hinv.clm_apply hLx

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
