import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientExistence
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory

theorem unitaryRep_inner_map {n : ℕ} {ε : Fin n → Bool} {U : Type} [NormedAddCommGroup U]
    [InnerProductSpace ℂ U] {π : UJ ε →* (U →L[ℂ] U)} (hπ : IsUnitaryRep π) (h : UJ ε) (x y : U) :
    ⟪π h x, π h y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let L : U →ₗᵢ[ℂ] U := ⟨(π h).toLinearMap, hπ.norm_apply h⟩
  exact L.inner_map_map x y

theorem isMulRightInvariant_haar_UJ {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε))
    [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  haveI : (muG ε).IsHaarMeasure := by unfold muG; infer_instance
  have hμ := Measure.isMulLeftInvariant_eq_smul μ (muG ε)
  constructor
  intro g
  rw [hμ, Measure.map_smul, indefinite_unitary_unimodular n ε g]

theorem span_orbit_coeff_memLp {n : ℕ} {ε : Fin n → Bool} (μ : Measure (UJ ε)) [μ.IsHaarMeasure]
    {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] {π : UJ ε →* (U →L[ℂ] U)}
    (hπ : IsUnitaryRep π) (q : ℝ≥0∞) (v : U) (hv : MemLp (fun g => ⟪v, π g v⟫_ℂ) q μ)
    (u : U) (hu : u ∈ Submodule.span ℂ (Set.range fun g => π g v))
    (u' : U) (hu' : u' ∈ Submodule.span ℂ (Set.range fun g => π g v)) :
    MemLp (fun g => ⟪u', π g u⟫_ℂ) q μ := by
  haveI := isMulRightInvariant_haar_UJ ε μ

  have gen : ∀ h g₀ : UJ ε, MemLp (fun g => ⟪π h v, π g (π g₀ v)⟫_ℂ) q μ := by
    intro h g₀
    have e : (fun g => ⟪π h v, π g (π g₀ v)⟫_ℂ) =
        (fun g => ⟪v, π g v⟫_ℂ) ∘ (fun g => h⁻¹ * g) ∘ (fun g => g * g₀) := by
      funext g
      simp only [Function.comp]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul,
        ← unitaryRep_inner_map hπ h⁻¹ (π h v), ← ContinuousLinearMap.mul_apply, ← map_mul,
        ← ContinuousLinearMap.mul_apply (π h⁻¹), ← map_mul, inv_mul_cancel, map_one,
        ContinuousLinearMap.one_apply]
    rw [e]
    exact (hv.comp_measurePreserving (measurePreserving_mul_left μ h⁻¹)).comp_measurePreserving
      (measurePreserving_mul_right μ g₀)
  have step1 : ∀ h : UJ ε, ∀ u ∈ Submodule.span ℂ (Set.range fun g => π g v),
      MemLp (fun g => ⟪π h v, π g u⟫_ℂ) q μ := by
    intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, rfl⟩ := hx
      exact gen h g₀
    | zero =>
      have : (fun g => ⟪π h v, π g (0 : U)⟫_ℂ) = 0 := by funext g; simp
      rw [this]; exact MemLp.zero
    | add x y _ _ hx hy =>
      have : (fun g => ⟪π h v, π g (x + y)⟫_ℂ) =
          (fun g => ⟪π h v, π g x⟫_ℂ) + (fun g => ⟪π h v, π g y⟫_ℂ) := by
        funext g; simp [map_add, inner_add_right]
      rw [this]; exact hx.add hy
    | smul c x _ hx =>
      have : (fun g => ⟪π h v, π g (c • x)⟫_ℂ) = c • (fun g => ⟪π h v, π g x⟫_ℂ) := by
        funext g; simp [map_smul, inner_smul_right]
      rw [this]; exact hx.const_smul c
  induction hu' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    exact step1 h u hu
  | zero =>
    have : (fun g => ⟪(0 : U), π g u⟫_ℂ) = 0 := by funext g; simp
    rw [this]; exact MemLp.zero
  | add x y _ _ hx hy =>
    have : (fun g => ⟪x + y, π g u⟫_ℂ) = (fun g => ⟪x, π g u⟫_ℂ) + (fun g => ⟪y, π g u⟫_ℂ) := by
      funext g; simp [inner_add_left]
    rw [this]; exact hx.add hy
  | smul c x _ hx =>
    have : (fun g => ⟪c • x, π g u⟫_ℂ) = (starRingEnd ℂ c) • (fun g => ⟪x, π g u⟫_ℂ) := by
      funext g; simp [inner_smul_left, mul_comm]
    rw [this]; exact hx.const_smul _

theorem span_orbit_coeff_integrable : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ (p : ℝ), 1 ≤ p → ∀ v : U, Integrable (fun g => ‖⟪v, π g v⟫_ℂ‖ ^ p) μ → ∀ u ∈ Submodule.span ℂ (Set.range fun g => π g v), ∀ u' ∈ Submodule.span ℂ (Set.range fun g => π g v), Integrable (fun g => ‖⟪u', π g u⟫_ℂ‖ ^ p) μ := by
  intro n ε μ _ U _ _ π hπ p hp v hv u hu u' hu'
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hqt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have cont : ∀ a b : U, Continuous fun g => ⟪a, π g b⟫_ℂ := fun a b =>
    continuous_const.inner (hπ.continuous_apply b)
  have hv' : MemLp (fun g => ⟪v, π g v⟫_ℂ) (ENNReal.ofReal p) μ := by
    rw [← integrable_norm_rpow_iff (cont v v).aestronglyMeasurable hq0 hqt, hpr]
    exact hv
  have h := span_orbit_coeff_memLp μ hπ _ v hv' u hu u' hu'
  rw [← integrable_norm_rpow_iff (cont u' u).aestronglyMeasurable hq0 hqt, hpr] at h
  exact h

end GlobalTheory
