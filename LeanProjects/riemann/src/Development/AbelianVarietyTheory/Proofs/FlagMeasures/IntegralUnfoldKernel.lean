import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.AdelicUnfold

theorem unfold_smul {Γ X : Type} [Group Γ] [Countable Γ] [MulAction Γ X] [MeasurableSpace X]
    [MeasurableConstSMul Γ X] (μ : Measure X) [SMulInvariantMeasure Γ X μ] {s : Set X}
    (hs : IsFundamentalDomain Γ s μ) (f : X → ℂ) (hf : Integrable f μ) :
    IntegrableOn (fun z => ∑' γ : Γ, f (γ • z)) s μ ∧
      ∫ z, f z ∂μ = ∫ z in s, ∑' γ : Γ, f (γ • z) ∂μ := by
  classical
  have hmeas : ∀ γ : Γ, AEStronglyMeasurable (fun z => f (γ • z)) μ := fun γ =>
    hf.aestronglyMeasurable.comp_measurePreserving (measurePreserving_smul γ μ)
  have hfin : ∑' γ : Γ, ∫⁻ z in s, ‖f (γ • z)‖ₑ ∂μ ≠ ⊤ := by
    rw [← hs.lintegral_eq_tsum'' (fun z => ‖f z‖ₑ)]
    exact hf.hasFiniteIntegral.ne
  have hae : ∀ᵐ z ∂μ.restrict s, ∑' γ : Γ, ‖f (γ • z)‖ₑ < ⊤ := by
    apply ae_lt_top' (AEMeasurable.tsum fun γ => (hmeas γ).restrict.enorm)
    rw [lintegral_tsum fun γ => (hmeas γ).restrict.enorm]
    exact hfin
  have hsm : ∀ᵐ z ∂μ.restrict s, Summable fun γ : Γ => f (γ • z) := by
    filter_upwards [hae] with z hz
    exact Summable.of_norm (tsum_enorm_ne_top_iff_summable_norm.1 hz.ne)
  have hasm : AEStronglyMeasurable (fun z => ∑' γ : Γ, f (γ • z)) (μ.restrict s) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := (Filter.atTop : Filter (Finset Γ)))
      (f := fun t z => ∑ γ ∈ t, f (γ • z)) (fun t => ?_) ?_
    · convert Finset.aestronglyMeasurable_sum t (fun γ _ => (hmeas γ).restrict) using 1
      ext z
      simp [Finset.sum_apply]
    · filter_upwards [hsm] with z hz using hz.hasSum
  refine ⟨⟨hasm, ?_⟩, ?_⟩
  · calc ∫⁻ z in s, ‖∑' γ : Γ, f (γ • z)‖ₑ ∂μ ≤ ∫⁻ z in s, ∑' γ : Γ, ‖f (γ • z)‖ₑ ∂μ :=
          lintegral_mono fun z => enorm_tsum_le_tsum_enorm
      _ = ∑' γ : Γ, ∫⁻ z in s, ‖f (γ • z)‖ₑ ∂μ :=
          lintegral_tsum fun γ => (hmeas γ).restrict.enorm
      _ < ⊤ := hfin.lt_top
  · rw [integral_tsum (fun γ => (hmeas γ).restrict) hfin]
    exact hs.integral_eq_tsum'' f hf

theorem measurePreserving_left (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (g : I.GA) : MeasurePreserving (fun z => g * z) (I.muA μf) (I.muA μf) := by
  unfold AutInst.muA
  have h0 : ∀ v, (muG (I.ε v)).IsMulLeftInvariant := fun v => inferInstance
  have h1 : (Measure.pi fun v => muG (I.ε v)).IsMulLeftInvariant := inferInstance
  have h2 : ((Measure.pi fun v => muG (I.ε v)).prod μf).IsMulLeftInvariant := inferInstance
  exact measurePreserving_mul_left _ g

theorem integral_unfold_kernel : ∀ (B : RowsAut) (φ F : B.I.GA → ℂ) (x : B.I.GA), (∀ᵐ z ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, F (γ * z) = F z) → Integrable (fun g => φ g * F (x * g)) (B.I.muA B.μf) → IntegrableOn (fun z => kern B.I φ x z * F z) B.fund (B.I.muA B.μf) ∧ ∫ g, φ g * F (x * g) ∂(B.I.muA B.μf) = ∫ z in B.fund, kern B.I φ x z * F z ∂(B.I.muA B.μf) := by
  intro B φ F x hF hint
  have := B.haar
  have := B.sf
  have hcount : Countable (GlobalTheory.RatDiscrete.ratSub B.I) := by
    have := (GlobalTheory.RatDiscrete.countable_GFset B.I).to_subtype
    exact this
  have : MeasurableConstSMul (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA :=
    ⟨fun γ => (measurePreserving_left B.I B.μf γ.1).measurable⟩
  have : SMulInvariantMeasure (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA (B.I.muA B.μf) :=
    ⟨fun γ A hA => (measurePreserving_left B.I B.μf γ.1).measure_preimage hA.nullMeasurableSet⟩
  have hfd : IsFundamentalDomain (GlobalTheory.RatDiscrete.ratSub B.I) B.fund (B.I.muA B.μf) :=
    GlobalTheory.RatDiscrete.isFundamentalDomain B.I B.μf B.fund B.fund_spec

  have hh : Integrable (fun z => φ (x⁻¹ * z) * F z) (B.I.muA B.μf) := by
    have := ((measurePreserving_left B.I B.μf x⁻¹).integrable_comp hint.aestronglyMeasurable).2 hint
    convert this using 1
    ext z
    simp [Function.comp, mul_inv_cancel_left]
  have hB : ∫ g, φ g * F (x * g) ∂(B.I.muA B.μf) = ∫ z, φ (x⁻¹ * z) * F z ∂(B.I.muA B.μf) := by
    have hmp := measurePreserving_left B.I B.μf x
    have e := integral_map hmp.measurable.aemeasurable
      (f := fun z => φ (x⁻¹ * z) * F z) (by rw [hmp.map_eq]; exact hh.aestronglyMeasurable)
    rw [hmp.map_eq] at e
    rw [e]
    congr 1
    ext g
    simp [inv_mul_cancel_left]

  have hD : (fun z => ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I, φ (x⁻¹ * (γ.1 * z)) * F (γ.1 * z))
      =ᵐ[(B.I.muA B.μf).restrict B.fund] fun z => kern B.I φ x z * F z := by
    filter_upwards [ae_restrict_of_ae (s := B.fund) hF] with z hz
    unfold kern
    have hγ : ∀ γ : GlobalTheory.RatDiscrete.ratSub B.I,
        φ (x⁻¹ * (γ.1 * z)) * F (γ.1 * z) = φ (x⁻¹ * γ.1 * z) * F z := fun γ => by
      rw [hz γ.1 γ.2, mul_assoc]
    rw [tsum_congr hγ, tsum_mul_right]
    rfl
  obtain ⟨hI, hE⟩ := unfold_smul (B.I.muA B.μf) hfd (fun z => φ (x⁻¹ * z) * F z) hh
  refine ⟨hI.congr hD, ?_⟩
  rw [hB, hE]
  exact integral_congr_ae hD

end GlobalTheory.AdelicUnfold
