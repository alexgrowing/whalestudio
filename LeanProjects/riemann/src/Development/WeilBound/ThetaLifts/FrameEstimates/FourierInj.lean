import Mathlib
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.WeilBound.ThetaLifts.FrameEstimates.FourierInjA
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant

noncomputable section

namespace PositivityTheory.ThKEst

open scoped NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels BoundedContinuousFunction

namespace FourInj

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

open scoped Classical in
variable (F κ) in

def split : (κ → AF F) ≃ₜ+ ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) where
  toFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  invFun p := fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) :
    InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  left_inv x := funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  right_inv p := Prod.ext (funext fun i => RingEquiv.apply_symm_apply _ _) rfl
  map_add' x y := Prod.ext (funext fun i => map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1 (y i).1) rfl
  continuous_toFun := Continuous.prodMk
    (continuous_pi fun i => (GroundTheory.Global.homeomorphMixedSpace F).continuous.comp
      (continuous_fst.comp (continuous_apply i)))
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  continuous_invFun := continuous_pi fun i => by
    have h : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm = (GroundTheory.Global.homeomorphMixedSpace F).symm := by
      funext z
      apply (GroundTheory.Global.homeomorphMixedSpace F).injective
      rw [Homeomorph.apply_symm_apply, GroundTheory.Global.homeomorphMixedSpace_apply, RingEquiv.apply_symm_apply]
    refine Continuous.prodMk ?_ ((continuous_apply i).comp continuous_snd)
    rw [h]
    exact (GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp ((continuous_apply i).comp continuous_fst)

open scoped Classical in

theorem sch_props (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Continuous Φ ∧ (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) ∧ Integrable Φ μ := by
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    have := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
    have := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
    have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
    let _ : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
    have : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
    let _ : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
    have : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
    have e : pureA F f g = (fun p => f p.1 * g p.2) ∘ split F κ := rfl
    have hc : Continuous fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) => f p.1 * g p.2 :=
      (f.continuous.comp continuous_fst).mul (hg.1.continuous.comp continuous_snd)
    obtain ⟨C, hC⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
    refine ⟨e ▸ hc.comp (split F κ).continuous, ⟨SchwartzMap.seminorm ℂ 0 0 f * C, fun x => ?_⟩, ?_⟩
    · rw [e, Function.comp_apply, norm_mul]
      exact mul_le_mul (SchwartzMap.norm_le_seminorm ℂ f _) (hC _) (norm_nonneg _) (apply_nonneg _ _)
    · let ν : Measure ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :=
        (Measure.addHaar).prod Measure.addHaar
      have hi : Integrable (fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
          f p.1 * g p.2) ν :=
        f.integrable.mul_prod (hg.1.continuous.integrable_of_hasCompactSupport hg.2)
      have : (μ.map (split F κ)).IsAddHaarMeasure := (split F κ).isAddHaarMeasure_map μ
      have : ν.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
      have h2 := Measure.isAddLeftInvariant_eq_smul (μ.map (split F κ)) ν
      rw [e]
      refine Integrable.comp_measurable ?_ (split F κ).continuous.measurable
      rw [h2]
      exact hi.smul_measure_nnreal
  | zero => exact ⟨continuous_const, ⟨0, fun x => by simp⟩, integrable_zero _ _ _⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨a1, ⟨C, hC⟩, a2⟩ := h1
    obtain ⟨b1, ⟨D, hD⟩, b2⟩ := h2
    exact ⟨a1.add b1, ⟨C + D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩, a2.add b2⟩
  | smul c Φ _ h =>
    obtain ⟨a1, ⟨C, hC⟩, a2⟩ := h
    refine ⟨a1.const_smul c, ⟨‖c‖ * C, fun x => ?_⟩, a2.smul c⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : ∃ x, ψ x ≠ 1 := by
  set n : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)
  have hn : 0 < n := Module.finrank_pos
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hat : At (evI F) (realAd F (1 / (2 * n))) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    refine Prod.ext ?_ ?_
    · show u.1 * _ = 0
      rw [h1, zero_mul]
    · show u.2 * 0 = 0
      rw [mul_zero]
  have hev : evI F (realAd F (1 / (2 * n))) = algebraMap ℝ _ (1 / (2 * n) : ℝ) := RingEquiv.apply_symm_apply _ _
  refine ⟨realAd F (1 / (2 * n)), ?_⟩
  rw [hψ.2.2 _ hat, hev, Algebra.trace_algebraMap]
  have eR : (n • (1 / (2 * n) : ℝ) : ℝ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    field_simp
  rw [eR]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * ((1 / 2 : ℝ) : ℂ) = -(Real.pi * Complex.I) := by push_cast; ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  obtain ⟨s, hs⟩ := exists_ne_one hψ
  have hne : ψ ≠ 1 := fun h1 => hs (by rw [h1]; rfl)
  exact (GlobalTheory.CompanionTheory.AdeleAnn.unitary_and_annihilator_eq F ψ hψ.1 hne hψ.2.1).1 x

theorem nondeg {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : AF F) (h : ∀ y, ψ (x * y) = 1) : x = 0 := by
  obtain ⟨s, hs⟩ := exists_ne_one hψ
  have hne : ψ ≠ 1 := fun h1 => hs (by rw [h1]; rfl)
  obtain ⟨b, rfl⟩ := (GlobalTheory.CompanionTheory.AdeleAnn.unitary_and_annihilator_eq F ψ hψ.1 hne hψ.2.1).2 x fun a => h _
  by_cases hb : b = 0
  · rw [hb, map_zero]
  · refine absurd ?_ hs
    rw [← h (algebraMap F (AF F) b⁻¹ * s), ← mul_assoc, ← map_mul, mul_inv_cancel₀ hb, map_one, one_mul]

theorem eq_zero {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure]
    {H : (κ → AF F) → ℂ} (hc : Continuous H) (hi : Integrable H μ) (h0 : ∀ y, ∫ u, ψ (u ⬝ᵥ y) * H u ∂μ = 0) :
    H = 0 := by
  classical
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : PolishSpace (κ → AF F) := polish_of_lc _
  have hn := norm_psi hψ
  have hne : ∀ t, ψ t ≠ 0 := fun t h => by simpa [h] using hn t
  let e : (κ → AF F) → (κ → AF F) →ᵇ ℂ := fun y =>
    BoundedContinuousFunction.ofNormedAddCommGroup (fun u => ψ (u ⬝ᵥ y))
      (hψ.1.comp (continuous_id.dotProduct continuous_const)) 1 fun u => (hn _).le
  have he : ∀ y u, e y u = ψ (u ⬝ᵥ y) := fun _ _ => rfl
  have hae : H =ᵐ[μ] 0 := by
    refine complex_ae_zero μ e ⟨0, ?_⟩ (fun a b => ⟨a + b, ?_⟩) (fun a => ⟨-a, ?_⟩) (fun x x' hxx => ?_) hi h0
    · ext u; simp [he]
    · ext u; simp [he, AddChar.map_add_eq_mul]
    · ext u
      have h1 : ψ (-(u ⬝ᵥ a)) * ψ (u ⬝ᵥ a) = 1 := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
      have h2 : (starRingEnd ℂ) (ψ (u ⬝ᵥ a)) * ψ (u ⬝ᵥ a) = 1 := by simp [Complex.conj_mul', hn]
      simpa [he] using mul_right_cancel₀ (hne _) (h1.trans h2.symm)
    · by_contra hcon
      push Not at hcon
      refine hxx (funext fun i => sub_eq_zero.1 (nondeg hψ _ fun t => ?_))
      have h1 := hcon (Pi.single i t)
      rw [he, he, dotProduct_single, dotProduct_single] at h1
      rw [sub_mul, AddChar.map_sub_eq_div, h1, div_self (hne _)]
  exact (hc.ae_eq_iff_eq μ continuous_const).1 hae

end FourInj

open FourInj in

theorem fourierInj_of : FourierInj := by
  intro F _ _ κ _ ψ hψ μ hμ Φ₁ h₁ Φ₂ h₂ Ψ₁ k₁ Ψ₂ k₂ hco x u
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hn := norm_psi hψ
  have hne : ∀ t, ψ t ≠ 0 := fun t h => by simpa [h] using hn t
  have hcont : ∀ {A B : (κ → AF F) → ℂ}, A ∈ schA F κ → B ∈ schA F κ → ∀ w,
      Continuous fun v => A (v + w) * (starRingEnd ℂ) (B v) := fun hA hB w =>
    ((sch_props μ hA).1.comp (continuous_id.add continuous_const)).mul
      (Complex.continuous_conj.comp (sch_props μ hB).1)
  have hint : ∀ {A B : (κ → AF F) → ℂ}, A ∈ schA F κ → B ∈ schA F κ → ∀ w,
      Integrable (fun v => A (v + w) * (starRingEnd ℂ) (B v)) μ := by
    intro A B hA hB w
    obtain ⟨C, hC⟩ := (sch_props μ hA).2.1
    have hic : Integrable (fun v => (starRingEnd ℂ) (B v)) μ :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (sch_props μ hB).2.2
    exact hic.bdd_mul (c := C)
      ((sch_props μ hA).1.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun v => hC _)
  have hint' : ∀ {A B : (κ → AF F) → ℂ}, A ∈ schA F κ → B ∈ schA F κ → ∀ w y,
      Integrable (fun v => ψ (v ⬝ᵥ y) * (A (v + w) * (starRingEnd ℂ) (B v))) μ := fun hA hB w y =>
    (hint hA hB w).bdd_mul (c := 1)
      (hψ.1.comp (continuous_id.dotProduct continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun v => (hn _).le)
  have hcoef : ∀ (A B : (κ → AF F) → ℂ) w y, coef F ψ μ A B (w, y) =
      ψ (⅟(2 : AF F) * (w ⬝ᵥ y)) * ∫ v, ψ (v ⬝ᵥ y) * (A (v + w) * (starRingEnd ℂ) (B v)) ∂μ := by
    intro A B w y
    rw [coef, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [schr, AddChar.map_add_eq_mul]
    ring
  have key := eq_zero hψ μ ((hcont h₁ h₂ (x - u)).sub (hcont k₁ k₂ (x - u)))
    ((hint h₁ h₂ (x - u)).sub (hint k₁ k₂ (x - u))) fun y => by
      have h3 := congrFun hco (x - u, y)
      rw [hcoef, hcoef] at h3
      have h4 := mul_left_cancel₀ (hne _) h3
      simp only [Pi.sub_apply, mul_sub]
      rw [integral_sub (hint' h₁ h₂ _ y) (hint' k₁ k₂ _ y), h4, sub_self]
  have h5 := congrFun key u
  simp only [Pi.sub_apply, add_sub_cancel, Pi.zero_apply] at h5
  exact sub_eq_zero.1 h5

end PositivityTheory.ThKEst

end
