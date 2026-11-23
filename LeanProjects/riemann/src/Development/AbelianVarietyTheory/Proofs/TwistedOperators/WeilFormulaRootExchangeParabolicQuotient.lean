import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProperTripleStatement

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.QuotIntFJ

theorem integral_rotate_three {B X U : Type} [MeasurableSpace X] [MeasurableSpace B] [MeasurableSpace U]
    (β : Measure B) (μ : Measure X) (ρ : Measure U) [SFinite μ] [SFinite β] [SFinite ρ]
    (Φ : B → X → U → ℂ) (hΦ : Integrable (fun z : B × (X × U) => Φ z.1 z.2.1 z.2.2) (β.prod (μ.prod ρ))) :
    Integrable (fun b => ∫ x, ∫ u, Φ b x u ∂ρ ∂μ) β ∧
      ∫ b, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ ∂β = ∫ x, ∫ u, ∫ b, Φ b x u ∂β ∂ρ ∂μ := by
  have hsec : ∀ᵐ b ∂β, Integrable (fun y : X × U => Φ b y.1 y.2) (μ.prod ρ) := hΦ.prod_right_ae
  have hin : ∀ᵐ b ∂β, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ = ∫ y : X × U, Φ b y.1 y.2 ∂(μ.prod ρ) := by
    filter_upwards [hsec] with b hb
    exact (integral_prod (fun y : X × U => Φ b y.1 y.2) hb).symm
  have hsw : Integrable (fun w : (X × U) × B => Φ w.2 w.1.1 w.1.2) ((μ.prod ρ).prod β) := hΦ.swap
  refine ⟨hΦ.integral_prod_left.congr (hin.mono fun b hb => hb.symm), ?_⟩
  calc ∫ b, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ ∂β
      = ∫ b, ∫ y : X × U, Φ b y.1 y.2 ∂(μ.prod ρ) ∂β := integral_congr_ae hin
    _ = ∫ w : B × (X × U), Φ w.1 w.2.1 w.2.2 ∂(β.prod (μ.prod ρ)) := (integral_prod _ hΦ).symm
    _ = ∫ w : (X × U) × B, Φ w.2 w.1.1 w.1.2 ∂((μ.prod ρ).prod β) :=
        (integral_prod_swap (fun w : B × (X × U) => Φ w.1 w.2.1 w.2.2)).symm
    _ = ∫ y : X × U, ∫ b, Φ b y.1 y.2 ∂β ∂(μ.prod ρ) := integral_prod _ hsw
    _ = ∫ x, ∫ u, ∫ b, Φ b x u ∂β ∂ρ ∂μ :=
        integral_prod (fun y : X × U => ∫ b, Φ b y.1 y.2 ∂β) hsw.integral_prod_left

theorem weil_formula_FJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) f z → (∀ h, Integrable (fun β : n → k => f (colE c (ρ + 1) β * h)) (Measure.pi fun _ => ν)) ∧ IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k, f (colE c (ρ + 1) β * h) ∂(Measure.pi fun _ => ν)) z := by
  intro k _ _ _ _ _ _ n _ _ c ρ hρ hρc ν _ μX _ μG f z hq
  obtain ⟨F, hF, hfF, hz⟩ := hq
  have hF' : IsLocallyConstant F ∧ HasCompactSupport F := hF
  obtain ⟨hsck, ht2k⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have := hsck
  have := ht2k
  obtain ⟨hB1, hL1, hS1, -⟩ := volGL_haar k n ν
  obtain ⟨hB2, hL2, hS2, -⟩ := volGL_haar k (n ⊕ Fin c) ν
  have := hB1
  have := hL1
  have := hS1
  have := hB2
  have := hL2
  have := hS2

  have hV : volN ν n c (ρ + 1) =
      (Measure.pi fun _ => ν).map (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)) :=
    GlobalTheory.RootEx.VolN.volN_eq (n := n) (c := c) ν (ρ + 1)
  have : SigmaFinite (volN ν n c (ρ + 1)) := by
    rw [hV]
    exact (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)).sigmaFinite_map
  have : IsFiniteMeasureOnCompacts (volN ν n c (ρ + 1)) := by
    rw [hV]
    refine ⟨fun K hK => ?_⟩
    rw [MeasurableEquiv.map_apply]
    have hpre : (GlobalTheory.RootEx.VolN.coEquiv (k := k) (n := n) (c := c) (ρ + 1)) ⁻¹' K =
        GlobalTheory.RootEx.VolN.co (ρ + 1) '' K := by
      ext e
      constructor
      · intro he
        exact ⟨_, he, GlobalTheory.RootEx.VolN.co_mkNel _ e⟩
      · rintro ⟨g, hg, rfl⟩
        show GlobalTheory.RootEx.Model.mkNel _ (GlobalTheory.RootEx.VolN.co _ g) ∈ K
        rw [GlobalTheory.RootEx.VolN.mkNel_co]
        exact hg
    rw [hpre]
    exact (hK.image (GlobalTheory.RootEx.VolN.continuous_co _)).measure_lt_top

  have hint : ∀ h : GL (n ⊕ Fin c) k, Integrable
      (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h))
      ((Measure.pi fun _ => ν).prod (μX.prod (volN ν n c (ρ + 1)))) := by
    intro h
    have hcont : Continuous (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h)) := by
      refine hF'.1.continuous.comp (Continuous.mul (Continuous.mul (Continuous.mul ?_ ?_) ?_) continuous_const)
      · exact GlobalTheory.RootEx.QuotStep.continuous_embX.comp (continuous_fst.comp continuous_snd)
      · exact continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
      · exact (GlobalTheory.RootEx.QuotStep.continuous_colE (ρ + 1)).comp continuous_fst
    obtain ⟨D, hD, hDC⟩ := GlobalTheory.T.exists_compact_preimage_embX_mul_colE k n c ρ hρ hρc ((fun g => g * h⁻¹) '' tsupport F)
      (hF'.2.image (continuous_mul_const h⁻¹))
    have hsupp : HasCompactSupport (fun w : (n → k) × (GL n k × N k n c (ρ + 1)) =>
        F (embX c w.2.1 * (w.2.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) w.1 * h)) := by
      refine HasCompactSupport.intro
        (hD.image (f := fun t : GL n k × N k n c (ρ + 1) × (n → k) => (t.2.2, (t.1, t.2.1)))
          (by fun_prop)) ?_
      intro w hw
      by_contra hne
      apply hw
      refine ⟨(w.2.1, w.2.2, w.1), hDC _ ⟨_, subset_tsupport _ hne, ?_⟩, rfl⟩
      simp [mul_assoc]
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hfeq : ∀ (h : GL (n ⊕ Fin c) k) (b : n → k), f (colE c (ρ + 1) b * h) =
      ∫ x, ∫ u : N k n c (ρ + 1), F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h)
        ∂(volN ν n c (ρ + 1)) ∂μX := by
    intro h b
    rw [hfF]
    simp only [mul_assoc]
  have key := fun h : GL (n ⊕ Fin c) k => integral_rotate_three (Measure.pi fun _ : n => ν) μX
    (volN ν n c (ρ + 1))
    (fun b x (u : N k n c (ρ + 1)) => F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h))
    (hint h)
  refine ⟨fun h => (key h).1.congr (Filter.Eventually.of_forall fun b => (hfeq h b).symm), ?_⟩
  unfold IsQuotIntFJ
  refine ⟨F, hF, fun h => ?_, hz⟩
  calc ∫ b : n → k, f (colE c (ρ + 1) b * h) ∂(Measure.pi fun _ => ν)
      = ∫ b : n → k, ∫ x, ∫ u : N k n c (ρ + 1),
          F (embX c x * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) b * h)
            ∂(volN ν n c (ρ + 1)) ∂μX ∂(Measure.pi fun _ => ν) :=
        integral_congr_ae (Filter.Eventually.of_forall (hfeq h))
    _ = _ := (key h).2

end GlobalTheory.QuotIntFJ
