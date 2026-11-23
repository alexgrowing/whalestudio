import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeakIntegralOfIsLocallyConstantOfIsCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.SBConv

section Abstract
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

theorem eventually_translate {F : G → ℂ} (hF : F ∈ SB G) :
    ∀ᶠ x in nhds (0 : G), ∀ g, F (g - x) = F g := by
  have hlc : IsLocallyConstant F := hF.1
  have hK : IsCompact (tsupport F) := hF.2
  have hz : ∀ z, z ∉ tsupport F → F z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport F h)
  have step : ∀ᶠ x in nhds (0 : G), ∀ y ∈ tsupport F, F (y - x) = F y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hy := hlc.eventually_eq y
    have h1 : Filter.Tendsto (fun p : G × G => p.2 - p.1) (nhds ((0 : G), y)) (nhds y) := by
      simpa using (continuous_snd.tendsto ((0 : G), y)).sub (continuous_fst.tendsto ((0 : G), y))
    have h2 : Filter.Tendsto (fun p : G × G => p.2) (nhds ((0 : G), y)) (nhds y) :=
      continuous_snd.tendsto _
    filter_upwards [h1.eventually hy, h2.eventually hy] with p hp1 hp2
    exact hp1.trans hp2.symm
  have step' : ∀ᶠ x in nhds (0 : G), ∀ y ∈ tsupport F, F (y - -x) = F y :=
    (continuous_neg.tendsto' (0 : G) 0 neg_zero).eventually step
  filter_upwards [step, step'] with x hx hx' g
  by_cases hg : g ∈ tsupport F
  · exact hx g hg
  · rw [hz g hg]
    by_cases hg' : g - x ∈ tsupport F
    · have h := hx' (g - x) hg'
      rw [sub_neg_eq_add, sub_add_cancel, hz g hg] at h
      exact h.symm
    · exact hz _ hg'

def translate (Ψ : SB G) (y : G) : SB G :=
  ⟨fun x => Ψ.1 (x - y), Ψ.2.1.comp_continuous (continuous_sub_right y),
    Ψ.2.2.comp_homeomorph (Homeomorph.subRight y)⟩

theorem isLocallyConstant_translate (Ψ : SB G) : IsLocallyConstant (translate Ψ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hmap : Filter.Tendsto (fun y' : G => y' - y) (nhds y) (nhds 0) := by
    simpa using (continuous_id.tendsto y).sub_const y
  filter_upwards [hmap.eventually (eventually_translate Ψ.2)] with y' hy'
  apply Subtype.ext
  funext x
  show Ψ.1 (x - y') = Ψ.1 (x - y)
  have h := hy' (x - y)
  rwa [sub_sub_sub_cancel_right] at h

theorem exists_conv [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] (Φ Ψ : SB G) :
    ∃ w : SB G, (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂μ) ∧
      ∀ l : SB G →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (translate Ψ y) ∂μ := by
  have hT : IsLocallyConstant (fun y => Φ.1 y • translate Ψ y) :=
    IsLocallyConstant.comp₂ Φ.2.1 (isLocallyConstant_translate Ψ) (fun c f => c • f)
  have hz : ∀ y, y ∉ tsupport Φ.1 → Φ.1 y • translate Ψ y = 0 := by
    intro y hy
    have h0 : Φ.1 y = 0 := by
      by_contra h
      exact hy (subset_tsupport _ h)
    rw [h0, zero_smul]
  obtain ⟨w, hw⟩ := GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact G μ (SB G)
    (fun y => Φ.1 y • translate Ψ y) hT (tsupport Φ.1) Φ.2.2.isCompact hz
  refine ⟨w, fun x => ?_, fun l => ?_⟩
  · exact hw ((LinearMap.proj x).comp (SB G).subtype)
  · rw [hw l]
    simp only [map_smul, smul_eq_mul]

end Abstract

theorem exists_convolution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (Φ Ψ : SB (n → k)), ∃ (T : (n → k) → SB (n → k)) (w : SB (n → k)), (∀ y x, (T y).1 x = Ψ.1 (x - y)) ∧ (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ (∀ x, w.1 x = ∫ y, Ψ.1 y * Φ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧ ∀ l : SB (n → k) →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (T y) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ n _ _ ν _ Φ Ψ
  have : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  have : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have : ν.Regular := inferInstance
  have : ν.IsNegInvariant := inferInstance
  obtain ⟨w, hw1, hw2⟩ := exists_conv (Measure.pi fun _ : n => ν) Φ Ψ
  refine ⟨translate Ψ, w, fun y x => rfl, hw1, fun x => ?_, hw2⟩
  rw [hw1 x]
  have h := integral_sub_left_eq_self (fun y => Φ.1 (x - y) * Ψ.1 y) (Measure.pi fun _ : n => ν) x
  simp only [sub_sub_cancel] at h
  refine h.trans ?_
  congr 1
  funext y
  exact mul_comm _ _

end GlobalTheory.SBConv
