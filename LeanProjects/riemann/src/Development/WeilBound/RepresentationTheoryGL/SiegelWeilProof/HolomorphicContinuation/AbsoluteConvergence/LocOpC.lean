import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SphericalCharacterInvCompact

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw LocOpA

variable {n : ℕ}

def fLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (y : KR n × (Fin n → Fin n → ℝ)) (w : ℂ) : ℂ :=
  (F0 p q e (y.1 : GR n))⁻¹ * (((hLoc ((y.1 : GR n) * A * nbEl y.2 * B) : ℂ) ^ w *
    F0 p q e ((y.1 : GR n) * A * nbEl y.2 * B)) * ψ y.2)

theorem continuous_fLoc (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) :
    Continuous (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ => fLoc p q e A B ψ y.1 y.2) := by
  have hg : Continuous (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ => ((y.1.1 : GR n) * A * nbEl y.1.2 * B)) :=
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul continuous_const).mul
      (continuous_nbEl.comp (continuous_snd.comp continuous_fst))).mul continuous_const
  unfold fLoc
  refine (((continuous_weight_factor p q e).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))).inv₀
    (fun _ => weight_factor_ne_zero _ _ _ _)).mul ?_
  refine ((Continuous.cpow ?_ continuous_snd ?_).mul ((continuous_weight_factor p q e).comp hg)).mul
    (hψ.comp (continuous_snd.comp continuous_fst))
  · exact Complex.continuous_ofReal.comp (continuous_hLoc.comp hg)
  · intro y
    exact Complex.ofReal_mem_slitPlane.2 (hLoc_pos _)

theorem continuous_fLoc_w (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) (w : ℂ) :
    Continuous (fun y : KR n × (Fin n → Fin n → ℝ) => fLoc p q e A B ψ y w) := by
  have h1 := continuous_fLoc p q e A B hψ
  have h2 : Continuous (fun y : KR n × (Fin n → Fin n → ℝ) => ((y, w) : (KR n × (Fin n → Fin n → ℝ)) × ℂ)) :=
    continuous_id.prodMk continuous_const
  have h3 := h1.comp h2
  exact h3

theorem cz_eq (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [IsProbabilityMeasure μ] (w : ℂ) :
    czLoc p q e A B ψ μ w =
      ∫ y, fLoc p q e A B ψ y w ∂((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) := by
  have hK : IsCompact ((univ : Set (KR n)) ×ˢ tsupport ψ) := isCompact_univ.prod hψ.2.1
  have hint : Integrable (fun y => fLoc p q e A B ψ y w) ((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) :=
    ((continuous_fLoc_w p q e A B hψ.1 w).continuousOn).integrableOn_compact hK
  rw [← Measure.prod_restrict, Measure.restrict_univ] at hint ⊢
  rw [integral_prod _ hint]
  unfold czLoc jLoc
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [fLoc]
  rw [integral_const_mul]
  congr 1
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
  have h0 : ψ x = 0 := by
    by_contra h
    exact hx (subset_tsupport ψ (Function.mem_support.2 h))
  simp [h0]

theorem cz_diff (hH : HolParam) (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [IsProbabilityMeasure μ] :
    Differentiable ℂ (czLoc p q e A B ψ μ) := by
  have hK : IsCompact ((univ : Set (KR n)) ×ˢ tsupport ψ) := isCompact_univ.prod hψ.2.1
  have hmeas : MeasurableSet ((univ : Set (KR n)) ×ˢ tsupport ψ) :=
    MeasurableSet.univ.prod (isClosed_tsupport ψ).measurableSet
  haveI : IsFiniteMeasure ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, Measure.prod_prod]
      exact ENNReal.mul_lt_top (measure_lt_top _ _) hψ.2.1.measure_lt_top⟩
  have hnull : ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ))
      ((univ : Set (KR n)) ×ˢ tsupport ψ)ᶜ = 0 := by
    rw [Measure.restrict_apply' hmeas, compl_inter_self, measure_empty]
  have hcont := (continuous_fLoc p q e A B hψ.1).continuousOn (s := ((univ : Set (KR n)) ×ˢ tsupport ψ) ×ˢ (univ : Set ℂ))
  have hdiff : ∀ y ∈ ((univ : Set (KR n)) ×ˢ tsupport ψ),
      DifferentiableOn ℂ (fun w => fLoc p q e A B ψ y w) univ := by
    intro y _
    refine Differentiable.differentiableOn ?_
    unfold fLoc
    refine Differentiable.const_mul ?_ _
    refine Differentiable.mul_const ?_ _
    refine Differentiable.mul_const ?_ _
    refine Differentiable.const_cpow differentiable_id (Or.inl ?_)
    exact_mod_cast (hLoc_pos _).ne'
  have h := (hH (KR n × (Fin n → Fin n → ℝ)) ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ))
    _ hK hnull univ (fun y w => fLoc p q e A B ψ y w) isOpen_univ hcont hdiff).1
  have heq : czLoc p q e A B ψ μ = fun w =>
      ∫ y, fLoc p q e A B ψ y w ∂((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) :=
    funext (cz_eq p q e A B hψ μ)
  rw [heq]
  exact differentiableOn_univ.1 h

set_option maxHeartbeats 800000 in
theorem locOp : LV → Iwa → Mult → HolParam → LocOp := by
  intro hLV hIwa hMult hHol n p q e hgood _ _ μ _ _
  let ι : KR n →* M2 n := (Units.coeHom (M2 n)).comp ((GR n).subtype.comp (KR n).subtype)
  have hι : Continuous ι := continuous_mR.comp continuous_subtype_val
  have hιs : ∀ g : M2 n, InK g ↔ ∃ k, ι k = g := by
    intro g
    constructor
    · intro hg
      exact ⟨kOf ⟨g, hg⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2
  obtain ⟨ψ, a, b, hψ, ha, hb, hne⟩ := hLV n p q hgood (KR n) μ ι hι hιs
  refine ⟨ψ, mkG a ha, mkG b hb, nbEl, czLoc p q e (mkG a ha) (mkG b hb) ψ μ, hψ, fun x => rfl, continuous_nbEl,
    cz_diff hHol p q e _ _ hψ μ, ?_, fun w y => eigen hIwa hMult p q e _ _ ψ μ w y⟩
  rw [cz_zero]
  refine mul_ne_zero (zpow_ne_zero _ (mul_ne_zero (det_mR_ne (mkG a ha)) (det_mR_ne (mkG b hb)))) ?_
  exact hne

end PositivityTheory.Rg.Sw.AbsSt
