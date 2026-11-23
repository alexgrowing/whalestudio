import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeBump

theorem integral_indicator_disp_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (X : Spc F E n) (x₀ : Fin n → E) (K : Subgroup (UA σ X.J)) (v : Pl F) (μK : Measure (KAt K (evFin F v)))
    (μ : Measure (idelesAt E (evFin F v))), IsNormK K (evFin F v) μK → IsNormE E v μ →
    ∀ V : Set (Fin n → Fv F v ⊗[F] E), IsOpen V → IsClosed V → (0 : Fin n → Fv F v ⊗[F] E) ∈ V →
    ∀ C : Set (idelesAt E (evFin F v)), IsCompact C →
      (∀ p : KAt K (evFin F v) × idelesAt E (evFin F v), GlobalTheory.ConeBump.disp v x₀ p.1.1 p.2.1 ∈ V → p.2 ∈ C) →
      (∫ k, ∫ l, V.indicator (fun _ => (1 : ℂ)) (GlobalTheory.ConeBump.disp v x₀ k.1 l.1) ∂μ ∂μK) ≠ 0 := by
  intro F E _ _ _ _ _ σ n X x₀ K v μK μ hK hμ V hVo hVc hV0 C hC hsub
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI := hK.1
  haveI := hμ.1
  haveI : IsFiniteMeasure μK := ⟨by rw [hK.2]; exact ENNReal.one_lt_top⟩
  have hcf : Continuous (compFin F E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
      ((RestrictedProduct.continuous_eval v).comp continuous_snd)
  have hm : Continuous fun g : UA σ X.J => mat g⁻¹ := Units.continuous_coe_inv.comp continuous_subtype_val
  have hD : Continuous fun p : KAt K (evFin F v) × idelesAt E (evFin F v) => disp v x₀ p.1.1 p.2.1 := by
    refine continuous_pi fun i => ?_
    refine Continuous.sub (hcf.comp ?_) continuous_const
    refine (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).mul ?_
    exact (continuous_apply i).comp
      ((hm.comp (continuous_subtype_val.comp continuous_fst)).matrix_mulVec continuous_const)
  set S : KAt K (evFin F v) → Set (idelesAt E (evFin F v)) := fun k => {l | disp v x₀ k.1 l.1 ∈ V} with hSdef
  have hSC : ∀ k, S k ⊆ C := fun k l hl => hsub (k, l) hl
  have hSo : ∀ k, IsOpen (S k) := fun k => hVo.preimage (hD.comp (Continuous.prodMk_right k))
  have hCfin : μ C ≠ ⊤ := hC.measure_lt_top.ne
  have hinner : ∀ k : KAt K (evFin F v),
      ∫ l, V.indicator (fun _ => (1 : ℂ)) (disp v x₀ k.1 l.1) ∂μ = ((μ.real (S k) : ℝ) : ℂ) := fun k => by
    have e : (fun l : idelesAt E (evFin F v) => V.indicator (fun _ => (1 : ℂ)) (disp v x₀ k.1 l.1)) =
        (S k).indicator fun _ => (1 : ℂ) := by
      funext l
      by_cases h : disp v x₀ k.1 l.1 ∈ V
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show l ∈ S k from h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show l ∉ S k from h)]
    rw [e, integral_indicator_const _ (hSo k).measurableSet, Complex.real_smul, mul_one]

  have hloc : ∀ k₀ : KAt K (evFin F v), ∀ᶠ k in 𝓝 k₀, S k = S k₀ := by
    intro k₀
    have h : ∀ᶠ k in 𝓝 k₀, ∀ l ∈ C, (disp v x₀ k.1 l.1 ∈ V ↔ disp v x₀ k₀.1 l.1 ∈ V) := by
      refine hC.eventually_forall_of_forall_eventually fun l _ => ?_
      have h2c : Continuous fun z : KAt K (evFin F v) × idelesAt E (evFin F v) => disp v x₀ k₀.1 z.2.1 :=
        hD.comp (continuous_const.prodMk continuous_snd)
      by_cases hl : disp v x₀ k₀.1 l.1 ∈ V
      · have h1 := hD.continuousAt (x := (k₀, l)) |>.preimage_mem_nhds (hVo.mem_nhds hl)
        have h2 := h2c.continuousAt (x := (k₀, l)) |>.preimage_mem_nhds (hVo.mem_nhds hl)
        filter_upwards [h1, h2] with z a b
        exact iff_of_true a b
      · have h1 := hD.continuousAt (x := (k₀, l)) |>.preimage_mem_nhds (hVc.isOpen_compl.mem_nhds hl)
        have h2 := h2c.continuousAt (x := (k₀, l)) |>.preimage_mem_nhds (hVc.isOpen_compl.mem_nhds hl)
        filter_upwards [h1, h2] with z a b
        exact iff_of_false a b
    filter_upwards [h] with k hk
    ext l
    exact ⟨fun hl => (hk l (hSC k hl)).1 hl, fun hl => (hk l (hSC k₀ hl)).2 hl⟩
  set g : KAt K (evFin F v) → ℝ := fun k => μ.real (S k) with hgdef
  have hg : Continuous g := continuous_iff_continuousAt.2 fun k₀ =>
    continuousAt_const.congr (by filter_upwards [hloc k₀] with k hk; exact (congrArg μ.real hk).symm)
  have hg0 : ∀ k, 0 ≤ g k := fun k => measureReal_nonneg
  have hgC : ∀ k, g k ≤ μ.real C := fun k => measureReal_mono (hSC k) hCfin
  have hg1 : 0 < g 1 := by
    have h1 : (1 : idelesAt E (evFin F v)) ∈ S 1 := by
      show disp v x₀ (1 : UA σ X.J) 1 ∈ V
      rw [disp_one_one]
      exact hV0
    have hpos : 0 < μ (S 1) := (hSo 1).measure_pos μ ⟨1, h1⟩
    exact ENNReal.toReal_pos hpos.ne' (ne_top_of_le_ne_top hCfin (measure_mono (hSC 1)))
  have hint : Integrable g μK :=
    (integrable_const (μ.real C)).mono' hg.aestronglyMeasurable
      (Eventually.of_forall fun k => by rw [Real.norm_of_nonneg (hg0 k)]; exact hgC k)
  have hpos : 0 < ∫ k, g k ∂μK := by
    rw [integral_pos_iff_support_of_nonneg hg0 hint]
    exact hg.isOpen_support.measure_pos μK ⟨1, hg1.ne'⟩
  have e : (∫ k, ∫ l, V.indicator (fun _ => (1 : ℂ)) (disp v x₀ k.1 l.1) ∂μ ∂μK) = ((∫ k, g k ∂μK : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun k => hinner k)
  rw [e]
  exact Complex.ofReal_ne_zero.2 hpos.ne'

end GlobalTheory.ConeBump

end
