import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FreeOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibInf

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set
open scoped TensorProduct ENNReal

namespace LocPosW

theorem pos_of_lb {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} (hι : Function.Injective ι)
    {U : Set V} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν Set.univ fib)
    {f' : V → X} (hf' : Continuous f') (hff : ∀ v, f v = ι (f' v))
    {φ : V → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hφ0 : ∀ v, 0 ≤ φ v) {W : Set V} (hWU : W ⊆ U) {δ : ℝ} (hδ : 0 < δ)
    (hWφ : ∀ v ∈ W, δ ≤ φ v) {b0 : X} {c : ℝ≥0∞} (hc : 0 < c) (hc' : c ≠ ⊤) {N : Set X}
    (hN : N ∈ 𝓝 b0) (hlb : ∀ S ⊆ N, MeasurableSet S → c * ν S ≤ μ (f ⁻¹' (ι '' S) ∩ W))
    (hνpos : ∀ O : Set X, IsOpen O → O.Nonempty → ν O ≠ 0) (hνfin : ∃ N' ∈ 𝓝 b0, ν N' < ⊤) :
    0 < ∫ v, φ v ∂(fib b0) := by
  classical
  set g : X → ℝ := fun b => ∫ v, φ v ∂(fib b) with hg
  obtain ⟨hint, hcont⟩ := hfib.2.2 φ hφc hφs hφU
  have hgc : ContinuousAt g b0 := (hcont b0 (mem_univ _)).continuousAt univ_mem
  by_contra hneg
  push Not at hneg
  set η := δ * c.toReal with hηdef
  have hη : 0 < η := mul_pos hδ (ENNReal.toReal_pos hc.ne' hc')
  obtain ⟨N', hN', hN'fin⟩ := hνfin
  have hev : ∀ᶠ b in 𝓝 b0, g b < η := hgc.eventually (Iio_mem_nhds (lt_of_le_of_lt hneg hη))
  obtain ⟨O, hOsub, hOo, hbO⟩ := mem_nhds_iff.1 (inter_mem (inter_mem hN hN') hev)
  have hOm : MeasurableSet O := hOo.measurableSet
  have hOpos : ν O ≠ 0 := hνpos O hOo ⟨b0, hbO⟩
  have hOfin : ν O ≠ ⊤ := ne_top_of_le_ne_top hN'fin.ne (measure_mono fun b hb => (hOsub hb).1.2)
  have hfO : f ⁻¹' (ι '' O) = f' ⁻¹' O := by
    ext v
    simp only [mem_preimage, mem_image, hff, hι.eq_iff, exists_eq_right]
  let ψ : V → ℝ≥0∞ := (f ⁻¹' (ι '' O)).indicator (fun v => ENNReal.ofReal (φ v))
  have hψm : Measurable ψ := by
    refine Measurable.indicator (ENNReal.measurable_ofReal.comp hφc.measurable) ?_
    rw [hfO]
    exact hf'.measurable hOm
  have hdis := hfib.2.1 ψ hψm
  have hin : ∀ b, ∫⁻ v, ψ v ∂(fib b) = O.indicator (fun b => ENNReal.ofReal (g b)) b := by
    intro b
    have hnull := hfib.1 b
    by_cases hb : b ∈ O
    · rw [indicator_of_mem hb]
      have hae : ψ =ᵐ[fib b] fun v => ENNReal.ofReal (φ v) := by
        refine ae_iff.2 (measure_mono_null (fun v hv => ?_) hnull)
        intro hvin
        apply hv
        have h1 : f v = ι b := hvin.1
        have h2 : f' v = b := hι (by rw [← hff]; exact h1)
        have h3 : v ∈ f ⁻¹' (ι '' O) := by rw [hfO]; show f' v ∈ O; rw [h2]; exact hb
        exact indicator_of_mem h3 _
      rw [lintegral_congr_ae hae,
        ← ofReal_integral_eq_lintegral_ofReal (hint b (mem_univ b)) (ae_of_all _ hφ0)]
    · rw [indicator_of_notMem hb]
      have hae : ψ =ᵐ[fib b] 0 := by
        refine ae_iff.2 (measure_mono_null (fun v hv => ?_) hnull)
        intro hvin
        apply hv
        have h1 : f v = ι b := hvin.1
        have h2 : f' v = b := hι (by rw [← hff]; exact h1)
        have h3 : v ∉ f ⁻¹' (ι '' O) := by rw [hfO]; show f' v ∉ O; rw [h2]; exact hb
        exact indicator_of_notMem h3 _
      rw [lintegral_congr_ae hae]
      simp
  simp_rw [hin] at hdis
  rw [lintegral_indicator hOm] at hdis
  have hup : ∫⁻ b in O, ENNReal.ofReal (g b) ∂ν < ∫⁻ b in O, ENNReal.ofReal η ∂ν := by
    have hle : ∫⁻ b in O, ENNReal.ofReal (g b) ∂ν ≤ ∫⁻ b in O, ENNReal.ofReal η ∂ν :=
      setLIntegral_mono measurable_const fun b hb => ENNReal.ofReal_le_ofReal (hOsub hb).2.le
    refine setLIntegral_strict_mono hOm hOpos measurable_const ?_ (ae_of_all _ fun b hb => ?_)
    · refine ne_top_of_le_ne_top ?_ hle
      rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hOfin
    · exact (ENNReal.ofReal_lt_ofReal_iff hη).2 (hOsub hb).2
  rw [setLIntegral_const] at hup
  have hlow : ENNReal.ofReal η * ν O ≤ ∫⁻ v in U, ψ v ∂μ := by
    calc ENNReal.ofReal η * ν O = ENNReal.ofReal δ * (c * ν O) := by
          rw [hηdef, ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_toReal hc', mul_assoc]
      _ ≤ ENNReal.ofReal δ * μ (f ⁻¹' (ι '' O) ∩ W) :=
          mul_le_mul_right (hlb O (fun b hb => (hOsub hb).1.1) hOm) _
      _ = ∫⁻ v in f ⁻¹' (ι '' O) ∩ W, ENNReal.ofReal δ ∂μ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ v in f ⁻¹' (ι '' O) ∩ W, ψ v ∂μ :=
          setLIntegral_mono hψm fun v hv => by
            show ENNReal.ofReal δ ≤ (f ⁻¹' (ι '' O)).indicator (fun v => ENNReal.ofReal (φ v)) v
            rw [indicator_of_mem hv.1]
            exact ENNReal.ofReal_le_ofReal (hWφ v hv.2)
      _ ≤ ∫⁻ v in U, ψ v ∂μ := lintegral_mono_set (inter_subset_right.trans hWU)
  rw [hdis] at hlow
  exact lt_irrefl _ (hlow.trans_lt hup)

theorem gramR_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X0 : Fin n → Fin M → E) :
    gramR R σ J (ratTup R X0) = (gramE σ J X0).map (inclR R) := by
  have hs : ∀ e : E, sigR R σ (inclR R e) = inclR R (σ e) := fun e => by
    simp [sigR, inclR, Algebra.TensorProduct.map_tmul]
  ext p q
  simp only [gramR, hR, gramE, hE, Formalism.UG.hform, Matrix.map_apply, ratTup, JR, map_sum, map_mul, hs]
  rfl

end LocPosW

open LocPosW

def LBInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ (μinf : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a)),
    μinf.IsAddHaarMeasure → νinf.IsAddHaarMeasure →
    ∀ W : Set (Fin a → Fin M → Ainf F ⊗[F] E), IsOpen W → ratTup (F := F) (Ainf F) X0 ∈ W →
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 (hermOf (Ainf F) σ (gramE σ J X0) hT),
      ∀ S ⊆ N, MeasurableSet S →
        c * νinf S ≤ μinf ((gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W)

theorem archPos_of_lb (hL : LBInf) : ArchPos := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ νinf hν fibInf hfib
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    (tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Ainf F) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (HermR (Ainf F) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set X1 := ratTup (F := F) (Ainf F) X0 with hX1
  have hX1U : X1 ∈ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    linIndep_of_isUnit_det (Ainf F) σ J X1
      (by rw [gramR_ratTup]; exact isUnit_det_hermOf (Ainf F) σ _ hT hdet)
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset t7 hX1U
  obtain ⟨φ, hφ1, hφ0, hφc, hφr⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := X1)) isOpen_interior.isClosed_compl
    (disjoint_singleton_left.2 fun h => h hxK)
  have hsupp : Function.support φ ⊆ interior K := fun X hX => by
    by_contra h
    exact hX (hφ0 h)
  have hts : tsupport φ ⊆ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    (closure_mono hsupp).trans ((closure_minimal interior_subset hK.isClosed).trans hKU)
  let W : Set (Fin a → Fin M → Ainf F ⊗[F] E) := {X | (1 / 2 : ℝ) < φ X}
  have hWo : IsOpen W := isOpen_lt continuous_const φ.continuous
  have hX1W : X1 ∈ W := by
    show (1 / 2 : ℝ) < φ X1
    rw [hφ1 (mem_singleton X1)]
    norm_num
  have hWU : W ⊆ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    fun X hX => hts (subset_tsupport _ (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hX).ne')
  obtain ⟨c, hc0, hctop, N, hN, hlb⟩ :=
    hL F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet μinf νinf hμ.1 hν.1 W hWo hX1W
  have hpos := pos_of_lb (f' := gramH (Ainf F) σ hσ J hJ.1) Subtype.val_injective hfib
    (continuous_gramH (Ainf F) σ hσ J hJ.1) (fun _ => rfl) φ.continuous hφc hts
    (fun X => (hφr X).1) hWU (by norm_num : (0 : ℝ) < 1 / 2) (fun X hX => hX.le) hc0 hctop hN hlb
    (fun O hO hne => (hO.measure_pos νinf hne).ne') (νinf.finiteAt_nhds _)
  refine ⟨fun X => ((φ X : ℝ) : ℂ), Complex.continuous_ofReal.comp φ.continuous,
    hφc.comp_left Complex.ofReal_zero, ?_⟩
  rw [integral_complex_ofReal]
  exact_mod_cast hpos.ne'

end PI.VolStabS
