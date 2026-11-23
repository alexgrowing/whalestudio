import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut

namespace Formalism.L2.SG.Pf

variable {D : D7} (X : HidaSetting D)

theorem fundBridge_holds : FundBridge X := by
  haveI := X.B.sf
  haveI := X.B.haar
  haveI := Formalism.L2.SG.Count.muA_isHaar X.B.I X.B.μf
  show IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) X.B.fund (X.B.I.muA X.B.μf)
  obtain ⟨hmeas, hcov, hdisj⟩ := X.B.fund_spec
  refine IsFundamentalDomain.mk'' hmeas.nullMeasurableSet
    (Filter.Eventually.of_forall fun y => ?_) (fun g hg => ?_) (fun g => ?_)
  · obtain ⟨γ, hγ, hy⟩ := hcov y
    exact ⟨⟨γ, hγ⟩, hy⟩
  · have hg' : (g : X.B.I.GA) ≠ 1 := fun h => hg (Subtype.ext h)
    exact hdisj g g.2 hg'
  · exact (measurePreserving_mul_left (X.B.I.muA X.B.μf) (g : X.B.I.GA)).quasiMeasurePreserving

theorem pserMeas_holds (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) : PserMeas X u hK := by
  intro hPM T Dt hDt hsum
  classical
  have hG : (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I : Set X.B.I.GA).Countable :=
    Set.countable_coe_iff.mp (by exact (inferInstance : Countable (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I)))
  have hc : Dt.Countable := Set.Countable.mono hDt.1 hG
  haveI : Countable Dt := hc.to_subtype
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset Dt))
    (f := fun (s : Finset Dt) x => ∑ δ ∈ s, Ph X u hK T ((δ : X.B.I.GA) * x)) (fun s => ?_) ?_
  · exact Finset.measurable_sum s fun δ _ => (hPM T).comp (measurable_const_mul _)
  · refine tendsto_pi_nhds.mpr fun x => ?_
    exact (Summable.of_norm (hsum x)).hasSum

namespace InHHLeaf

open MeasureTheory Set Formalism.MainNotions.LeviCoordinates
open scoped ENNReal InnerProductSpace

variable {G H : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G} [MeasurableSpace H] {ν : Measure H} [SigmaFinite ν]

theorem step_sub (h : rr_FD μ Γ D) (ι : H → G) (hι : Measurable ι) {φ : H → ℂ} (hφm : Measurable φ)
    {r : G → G} (hrm : Measurable r) (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D)
    {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))} (hR : rr_IsReg μ Γ D R)
    (T : Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D)) (hφ : Integrable φ ν)
    (hT : ∀ u v : Lp ℂ 2 (μ.restrict D), ⟪u, T v⟫_ℂ = ∫ k, φ k * ⟪u, R (ι k) v⟫_ℂ ∂ν) (f : Lp ℂ 2 (μ.restrict D))
    (f0 : G → ℂ) (hf0m : Measurable f0) (hf0 : (f : G → ℂ) =ᵐ[μ.restrict D] f0) :
    ((T f : Lp ℂ 2 (μ.restrict D)) : G → ℂ) =ᵐ[μ.restrict D] fun x => ∫ k, φ k * f0 (r (x * ι k)) ∂ν := by
  set Φ : H × G → ℂ := fun p => φ p.1 * f0 (r (p.2 * ι p.1)) with hΦ
  have hΦm : StronglyMeasurable Φ :=
    ((hφm.comp measurable_fst).stronglyMeasurable).mul
      ((hf0m.comp (hrm.comp (measurable_snd.mul (hι.comp measurable_fst)))).stronglyMeasurable)
  have hsq : ∫⁻ y in D, ‖f0 y‖ₑ ^ 2 ∂μ ≠ ∞ := by
    have e : ∫⁻ y in D, ‖(f : G → ℂ) y‖ₑ ^ 2 ∂μ = ∫⁻ y in D, ‖f0 y‖ₑ ^ 2 ∂μ :=
      lintegral_congr_ae (hf0.mono fun x hx => by simp only [hx])
    rw [← e]; exact rrkb_sq_fin f
  have hInt : ∀ s, MeasurableSet s → (μ.restrict D) s < ∞ →
      Integrable Φ (ν.prod ((μ.restrict D).restrict s)) := by
    intro s hs hfin
    refine ⟨hΦm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hΦm.enorm.aemeasurable]
    set C : ℝ≥0∞ := (μ.restrict D) s + ∫⁻ y in D, ‖f0 y‖ₑ ^ 2 ∂μ with hC
    have hCfin : C ≠ ∞ := ENNReal.add_ne_top.2 ⟨hfin.ne, hsq⟩
    have hb : ∀ g, ∫⁻ x, ‖Φ (g, x)‖ₑ ∂((μ.restrict D).restrict s) ≤ ‖φ g‖ₑ * C := by
      intro g
      have hm1 : Measurable fun x => ‖f0 (r (x * ι g))‖ₑ :=
        (hf0m.comp (hrm.comp (measurable_mul_const (ι g)))).enorm
      simp only [hΦ, enorm_mul]
      rw [lintegral_const_mul _ hm1]
      refine mul_le_mul' le_rfl ?_
      calc ∫⁻ x, ‖f0 (r (x * ι g))‖ₑ ∂((μ.restrict D).restrict s)
          ≤ ∫⁻ x, (1 + ‖f0 (r (x * ι g))‖ₑ ^ 2) ∂((μ.restrict D).restrict s) :=
            lintegral_mono fun x => rrkb_le_one_add_sq _
        _ = (μ.restrict D) s + ∫⁻ x, ‖f0 (r (x * ι g))‖ₑ ^ 2 ∂((μ.restrict D).restrict s) := by
            rw [lintegral_add_left measurable_const, lintegral_one, Measure.restrict_apply_univ]
        _ ≤ (μ.restrict D) s + ∫⁻ x in D, ‖f0 (r (x * ι g))‖ₑ ^ 2 ∂μ :=
            add_le_add le_rfl (lintegral_mono' Measure.restrict_le_self le_rfl)
        _ = C := by rw [rrkb_lint h hr (ι g) (F := fun y => ‖f0 y‖ₑ ^ 2) (hf0m.enorm.pow_const 2)]
    calc ∫⁻ g, ∫⁻ x, ‖Φ (g, x)‖ₑ ∂((μ.restrict D).restrict s) ∂ν ≤ ∫⁻ g, ‖φ g‖ₑ * C ∂ν := lintegral_mono hb
      _ = (∫⁻ g, ‖φ g‖ₑ ∂ν) * C := lintegral_mul_const _ hφm.enorm
      _ < ∞ := ENNReal.mul_lt_top hφ.2 (lt_top_iff_ne_top.2 hCfin)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
  · intro s hs hfin
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hfin.ne
  · intro s hs hfin
    exact (hInt s hs hfin).integral_prod_right
  · intro s hs hfin
    rw [← L2.inner_indicatorConstLp_one (𝕜 := ℂ) hs hfin.ne (T f), hT]
    have e : ∀ g, ⟪indicatorConstLp 2 hs hfin.ne (1 : ℂ), R (ι g) f⟫_ℂ =
        ∫ x in s, f0 (r (x * ι g)) ∂(μ.restrict D) := by
      intro g
      rw [L2.inner_indicatorConstLp_one]
      refine integral_congr_ae (ae_restrict_of_ae ?_)
      have hmap := rr_map h (ι g)
      have h3 : (fun x => (f : G → ℂ) (rr_rep (Γ : Set G) D (x * ι g))) =ᵐ[μ.restrict D]
          fun x => f0 (rr_rep (Γ : Set G) D (x * ι g)) := by
        show ∀ᵐ x ∂(μ.restrict D), (f : G → ℂ) (rr_rep (Γ : Set G) D (x * ι g)) = f0 (rr_rep (Γ : Set G) D (x * ι g))
        refine ae_of_ae_map (p := fun y => (f : G → ℂ) y = f0 y) hmap.1 ?_
        rw [hmap.2]
        exact hf0
      filter_upwards [hR (ι g) f, h3, ae_restrict_of_ae (s := D) (rr_rep_ae_eq h hr (ι g))] with x a1 a2 a3
      rw [a1, a2, a3]
    simp only [e]
    have hsw := integral_integral_swap (f := fun g x => φ g * f0 (r (x * ι g))) (μ := ν)
      (ν := (μ.restrict D).restrict s) (hInt s hs hfin)
    rw [← hsw]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact (integral_const_mul _ _).symm

end InHHLeaf

namespace InHHLeaf

open MeasureTheory Set Formalism.MainNotions.LeviCoordinates
open scoped ENNReal InnerProductSpace

variable {G H : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G} [MeasurableSpace H] {ν : Measure H} [SigmaFinite ν]

theorem fix_of (h : rr_FD μ Γ D) (ι : H → G) (hι : Measurable ι) {φ : H → ℂ} (hφ : Integrable φ ν)
    {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))} (hR : rr_IsReg μ Γ D R)
    (T : Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))
    (hT : ∀ u v : Lp ℂ 2 (μ.restrict D), ⟪u, T v⟫_ℂ = ∫ k, φ k * ⟪u, R (ι k) v⟫_ℂ ∂ν)
    (f0 : G → ℂ) (hf0m : Measurable f0) (hinv : ∀ γ ∈ Γ, ∀ y, f0 (γ * y) = f0 y)
    (hm : MemLp f0 2 (μ.restrict D)) (hfix : ∀ᵐ y ∂μ, ∫ k, φ k * f0 (y * ι k) ∂ν = f0 y) :
    T (hm.toLp f0) = hm.toLp f0 := by
  set φ' := hφ.1.aemeasurable.mk φ with hφ'
  have hφ'm : Measurable φ' := hφ.1.aemeasurable.measurable_mk
  have hφφ' : φ =ᵐ[ν] φ' := hφ.1.aemeasurable.ae_eq_mk
  have hφ'i : Integrable φ' ν := hφ.congr hφφ'
  have hT' : ∀ u v : Lp ℂ 2 (μ.restrict D), ⟪u, T v⟫_ℂ = ∫ k, φ' k * ⟪u, R (ι k) v⟫_ℂ ∂ν := by
    intro u v
    rw [hT]
    exact integral_congr_ae (hφφ'.mono fun k hk => by simp only [hk])
  obtain ⟨r, hrm, hr⟩ := rr_exists_meas_rep h
  have hs := step_sub h ι hι hφ'm hrm hr hR T hφ'i hT' (hm.toLp f0) f0 hf0m (MemLp.coeFn_toLp hm)
  have hr' : ∀ z, f0 (r z) = f0 z := by
    intro z
    obtain ⟨γ, hγ, e1, -⟩ := hr z
    rw [e1, hinv γ hγ z]
  refine Lp.ext ?_
  filter_upwards [hs, MemLp.coeFn_toLp hm, ae_restrict_of_ae hfix] with x a1 a2 a3
  rw [a1, a2, ← a3]
  refine integral_congr_ae (hφφ'.mono fun k hk => ?_)
  simp only [hr', hk]

end InHHLeaf

section Fix

open MeasureTheory Formalism.MainNotions.LeviCoordinates

variable {D : D7} (X : HidaSetting D)

theorem muf_right : X.B.μf.IsMulRightInvariant := by
  haveI := X.B.sf
  haveI := X.B.haar
  exact Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf

theorem idempotent_fixes_invariant_L2 : IdempotentFixesInvariantL2 X := by
  intro f hf hinv hm hfix
  have := X.B.sf
  have := X.B.haar
  have := gf_secondCountable X.B.I
  have := muf_right X
  have := rr_muA_sigmaFinite X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  have := rr_muA_right X.B.I X.B.μf
  exact InHHLeaf.fix_of (rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec) (fun g => ((1 : X.B.I.Ginf), g))
    (measurable_const.prodMk measurable_id) X.B.Re_spec.1 (rr_IsReg_of X.B.I X.B.μf X.B.fund X.B.R X.B.R_spec)
    X.B.Re X.B.Re_spec.2 f hf hinv hm hfix

theorem regular_fixes_invariant_L2 : ArchimedeanConvolutionFixesInvariantL2 X := by
  intro f hf hinv hm hPI hfix
  have := X.B.sf
  have := X.B.haar
  have := gf_secondCountable X.B.I
  have := muf_right X
  have := rr_muA_sigmaFinite X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  have := rr_muA_right X.B.I X.B.μf
  exact InHHLeaf.fix_of (rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec) (fun y => (y, (1 : X.B.I.Gf)))
    (measurable_id.prodMk measurable_const) hPI (rr_IsReg_of X.B.I X.B.μf X.B.fund X.B.R X.B.R_spec)
    X.Rph X.Rph_spec f hf hinv hm hfix

end Fix

namespace InHHLeaf

open MeasureTheory Set Formalism.MainNotions.LeviCoordinates
open scoped ENNReal Pointwise

section Unfold

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}

theorem poincE_left_inv (S : Subgroup G) (Dt : Set G) (hD : FoldBound.IsRightTransversal Γ S Dt)
    (f : G → ℝ≥0∞) (hinv : ∀ s ∈ S, ∀ y, f (s * y) = f y) (γ : G) (hγ : γ ∈ Γ) (x : G) :
    ∑' δ : Dt, f ((δ : G) * (γ * x)) = ∑' δ : Dt, f ((δ : G) * x) := by
  classical
  have key : ∀ (a : G), a ∈ Γ → ∀ p q : S × Dt, ((p.1 : G) * (p.2 : G)) = a →
      ((q.1 : G) * (q.2 : G)) = a → p = q :=
    fun a ha p q hp hq => (hD.2 a ha).unique hp hq
  have hex : ∀ δ : Dt, ∃! p : S × Dt, ((p.1 : G) * (p.2 : G)) = (δ : G) * γ := fun δ =>
    hD.2 _ (Γ.mul_mem (hD.1 δ.2) hγ)
  choose φ hφ _ using hex
  have hinj : Function.Injective (fun δ => (φ δ).2) := by
    intro δ1 δ2 h
    have h' : (φ δ1).2 = (φ δ2).2 := h
    have e1 : (δ1 : G) = (φ δ1).1 * (φ δ1).2 * γ⁻¹ := by rw [hφ δ1]; group
    have e2 : (δ2 : G) = (φ δ2).1 * (φ δ2).2 * γ⁻¹ := by rw [hφ δ2]; group
    have hpq := key (δ1 : G) (hD.1 δ1.2) ((φ δ1).1 * (φ δ2).1⁻¹, δ2) (1, δ1) ?_ (by simp)
    · exact (congrArg Prod.snd hpq).symm
    · show (((φ δ1).1 * (φ δ2).1⁻¹ : S) : G) * (δ2 : G) = δ1
      rw [Subgroup.coe_mul, Subgroup.coe_inv, e1, e2, h']
      group
  have hsurj : Function.Surjective (fun δ => (φ δ).2) := by
    intro d
    obtain ⟨p, hp, -⟩ := hD.2 ((d : G) * γ⁻¹) (Γ.mul_mem (hD.1 d.2) (Γ.inv_mem hγ))
    refine ⟨p.2, ?_⟩
    have hq := key ((p.2 : G) * γ) (Γ.mul_mem (hD.1 p.2.2) hγ) (φ p.2) (p.1⁻¹, d) (hφ p.2) ?_
    · show (φ p.2).2 = d
      rw [hq]
    · show ((p.1⁻¹ : S) : G) * (d : G) = p.2 * γ
      have hd : (d : G) = p.1 * p.2 * γ := by rw [hp]; group
      rw [hd, Subgroup.coe_inv]
      group
  calc ∑' δ : Dt, f ((δ : G) * (γ * x)) = ∑' δ : Dt, f (((φ δ).2 : G) * x) := by
        refine tsum_congr fun δ => ?_
        rw [← mul_assoc, ← hφ δ, mul_assoc]
        exact hinv _ (φ δ).1.2 _
    _ = ∑' d : Dt, f ((d : G) * x) :=
        (Equiv.ofBijective _ ⟨hinj, hsurj⟩).tsum_eq (fun d : Dt => f ((d : G) * x))

theorem img_mul (δ : G) (A : Set G) : (fun y => δ * y) '' A = (fun y => δ⁻¹ * y) ⁻¹' A := by
  exact Set.image_mul_left

theorem rr_FD_union (h : rr_FD μ Γ D) (S : Subgroup G) (hS : S ≤ Γ) (Dt : Set G)
    (hD : FoldBound.IsRightTransversal Γ S Dt) (hDc : Dt.Countable) : rr_FD μ S (⋃ δ ∈ Dt, (fun y => δ * y) '' D) := by
  classical
  have hsΓ : ∀ s ∈ S, s ∈ Γ := fun s hs => hS hs
  refine ⟨?_, ?_, ?_⟩
  · exact MeasurableSet.biUnion hDc fun δ _ => by
      rw [img_mul]
      exact h.meas.preimage (measurable_const_mul _)
  · intro y
    obtain ⟨γ, hγ, hγy⟩ := h.cov y
    obtain ⟨⟨⟨s, hs⟩, ⟨δ, hδ⟩⟩, hsδ, -⟩ := hD.2 γ⁻¹ (Γ.inv_mem hγ)
    change s * δ = γ⁻¹ at hsδ
    refine ⟨s⁻¹, S.inv_mem hs, Set.mem_biUnion hδ ⟨γ * y, hγy, ?_⟩⟩
    show δ * (γ * y) = s⁻¹ * y
    have hδe : δ = s⁻¹ * γ⁻¹ := by rw [← hsδ]; group
    rw [hδe]
    group
  · intro s hs hs1
    refine measure_mono_null (t := ⋃ δ ∈ Dt, ⋃ δ' ∈ Dt,
      (fun y => δ' * y) '' ((fun y => (δ'⁻¹ * s * δ) * y) '' D ∩ D)) ?_ ?_
    · rintro x ⟨⟨u, hu, rfl⟩, hx⟩
      obtain ⟨δ, hδ, d, hd, rfl⟩ := Set.mem_iUnion₂.mp hu
      obtain ⟨δ', hδ', d', hd', hx'⟩ := Set.mem_iUnion₂.mp hx
      have hx'' : δ' * d' = s * (δ * d) := hx'
      refine Set.mem_iUnion₂.mpr ⟨δ, hδ, Set.mem_iUnion₂.mpr ⟨δ', hδ', d', ⟨⟨d, hd, ?_⟩, hd'⟩, hx'⟩⟩
      show δ'⁻¹ * s * δ * d = d'
      have hd'e : d' = δ'⁻¹ * (s * (δ * d)) := by rw [← hx'']; group
      rw [hd'e]
      group
    · refine (measure_biUnion_null_iff hDc).mpr fun δ hδ => (measure_biUnion_null_iff hDc).mpr fun δ' hδ' => ?_
      rw [img_mul δ', measure_preimage_mul]
      have hΓ : δ'⁻¹ * s * δ ∈ Γ :=
        Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (hD.1 hδ')) (hsΓ s hs)) (hD.1 hδ)
      refine h.disj _ hΓ ?_
      intro h1
      apply hs1
      have hsδ : s * δ = δ' := by
        calc s * δ = δ' * (δ'⁻¹ * s * δ) := by group
          _ = δ' := by rw [h1, mul_one]
      have huq := (hD.2 δ' (hD.1 hδ')).unique (y₁ := ((⟨s, hs⟩ : S), (⟨δ, hδ⟩ : Dt)))
        (y₂ := ((1 : S), (⟨δ', hδ'⟩ : Dt))) hsδ (by simp)
      have := congrArg (fun p : S × Dt => (p.1 : G)) huq
      simpa using this

end Unfold

end InHHLeaf

namespace InHHLeaf

open MeasureTheory Set Formalism.MainNotions.LeviCoordinates
open scoped ENNReal Pointwise

section Unfold2

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}

private theorem isFundamentalDomain_of_rr_FD (h : rr_FD μ Γ D) : IsFundamentalDomain Γ D μ := by
  refine IsFundamentalDomain.mk'' h.meas.nullMeasurableSet
    (Filter.Eventually.of_forall fun y => ?_) (fun g hg => ?_) (fun g => ?_)
  · obtain ⟨γ, hγ, hy⟩ := h.cov y
    exact ⟨⟨γ, hγ⟩, hy⟩
  · have hg' : (g : G) ≠ 1 := fun h' => hg (Subtype.ext h')
    exact h.disj g g.2 hg'
  · exact (measurePreserving_mul_left μ (g : G)).quasiMeasurePreserving

theorem unfold_lint (h : rr_FD μ Γ D) (S : Subgroup G) (hS : S ≤ Γ) (Dt : Set G)
    (hD : FoldBound.IsRightTransversal Γ S Dt) (Fs : Set G) (hFs : IsFundamentalDomain S Fs μ)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ s ∈ S, ∀ y, f (s * y) = f y) :
    ∫⁻ y in D, ∑' δ : Dt, f ((δ : G) * y) ∂μ = ∫⁻ y in Fs, f y ∂μ := by
  classical
  have hΓc : (Γ : Set G).Countable := Set.countable_coe_iff.mp (by exact (inferInstance : Countable Γ))
  have hDc : Dt.Countable := Set.Countable.mono hD.1 hΓc
  haveI : Countable Dt := hDc.to_subtype
  haveI : Countable S := Function.Injective.countable (Subgroup.inclusion_injective hS)
  have hU := isFundamentalDomain_of_rr_FD (rr_FD_union h S hS Dt hD hDc)
  have hUeq : (⋃ δ ∈ Dt, (fun y => δ * y) '' D) = ⋃ δ : Dt, (fun y => (δ : G) * y) '' D := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨δ, hδ, hx⟩
      exact ⟨⟨δ, hδ⟩, hx⟩
    · rintro ⟨⟨δ, hδ⟩, hx⟩
      exact ⟨δ, hδ, hx⟩
  have hm : ∀ δ : Dt, AEMeasurable (fun y => f ((δ : G) * y)) (μ.restrict D) :=
    fun δ => (hf.comp (measurable_const_mul _)).aemeasurable
  rw [← hU.setLIntegral_eq hFs f (fun g x => hinv g g.2 x), hUeq, lintegral_tsum hm, lintegral_iUnion₀ ?_ ?_ f]
  · refine tsum_congr fun δ => ?_
    exact (measurePreserving_mul_left μ (δ : G)).setLIntegral_comp_emb (measurableEmbedding_mulLeft _) f D
  · intro δ
    rw [img_mul]
    exact (h.meas.preimage (measurable_const_mul _)).nullMeasurableSet
  · intro δ δ' hne
    show μ ((fun y => (δ : G) * y) '' D ∩ (fun y => (δ' : G) * y) '' D) = 0
    have hne' : (δ : G) ≠ δ' := fun e => hne (Subtype.ext e)
    have hΓ : (δ' : G)⁻¹ * δ ∈ Γ := Γ.mul_mem (Γ.inv_mem (hD.1 δ'.2)) (hD.1 δ.2)
    have h1 : (δ' : G)⁻¹ * δ ≠ 1 := by
      intro e
      apply hne'
      calc (δ : G) = δ' * ((δ' : G)⁻¹ * δ) := by group
        _ = δ' := by rw [e, mul_one]
    refine measure_mono_null
      (t := (fun y => (δ' : G) * y) '' ((fun y => ((δ' : G)⁻¹ * δ) * y) '' D ∩ D)) ?_ ?_
    · rintro x ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
      refine ⟨b, ⟨⟨a, ha, ?_⟩, hb⟩, hab⟩
      have hab' : (δ' : G) * b = δ * a := hab
      show (δ' : G)⁻¹ * δ * a = b
      have hbe : b = (δ' : G)⁻¹ * (δ * a) := by rw [← hab']; group
      rw [hbe]
      group
    · rw [img_mul (δ' : G), measure_preimage_mul]
      exact h.disj _ hΓ h1

end Unfold2

end InHHLeaf

section PserRphSec

open MeasureTheory Formalism.MainNotions.LeviCoordinates
open scoped ENNReal

variable {D : D7} (X : HidaSetting D)

theorem one_le_mult {G : Type*} [Group G] (Γ : Subgroup G) (Ω : Set G) (h1 : (1 : G) ∈ Ω) (x : G) :
    1 ≤ Formalism.L2.SG.FoldBound.mult Γ Ω x := by
  unfold Formalism.L2.SG.FoldBound.mult
  refine le_trans ?_ (le_iSup _ x)
  have hmem : (1 : Γ) ∈ ({γ : Γ | x⁻¹ * ((γ : G) * x) ∈ Ω} : Set Γ) := by simpa using h1
  have h1' : (1 : ℕ∞) ≤ ({γ : Γ | x⁻¹ * ((γ : G) * x) ∈ Ω} : Set Γ).encard :=
    Set.one_le_encard_iff_nonempty.mpr ⟨1, hmem⟩
  calc (1 : ℝ≥0∞) = ((1 : ℕ∞) : ℝ≥0∞) := by simp
    _ ≤ _ := ENat.toENNReal_le.mpr h1'

theorem pserRph_holds (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) : PserRph X u hK := by
  intro hOK hPI hPP T Dt hD
  have := X.B.sf
  have := X.B.haar
  have := gf_secondCountable X.B.I
  have := muf_right X
  have := rr_muA_sigmaFinite X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  have := rr_muA_right X.B.I X.B.μf
  obtain ⟨⟨Fs, hFs⟩, Ω₀, a, hc, h1, hT⟩ := hOK
  have hFD := rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have hS : Srat X u ≤ rr_GF X.B.I := inf_le_left
  obtain ⟨r, hrm, hr⟩ := rr_exists_meas_rep hFD
  set f : X.B.I.GA → ℝ≥0∞ := fun w => ‖Ph X u hK T w‖ₑ with hfdef
  have hfm : Measurable f := (hPP T).1.enorm
  have hfinv : ∀ s ∈ Srat X u, ∀ y, f (s * y) = f y := fun s hs y => by
    simp only [hfdef, (hPP T).2.1 s hs y]
  set F : X.B.I.GA → ℝ≥0∞ := fun w => ∑' δ : Dt, f ((δ : X.B.I.GA) * w) with hFdef
  have hDc : Dt.Countable :=
    (Set.countable_coe_iff.1 (inferInstance : Countable (rr_GF X.B.I))).mono hD.1
  have := hDc.to_subtype
  have hFm : Measurable F := Measurable.ennreal_tsum fun δ => hfm.comp (measurable_const_mul _)
  have hFinv : ∀ γ ∈ rr_GF X.B.I, ∀ w, F (γ * w) = F w := fun γ hγ w =>
    InHHLeaf.poincE_left_inv (Srat X u) Dt hD f hfinv γ hγ w

  have hC : ∫⁻ y in X.B.fund, F y ∂(X.B.I.muA X.B.μf) < ⊤ := by
    rw [InHHLeaf.unfold_lint hFD (Srat X u) hS Dt hD Fs hFs f hfm hfinv]
    refine lt_of_le_of_lt ?_ ((hT T).2 Ω₀ hc Fs hFs)
    unfold Formalism.L2.SG.PoincareSeriesSquareIntegrable.multiplicityLIntegral
    refine lintegral_mono fun y => ?_
    calc f y = 1 * ‖Ph X u hK T y‖ₑ := by rw [one_mul]
      _ ≤ _ := mul_le_mul' (one_le_mult _ _ h1 y) le_rfl

  set φ' := hPI.1.aemeasurable.mk X.ph with hφ'
  have hφ'm : Measurable φ' := hPI.1.aemeasurable.measurable_mk
  have hφφ' : X.ph =ᵐ[Formalism.L2.SG.ProjRows.muInf X.B.I] φ' := hPI.1.aemeasurable.ae_eq_mk
  set ι : X.B.I.Ginf → X.B.I.GA := fun z => (z, (1 : X.B.I.Gf)) with hι
  have hιm : Measurable ι := measurable_id.prodMk measurable_const
  set K : X.B.I.GA × X.B.I.Ginf → ℝ≥0∞ := fun p => ‖φ' p.2‖ₑ * F (p.1 * ι p.2) with hKdef
  have hKm : Measurable K := (hφ'm.comp measurable_snd).enorm.mul (hFm.comp (measurable_fst.mul (hιm.comp measurable_snd)))
  set J : X.B.I.GA → ℝ≥0∞ := fun y => ∫⁻ z, K (y, z) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) with hJdef
  have hJm : Measurable J := hKm.lintegral_prod_right'
  have hJint : ∫⁻ y in X.B.fund, J y ∂(X.B.I.muA X.B.μf) < ⊤ := by
    rw [hJdef, lintegral_lintegral_swap (f := fun y z => K (y, z)) hKm.aemeasurable]
    have e1 : ∀ z, ∫⁻ y in X.B.fund, K (y, z) ∂(X.B.I.muA X.B.μf) =
        ‖φ' z‖ₑ * ∫⁻ y in X.B.fund, F y ∂(X.B.I.muA X.B.μf) := by
      intro z
      simp only [hKdef]
      rw [lintegral_const_mul (f := fun y => F (y * ι z)) _ (hFm.comp (measurable_mul_const _))]
      congr 1
      rw [← rrkb_lint hFD hr (ι z) hFm]
      refine lintegral_congr fun x => ?_
      obtain ⟨γ, hγ, e, -⟩ := hr (x * ι z)
      rw [e, hFinv γ hγ]
    simp only [e1]
    rw [lintegral_mul_const _ hφ'm.enorm]
    refine ENNReal.mul_lt_top ?_ hC
    exact (hPI.congr hφφ').2
  have hJae : ∀ᵐ y ∂((X.B.I.muA X.B.μf).restrict X.B.fund), J y < ⊤ :=
    ae_lt_top hJm hJint.ne
  have hJinv : ∀ γ ∈ rr_GF X.B.I, ∀ y, J (γ * y) = J y := by
    intro γ hγ y
    simp only [hJdef, hKdef, mul_assoc, hFinv γ hγ]
  have hJall : ∀ᵐ y ∂(X.B.I.muA X.B.μf), J y < ⊤ := by
    set B := {y | ¬ J y < ⊤} with hB
    have hBD : X.B.I.muA X.B.μf (B ∩ X.B.fund) = 0 := by
      rw [← Measure.restrict_apply' hFD.meas]
      exact hJae
    have hsub : B ⊆ ⋃ γ : rr_GF X.B.I, (fun y => (γ : X.B.I.GA)⁻¹ * y) '' (B ∩ X.B.fund) := by
      intro y hy
      obtain ⟨γ, hγ, hyD⟩ := hFD.cov y
      refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, γ * y, ⟨?_, hyD⟩, by simp⟩
      show ¬ J (γ * y) < ⊤
      rw [hJinv γ hγ]; exact hy
    refine measure_mono_null hsub (measure_iUnion_null fun γ => ?_)
    rw [InHHLeaf.img_mul, measure_preimage_mul]
    exact hBD
  filter_upwards [hJall] with y hy
  unfold Pser Formalism.L2.SG.PoincareSeriesSquareIntegrable.poinc
  have hmeas : ∀ δ : Dt, AEStronglyMeasurable
      (fun z => X.ph z * Ph X u hK T ((δ : X.B.I.GA) * (y * (z, 1)))) (Formalism.L2.SG.ProjRows.muInf X.B.I) := by
    intro δ
    have := ((hPP T).2.2.2 ((δ : X.B.I.GA) * y)).1
    simpa [mul_assoc] using this.1
  have hsum : ∑' δ : Dt, ∫⁻ z, ‖X.ph z * Ph X u hK T ((δ : X.B.I.GA) * (y * (z, 1)))‖ₑ
      ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) ≠ ⊤ := by
    rw [← lintegral_tsum fun δ => (hmeas δ).enorm]
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hy)
    simp only [hJdef, hKdef, hFdef, hfdef]
    refine lintegral_congr_ae (hφφ'.mono fun z hz => ?_)
    beta_reduce
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun δ => ?_
    rw [enorm_mul, hz]
  simp only [← tsum_mul_left]
  rw [integral_tsum hmeas hsum]
  refine tsum_congr fun δ => ?_
  have := ((hPP T).2.2.2 ((δ : X.B.I.GA) * y)).2
  simpa [mul_assoc] using this

end PserRphSec

end Formalism.L2.SG.Pf
