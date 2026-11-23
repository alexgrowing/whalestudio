import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FlagExtensionRegularity
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.WeilIndicatorMeasures.MeasurableUnitMulIndicator
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

noncomputable section

open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.NGPin

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def haarOn (H : Subgroup G) (hH : IsClosed (H : Set G)) : Measure G :=
  have : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  (Measure.haar : Measure H).map Subtype.val

theorem haarOn_spec (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    SigmaFinite (haarOn H hH) ∧ haarOn H hH ≠ 0 ∧ haarOn H hH (H : Set G)ᶜ = 0 ∧
      ∀ s ∈ H, (haarOn H hH).map (fun x => s * x) = haarOn H hH := by
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hm : Measurable (Subtype.val : H → G) := measurable_subtype_coe
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI : IsFiniteMeasureOnCompacts (haarOn H hH) := by
      constructor
      intro K hK
      simp only [haarOn]
      rw [Measure.map_apply hm hK.measurableSet]
      exact (hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top
    infer_instance
  · simp only [haarOn]
    rw [Ne, Measure.map_eq_zero_iff hm.aemeasurable]
    exact NeZero.ne _
  · simp only [haarOn]
    rw [Measure.map_apply hm hH.isOpen_compl.measurableSet]
    have e0 : (Subtype.val : H → G) ⁻¹' (H : Set G)ᶜ = ∅ := by
      ext x
      exact ⟨fun hx => hx x.2, fun hx => hx.elim⟩
    rw [e0, measure_empty]
  · intro s hs
    simp only [haarOn]
    rw [Measure.map_map (measurable_const_mul s) hm]
    have e : (fun x => s * x) ∘ (Subtype.val : H → G) = Subtype.val ∘ (fun y : H => (⟨s, hs⟩ : H) * y) := by
      funext y; rfl
    rw [e, ← Measure.map_map hm (measurable_const_mul _), map_mul_left_eq_self]

theorem quot_exists_gen (H : Subgroup G) (hH : IsClosed (H : Set G)) (μG μS : Measure G) [SigmaFinite μG]
    (hGinv : ∀ h ∈ H, μG.map (fun x => h * x) = μG) [hSsf : SigmaFinite μS] (hSne : μS ≠ 0)
    (hScon : μS (H : Set G)ᶜ = 0) (hSinv : ∀ h ∈ H, μS.map (fun x => h * x) = μS) :
    ∃ ν : Measure G, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν := by
  classical
  have : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  have : SigmaCompactSpace H := sigmaCompactSpace_of_locallyCompact_secondCountable
  let e : H → G := Subtype.val
  have he : MeasurableEmbedding e := hH.isClosedEmbedding_subtypeVal.measurableEmbedding
  have hae : ∀ᵐ x ∂μS, x ∈ Set.range e := by
    rw [Subtype.range_coe, ae_iff]
    exact hScon
  set κ : Measure H := μS.comap e with hκ
  have hκmap : κ.map e = μS := by rw [hκ, he.map_comap, Measure.restrict_eq_self_of_ae_mem hae]
  haveI : SigmaFinite κ := SigmaFinite.of_map κ he.measurable.aemeasurable (by rw [hκmap]; exact hSsf)
  have hκinv : ∀ g : H, κ.map (g * ·) = κ := by
    intro g
    have hcomm : e ∘ (g * ·) = (fun x => (g : G) * x) ∘ e := by
      funext h
      rfl
    rw [← he.comap_map (κ.map (g * ·)), Measure.map_map he.measurable (measurable_const_mul g), hcomm,
      ← Measure.map_map (measurable_const_mul _) he.measurable, hκmap, hSinv _ g.2, hκ]
  haveI : κ.IsMulLeftInvariant := ⟨fun g => hκinv g⟩
  set lam : Measure H := Measure.haar with hlam
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : H)
  have hK0 : lam K ≠ 0 := (Measure.measure_pos_of_mem_nhds lam hK1).ne'
  have hKt : lam K ≠ ⊤ := hKc.measure_lt_top.ne
  have hκeq : κ = (κ K / lam K) • lam := measure_eq_div_smul κ lam hK0 hKt
  set c : ℝ≥0∞ := κ K / lam K with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply hSne
    rw [← hκmap, hκeq, h0, zero_smul, Measure.map_zero]
  have hct : c ≠ ⊤ := by
    intro ht
    have hnull : ∀ n, lam (spanningSets κ n) = 0 := fun n => by
      have h1 := measure_spanningSets_lt_top κ n
      generalize spanningSets κ n = A at h1 ⊢
      rw [hκeq, ht, Measure.smul_apply, smul_eq_mul] at h1
      by_contra hne
      rw [ENNReal.top_mul hne] at h1
      exact lt_irrefl _ h1
    have h2 : lam Set.univ = 0 := by
      rw [← iUnion_spanningSets κ]
      exact measure_iUnion_null hnull
    exact hK0 (measure_mono_null (Set.subset_univ K) h2)
  obtain ⟨β, hβm, hβ1⟩ := Formalism.L2.SG.Pf.Weil.QuotInt.exists_fib_eq_one hH lam
  set φ : G → ℝ≥0∞ := fun y => β y⁻¹ with hφ
  have hφm : Measurable φ := hβm.comp measurable_inv
  refine ⟨μG.withDensity (fun y => c⁻¹ * φ y), fun f hf => ?_⟩
  have hF2 : Measurable fun p : G × G => f (p.2 * p.1) := hf.comp (measurable_snd.mul measurable_fst)
  have hin : Measurable fun x : G => ∫⁻ s, f (s * x) ∂μS := Measurable.lintegral_prod_right' hF2
  have hfib : ∀ x : G, Measurable fun s : G => f (s * x) := fun x => hf.comp (measurable_id.mul measurable_const)
  have hsub : ∀ h : H, ∫⁻ x, c⁻¹ * φ x * f ((h : G) * x) ∂μG =
      ∫⁻ y, c⁻¹ * φ ((h : G)⁻¹ * y) * f y ∂μG := by
    intro h
    have hmap := hGinv _ h.2
    have hFm : Measurable fun y => c⁻¹ * φ ((h : G)⁻¹ * y) * f y :=
      (measurable_const.mul (hφm.comp (measurable_const_mul _))).mul hf
    calc ∫⁻ x, c⁻¹ * φ x * f ((h : G) * x) ∂μG
        = ∫⁻ x, c⁻¹ * φ ((h : G)⁻¹ * ((h : G) * x)) * f ((h : G) * x) ∂μG := by
          refine lintegral_congr fun x => ?_
          rw [inv_mul_cancel_left]
      _ = ∫⁻ y, c⁻¹ * φ ((h : G)⁻¹ * y) * f y ∂(μG.map (fun x => (h : G) * x)) :=
          (lintegral_map hFm (measurable_const_mul _)).symm
      _ = ∫⁻ y, c⁻¹ * φ ((h : G)⁻¹ * y) * f y ∂μG := by rw [hmap]
  have hone : ∀ y : G, ∫⁻ h : H, φ ((h : G)⁻¹ * y) ∂κ = c := by
    intro y
    have hval : ∀ h : H, φ ((h : G)⁻¹ * y) = β (y⁻¹ * (h : G)) := by
      intro h
      simp only [hφ, mul_inv_rev, inv_inv]
    simp_rw [hval]
    rw [hκeq, lintegral_smul_measure]
    have := hβ1 y⁻¹
    unfold Formalism.L2.SG.Pf.Weil.QuotInt.fib at this
    rw [this, smul_eq_mul, mul_one]
  symm
  have hden : Measurable fun y => c⁻¹ * φ y := measurable_const.mul hφm
  refine (lintegral_withDensity_eq_lintegral_mul μG hden hin).trans ?_
  simp only [Pi.mul_apply]
  calc ∫⁻ x, c⁻¹ * φ x * ∫⁻ s, f (s * x) ∂μS ∂μG
      = ∫⁻ x, ∫⁻ s, c⁻¹ * φ x * f (s * x) ∂μS ∂μG :=
        lintegral_congr fun x => (lintegral_const_mul _ (hfib x)).symm
    _ = ∫⁻ s, ∫⁻ x, c⁻¹ * φ x * f (s * x) ∂μG ∂μS := by
        refine lintegral_lintegral_swap ?_
        exact ((measurable_const.mul (hφm.comp measurable_fst)).mul hF2).aemeasurable
    _ = ∫⁻ h, ∫⁻ x, c⁻¹ * φ x * f ((e h) * x) ∂μG ∂κ := by
        rw [← hκmap, he.lintegral_map]
    _ = ∫⁻ h, ∫⁻ y, c⁻¹ * φ ((h : G)⁻¹ * y) * f y ∂μG ∂κ := lintegral_congr hsub
    _ = ∫⁻ y, ∫⁻ h, c⁻¹ * φ ((h : G)⁻¹ * y) * f y ∂κ ∂μG := by
        refine lintegral_lintegral_swap ?_
        have hc2 : Measurable fun p : H × G => (p.1 : G)⁻¹ * p.2 :=
          ((measurable_subtype_coe.comp measurable_fst).inv).mul measurable_snd
        exact ((measurable_const.mul (hφm.comp hc2)).mul (hf.comp measurable_snd)).aemeasurable
    _ = ∫⁻ y, f y ∂μG := by
        refine lintegral_congr fun y => ?_
        have hmeas : Measurable fun h : H => φ ((h : G)⁻¹ * y) :=
          hφm.comp ((measurable_subtype_coe.inv).mul measurable_const)
        calc ∫⁻ h, c⁻¹ * φ ((h : G)⁻¹ * y) * f y ∂κ = (∫⁻ h, c⁻¹ * φ ((h : G)⁻¹ * y) ∂κ) * f y :=
              lintegral_mul_const _ (measurable_const.mul hmeas)
          _ = (c⁻¹ * ∫⁻ h, φ ((h : G)⁻¹ * y) ∂κ) * f y := by rw [lintegral_const_mul _ hmeas]
          _ = f y := by rw [hone y, ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem eq_smul_dirac_of_conc (μ : Measure G) (a : G) (h : μ ({a} : Set G)ᶜ = 0) :
    μ = μ {a} • Measure.dirac a := by
  ext s hs
  have h0 : μ (s \ {a}) = 0 := measure_mono_null (fun x hx => hx.2) h
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul,
    ← measure_inter_add_diff s (measurableSet_singleton a), h0, add_zero]
  by_cases ha : a ∈ s
  · rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr ha)]
    simp [ha]
  · rw [Set.inter_singleton_eq_empty.mpr ha]
    simp [ha]

end Gen

section St

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ninf_eq (u : D.what₂.Word) : (ProductExactness.NinfG X u : Set X.B.I.Ginf) = X.NinfU u := ProductExactness.NinfG_coe X u

theorem mem_ninfG {u : D.what₂.Word} {y : X.B.I.Ginf} : y ∈ ProductExactness.NinfG X u ↔ y ∈ X.NinfU u := by
  rw [← SetLike.mem_coe, ninf_eq X u]

def StG (u u' : D.what₂.Word) (γ : X.B.I.Ginf) : Subgroup X.B.I.Ginf where
  carrier := StInf X u u' γ
  one_mem' := ⟨mem_ninfG X |>.1 (ProductExactness.NinfG X u).one_mem, by
    have := mem_ninfG X |>.1 (ProductExactness.NinfG X u').one_mem
    have e : γ⁻¹ * 1 * γ = 1 := by group
    show γ⁻¹ * 1 * γ ∈ X.NinfU u'
    rw [e]; exact this⟩
  mul_mem' := fun {a b} ha hb => ⟨mem_ninfG X |>.1 ((ProductExactness.NinfG X u).mul_mem (mem_ninfG X |>.2 ha.1)
      (mem_ninfG X |>.2 hb.1)), by
    have := mem_ninfG X |>.1 ((ProductExactness.NinfG X u').mul_mem (mem_ninfG X |>.2 ha.2) (mem_ninfG X |>.2 hb.2))
    have e : γ⁻¹ * (a * b) * γ = (γ⁻¹ * a * γ) * (γ⁻¹ * b * γ) := by group
    show γ⁻¹ * (a * b) * γ ∈ X.NinfU u'
    rw [e]; exact this⟩
  inv_mem' := fun {a} ha => ⟨mem_ninfG X |>.1 ((ProductExactness.NinfG X u).inv_mem (mem_ninfG X |>.2 ha.1)), by
    have := mem_ninfG X |>.1 ((ProductExactness.NinfG X u').inv_mem (mem_ninfG X |>.2 ha.2))
    have e : γ⁻¹ * a⁻¹ * γ = (γ⁻¹ * a * γ)⁻¹ := by group
    show γ⁻¹ * a⁻¹ * γ ∈ X.NinfU u'
    rw [e]; exact this⟩

theorem coe_StG (u u' : D.what₂.Word) (γ : X.B.I.Ginf) : (StG X u u' γ : Set X.B.I.Ginf) = StInf X u u' γ := rfl

theorem isClosed_StG (u u' : D.what₂.Word) (γ : X.B.I.Ginf) : IsClosed (StG X u u' γ : Set X.B.I.Ginf) := by
  rw [coe_StG]
  have h1 : IsClosed (X.NinfU u) := by rw [← ninf_eq X u]; exact ProductExactness.NinfG_closed X u
  have h2 : IsClosed (X.NinfU u') := by rw [← ninf_eq X u']; exact ProductExactness.NinfG_closed X u'
  have hc : Continuous (fun y : X.B.I.Ginf => γ⁻¹ * y * γ) := by fun_prop
  exact h1.inter (h2.preimage hc)

theorem stInf_reg (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (hreg : RegX X u u' γ) : StInf X u u' γ = {1} := by
  ext y
  constructor
  · rintro ⟨hN, hN'⟩
    rw [Set.mem_singleton_iff]
    funext v
    apply Subtype.ext
    apply Units.ext
    show uMat (y v) = 1
    set g := uMat (γ v) with hg
    set gi := uMat (γ⁻¹ v) with hgi
    have hgg : g * gi = 1 := FlagExtensionRegularity.uMat_mul_inv' (γ v)
    have hv := hN v
    have hv' := hN' v
    have hconj : uMat ((γ⁻¹ * y * γ) v) = gi * uMat (y v) * g := by
      simp [uMat, hg, hgi]
    rw [hconj] at hv'
    set e := fun a => rv X.B.I v (X.eR a) with he
    have hkey : ∀ z, (uMat (y v) - 1) *ᵥ (g *ᵥ z) = g *ᵥ ((gi * uMat (y v) * g - 1) *ᵥ z) := by
      intro z
      have hm : g * (gi * uMat (y v) * g - 1) = (uMat (y v) - 1) * g := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc, hgg]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm]
    refine HermitianBlockSpans.st_triv (X.B.I.ε v) e (fun a => g *ᵥ e a) (uMat (y v)) (HermitianBlockSpans.hJ_map _ (y v).2) hv.1.1
      (fun a => ?_) hv.2 (fun l hl h1 => ?_)
    · rw [hkey]
      exact FlagExtensionRegularity.span_map g e a.1 (hv'.1.1 a)
    · have := (hreg v).1 l h1 hl
      rwa [FlagExtensionRegularity.dl_eq X u u' γ v hl] at this
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (StG X u u' γ).one_mem'

end St

section PtInj

theorem ptEntry_cons {K : Type*} [Zero K] (t : K) (s : ℕ) (bs : List (K × ℕ)) (a b : ℕ) :
    ptEntry ((t, s) :: bs) a b = if a < s ∧ b < s then (if a + b + 1 = s then t else 0)
      else if s ≤ a ∧ s ≤ b then ptEntry bs (a - s) (b - s) else 0 := rfl

theorem ptEntry_inj {K : Type*} [Zero K] : ∀ (bs cs : List (K × ℕ)) (i : ℕ),
    (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → (bs.map Prod.snd).sum = i →
    (∀ b ∈ cs, b.1 ≠ 0 ∧ 1 ≤ b.2) → (cs.map Prod.snd).sum = i →
    (∀ a b, a < i → b < i → ptEntry bs a b = ptEntry cs a b) → bs = cs
  | [], [], _, _, _, _, _, _ => rfl
  | [], (c :: cs), i, _, h1, h2, h3, _ => by
    have := (h2 c (List.mem_cons_self ..)).2
    simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons] at h1 h3
    omega
  | (b :: bs), [], i, h0, h1, _, h3, _ => by
    have := (h0 b (List.mem_cons_self ..)).2
    simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons] at h1 h3
    omega
  | ((t, s) :: bs), ((t', s') :: cs), i, hb, hbs, hc, hcs, he => by
    have ht := (hb (t, s) (List.mem_cons_self ..))
    have ht' := (hc (t', s') (List.mem_cons_self ..))
    simp only [List.map_cons, List.sum_cons] at hbs hcs
    have hsi : s ≤ i := by omega
    have e0 := he 0 (s - 1) (by omega) (by omega)
    rw [ptEntry_cons, ptEntry_cons] at e0
    have hl : (0 < s ∧ s - 1 < s) := ⟨by omega, by omega⟩
    rw [if_pos hl, if_pos (by omega : 0 + (s - 1) + 1 = s)] at e0
    have hss : s = s' ∧ t = t' := by
      by_cases h1 : 0 < s' ∧ s - 1 < s'
      · rw [if_pos h1] at e0
        by_cases h2 : 0 + (s - 1) + 1 = s'
        · rw [if_pos h2] at e0
          exact ⟨by omega, e0⟩
        · rw [if_neg h2] at e0
          exact absurd e0 ht.1
      · rw [if_neg h1, if_neg (by omega)] at e0
        exact absurd e0 ht.1
    obtain ⟨rfl, rfl⟩ := hss
    congr 1
    refine ptEntry_inj bs cs (i - s) (fun b hb' => hb b (List.mem_cons_of_mem _ hb')) (by omega)
      (fun b hb' => hc b (List.mem_cons_of_mem _ hb')) (by omega) (fun a b ha hb2 => ?_)
    have := he (a + s) (b + s) (by omega) (by omega)
    rw [ptEntry_cons, ptEntry_cons, if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega),
      Nat.add_sub_cancel, Nat.add_sub_cancel] at this
    exact this

theorem ptMat_inj {K : Type*} [Zero K] {i : ℕ} {p q : Point K i} (h : ptMat p = ptMat q) : p = q := Subtype.ext (ptEntry_inj p.1 q.1 i p.2.1 p.2.2 q.2.1 q.2.2
  (fun a b ha hb => congrFun (congrFun h ⟨a, ha⟩) ⟨b, hb⟩))

end PtInj

section Pin

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PinHaarEx : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)),
    (∃ γ, IsPtRep X u u' w γ) →
    ∃ (μ : Measure X.B.I.Ginf) (c : ℝ≥0∞), IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μ ∧
      c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map (stCoord X u' w (gamW X u u' w)) = c • muStab X w

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

theorem isPtRep_gamW {w : Point D.host.E (D.R.rS + 1)} (h : ∃ γ, IsPtRep X u u' w γ) :
    IsPtRep X u u' w (gamW X u u' w) := by
  unfold gamW
  rw [dif_pos h]
  exact h.choose_spec

theorem pt_eq_of_rep {w w' : Point D.host.E (D.R.rS + 1)} {γ : X.B.I.Ginf} (h : IsPtRep X u u' w γ)
    (h' : IsPtRep X u u' w' γ) : w = w' := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have e : ptC X v w = ptC X v w' := (h v).symm.trans (h' v)
  apply ptMat_inj
  have hinj : Function.Injective (fun t => X.B.I.φ v (X.ιE.symm t)) :=
    fun a b hab => X.ιE.symm.injective ((X.B.I.φ v).injective hab)
  exact Matrix.map_injective hinj e

private theorem sf_smul_lemma {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] {c : ℝ≥0∞}
    (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by
  have hfin : ∀ i, (c • μ) (spanningSets μ i) < ⊤ := fun i => by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_spanningSets_lt_top μ i)
  exact ⟨⟨{ set := spanningSets μ, set_mem := fun _ => trivial, finite := hfin, spanning := iUnion_spanningSets μ }⟩⟩

private theorem pi_pi_univ_lemma_2 {ι κ : Type*} [Fintype ι] [Fintype κ] (k : ℝ≥0∞) (hk : k ≠ ⊤) :
    (Measure.pi fun _ : ι => Measure.pi fun _ : κ => k • (volume : Measure ℂ)) Set.univ = 0 ∨
    (Measure.pi fun _ : ι => Measure.pi fun _ : κ => k • (volume : Measure ℂ)) Set.univ = 1 ∨
    (Measure.pi fun _ : ι => Measure.pi fun _ : κ => k • (volume : Measure ℂ)) Set.univ = ⊤ := by
  have key : ∀ (n : ℕ) (x : ℝ≥0∞), (x = 0 ∨ x = 1 ∨ x = ⊤) → (x ^ n = 0 ∨ x ^ n = 1 ∨ x ^ n = ⊤) := by
    intro n x hx
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · right; left; exact pow_zero x
    · rcases hx with rfl | rfl | rfl
      · left; exact zero_pow hn.ne'
      · right; left; exact one_pow n
      · right; right; exact ENNReal.pow_eq_top_iff.2 ⟨rfl, hn.ne'⟩
  haveI : SigmaFinite (k • (volume : Measure ℂ)) := sf_smul_lemma _ hk
  have hvol : (volume : Measure ℂ) Set.univ = ⊤ := measure_univ_of_isAddLeftInvariant _
  simp only [Measure.pi_univ, Measure.smul_apply, smul_eq_mul, hvol, Finset.prod_const, Finset.card_univ]
  apply key
  apply key
  by_cases h0 : k = 0
  · left; rw [h0, zero_mul]
  · right; right; exact ENNReal.mul_top h0

theorem muStab_univ (w : Point D.host.E (D.R.rS + 1)) :
    muStab X w Set.univ = 0 ∨ muStab X w Set.univ = 1 ∨ muStab X w Set.univ = ⊤ := by
  unfold muStab
  exact pi_pi_univ_lemma_2 _ ENNReal.ofReal_ne_top

theorem pin_reg (hP : PinHaarEx) {w : Point D.host.E (D.R.rS + 1)} (hw : ∃ γ, IsPtRep X u u' w γ)
    (hreg : RegX X u u' (gamW X u u' w)) :
    (Measure.dirac (1 : X.B.I.Ginf)).map (stCoord X u' w (gamW X u u' w)) = muStab X w := by
  obtain ⟨μ, c, ⟨hsf, hne, hcon, _⟩, hc0, hct, hmap⟩ := hP D X u u' w hw
  haveI := hsf
  rw [stInf_reg X u u' _ hreg] at hcon
  have hμ := eq_smul_dirac_of_conc μ 1 hcon
  have ha0 : μ {1} ≠ 0 := by
    intro h0; apply hne; rw [hμ, h0, zero_smul]
  have hat : μ {1} ≠ ⊤ := ne_top_of_le_ne_top (measure_spanningSets_lt_top μ _).ne
    (measure_mono (Set.singleton_subset_iff.2 (mem_spanningSetsIndex μ 1)))
  rw [hμ, Measure.map_smul] at hmap
  set m := (Measure.dirac (1 : X.B.I.Ginf)).map (stCoord X u' w (gamW X u u' w)) with hm
  have hm' : m = (μ {1})⁻¹ • c • muStab X w := by
    rw [← hmap, smul_smul, ENNReal.inv_mul_cancel ha0 hat, one_smul]
  by_cases hf : AEMeasurable (stCoord X u' w (gamW X u u' w)) (Measure.dirac 1)
  · have h1 : m Set.univ = 1 := by
      rw [hm, Measure.map_apply_of_aemeasurable hf MeasurableSet.univ, Set.preimage_univ, measure_univ]
    have h2 := congrArg (fun n : Measure _ => n Set.univ) hmap
    simp only [Measure.smul_apply, smul_eq_mul, h1, mul_one] at h2
    have h3 : muStab X w Set.univ = 1 := by
      rcases muStab_univ X w with h | h | h
      · rw [h, mul_zero] at h2; exact absurd h2 ha0
      · exact h
      · rw [h, ENNReal.mul_top hc0] at h2; exact absurd h2 hat
    rw [h3, mul_one] at h2
    rw [hm', ← h2, smul_smul, ENNReal.inv_mul_cancel ha0 hat, one_smul]
  · have h0 : m = 0 := Measure.map_of_not_aemeasurable hf
    rw [h0, smul_zero] at hmap
    rw [h0]
    ext s hs
    have h4 := congrArg (fun n : Measure _ => n s) hmap
    simp only [Measure.coe_zero, Pi.zero_apply, Measure.smul_apply, smul_eq_mul] at h4 ⊢
    rcases mul_eq_zero.1 h4.symm with h | h
    · exact absurd h hc0
    · exact h.symm

end Pin

section Assembly

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

theorem muInf_map (h : X.B.I.Ginf) :
    (Formalism.L2.SG.ProjRows.muInf X.B.I).map (fun x => h * x) = Formalism.L2.SG.ProjRows.muInf X.B.I := map_mul_left_eq_self _ h

theorem quot_St (γ : X.B.I.Ginf) (μR : Measure X.B.I.Ginf) (hR : IsHaarOnSet X.B.I (StInf X u u' γ) μR) :
    ∃ ν, IsQuotMeasS X.B.I μR ν := by
  obtain ⟨hsf, hne, hcon, hinv⟩ := hR
  haveI := hsf
  exact quot_exists_gen (StG X u u' γ) (isClosed_StG X u u' γ) (Formalism.L2.SG.ProjRows.muInf X.B.I) μR
    (fun h _ => muInf_map X h) hne hcon hinv

theorem haar_St (γ : X.B.I.Ginf) : ∃ μR, IsHaarOnSet X.B.I (StInf X u u' γ) μR := by
  exact ⟨_, haarOn_spec (StG X u u' γ) (isClosed_StG X u u' γ)⟩

theorem pinned_at (hP : PinHaarEx) {w : Point D.host.E (D.R.rS + 1)} (hw : ∃ γ, IsPtRep X u u' w γ) :
    ∃ μR, IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR ∧
      μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w := by
  obtain ⟨μ, c, ⟨hsf, hne, hcon, hinv⟩, hc0, hct, hmap⟩ := hP D X u u' w hw
  haveI := hsf
  refine ⟨c⁻¹ • μ, ⟨sf_smul_lemma μ (ENNReal.inv_ne_top.2 hc0), ?_, ?_, ?_⟩, ?_⟩
  · intro h0
    apply hne
    have h2 := congrArg (fun m : Measure X.B.I.Ginf => c • m) h0
    simpa [smul_smul, ENNReal.mul_inv_cancel hc0 hct] using h2
  · rw [Measure.smul_apply, hcon, smul_zero]
  · intro s hs
    rw [Measure.map_smul, hinv s hs]
  · rw [Measure.map_smul, hmap, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]

theorem exists_at (hP : PinHaarEx) (γ : X.B.I.Ginf) :
    ∃ ν : Measure X.B.I.Ginf, (RegX X u u' γ → ν = Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
      (∃ μR, IsHaarOnSet X.B.I (StInf X u u' γ) μR ∧ IsQuotMeasS X.B.I μR ν) ∧
      ∀ w : Point D.host.E (D.R.rS + 1), (∃ g, IsPtRep X u u' w g) → gamW X u u' w = γ →
        ∃ μR, IsHaarOnSet X.B.I (StInf X u u' γ) μR ∧ IsQuotMeasS X.B.I μR ν ∧
          μR.map (stCoord X u' w γ) = muStab X w := by
  by_cases hreg : RegX X u u' γ
  · have hS := stInf_reg X u u' γ hreg
    have hH : Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' γ) (Measure.dirac 1) := by
      refine ⟨inferInstance, NeZero.ne _, ?_, ?_⟩
      · rw [hS, Measure.dirac_apply' _ (measurableSet_singleton 1).compl]
        simp
      · intro s hs
        rw [hS] at hs
        rw [Set.mem_singleton_iff.1 hs]
        simp
    have hQ : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I (Measure.dirac 1) (Formalism.L2.SG.ProjRows.muInf X.B.I) := by
      intro f _
      refine lintegral_congr fun x => ?_
      rw [lintegral_dirac, one_mul]
    refine ⟨Formalism.L2.SG.ProjRows.muInf X.B.I, fun _ => rfl, ⟨_, hH, hQ⟩, fun w hw hwγ => ⟨_, hH, hQ, ?_⟩⟩
    subst hwγ
    exact pin_reg X u u' hP hw hreg
  · by_cases hex : ∃ w, (∃ g, IsPtRep X u u' w g) ∧ gamW X u u' w = γ
    · obtain ⟨w, hw, rfl⟩ := hex
      obtain ⟨μR, hH, hmap⟩ := pinned_at X u u' hP hw
      obtain ⟨ν, hν⟩ := quot_St X u u' _ μR hH
      refine ⟨ν, fun h => absurd h hreg, ⟨μR, hH, hν⟩, fun w' hw' hw'γ => ?_⟩
      have h1 := isPtRep_gamW X u u' hw'
      rw [hw'γ] at h1
      have h2 : w' = w := pt_eq_of_rep X u u' h1 (isPtRep_gamW X u u' hw)
      subst h2
      exact ⟨μR, hH, hν, hmap⟩
    · obtain ⟨μR, hH⟩ := haar_St X u u' γ
      obtain ⟨ν, hν⟩ := quot_St X u u' γ μR hH
      exact ⟨ν, fun h => absurd h hreg, ⟨μR, hH, hν⟩, fun w hw hwγ => absurd ⟨w, hw, hwγ⟩ hex⟩

theorem stepPinExists_of (hP : PinHaarEx) : Formalism.L2.SG.NGAnalytic.StepPinExists := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ => ?_⟩
  choose ν h1 h2 h3 using exists_at X u u' hP
  exact ⟨ν, fun γ => ⟨h1 γ, h2 γ⟩, h1, fun w hw => h3 _ w hw rfl⟩

end Assembly

section Places

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def StV (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) : Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  {y | InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat y) ∧
    InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat ((γ v)⁻¹ * y * γ v))}

theorem stInf_eq_pi (u u' : D.what₂.Word) (γ : X.B.I.Ginf) : StInf X u u' γ = Set.univ.pi (StV X u u' γ) := by
  ext y
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h v
    exact ⟨h.1 v, h.2 v⟩
  · intro h
    exact ⟨fun v => (h v).1, fun v => (h v).2⟩

def stCoordV (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F)
    (y : Formalism.REAL.UJ (X.B.I.ε v)) : FreeE w → ℂ :=
  fun p => ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1)) *
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR ⟨p.1.1.1, by have := p.2.1; omega⟩))
      (uMat ((γ v)⁻¹ * y * γ v) *ᵥ frm X u' D.host.rdE v p.1.2)

theorem stCoord_eq (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) :
    stCoord X u' w γ = fun y v => stCoordV X u' w γ v (y v) := rfl

def PlaceHaar : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ : X.B.I.Ginf), IsPtRep X u u' w γ → ∀ v : InfinitePlace X.B.I.F,
    ∃ (μ : Measure (Formalism.REAL.UJ (X.B.I.ε v))) (c : ℝ≥0∞), IsHaarLoc (StV X u u' γ v) μ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
      μ.map (stCoordV X u' w γ v) = c • Measure.pi (fun _ : FreeE w => (volume : Measure ℂ))

theorem pi_smul {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0∞) [∀ i, SigmaFinite (c i • μ i)] :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  simp only [Measure.smul_apply, smul_eq_mul]

theorem sf_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    SigmaFinite (c • μ) := sf_smul_lemma μ hc

theorem muStab_eq (w : Point D.host.E (D.R.rS + 1)) :
    ∃ K : ℝ≥0∞, K ≠ 0 ∧ K ≠ ⊤ ∧ muStab X w =
      K • Measure.pi (fun _ : InfinitePlace X.B.I.F => Measure.pi (fun _ : FreeE w => (volume : Measure ℂ))) := by
  set k : ℝ≥0∞ := ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi) with hk
  have hkt : k ≠ ⊤ := ENNReal.ofReal_ne_top
  have hk0 : k ≠ 0 := by
    rw [hk, Ne, ENNReal.ofReal_eq_zero, not_le]
    have hrd := (Formalism.BasicNotions.rdE_pos_le D).1
    have hg : (0 : ℝ) < X.B.g := by
      rw [X.g_eq]
      have h0 := (D.host.g_prime 0).pos
      have h1 := (D.host.g_prime 1).pos
      exact_mod_cast Nat.mul_pos h0 h1
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    positivity
  haveI : SigmaFinite (k • (volume : Measure ℂ)) := sf_smul _ hkt
  have hin : Measure.pi (fun _ : FreeE w => k • (volume : Measure ℂ)) =
      (∏ _ : FreeE w, k) • Measure.pi (fun _ : FreeE w => (volume : Measure ℂ)) := pi_smul _ _
  set K1 := ∏ _ : FreeE w, k with hK1
  have hK1t : K1 ≠ ⊤ := ENNReal.prod_ne_top fun _ _ => hkt
  have hK10 : K1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => hk0
  haveI : SigmaFinite (K1 • Measure.pi (fun _ : FreeE w => (volume : Measure ℂ))) := sf_smul _ hK1t
  refine ⟨∏ _ : InfinitePlace X.B.I.F, K1, Finset.prod_ne_zero_iff.2 fun _ _ => hK10,
    ENNReal.prod_ne_top fun _ _ => hK1t, ?_⟩
  unfold muStab
  rw [← hk]
  simp_rw [hin]
  exact pi_smul _ _

private theorem pi_map_lemma_3 {ι : Type*} [Fintype ι] {α β : ι → Type*} [∀ i, MeasurableSpace (α i)]
    [∀ i, MeasurableSpace (β i)] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (ν : ∀ i, Measure (β i))
    [∀ i, SigmaFinite (ν i)] (f : ∀ i, α i → β i) (hf : ∀ i, AEMeasurable (f i) (μ i))
    (h : ∀ i, (μ i).map (f i) = ν i) : (Measure.pi μ).map (fun x i => f i (x i)) = Measure.pi ν := by
  have hF : AEMeasurable (fun x : ∀ i, α i => fun i => f i (x i)) (Measure.pi μ) :=
    aemeasurable_pi_lambda _ fun i => (hf i).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval μ i)
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply_of_aemeasurable hF (MeasurableSet.univ_pi hs)]
  have e : (fun x : ∀ i, α i => fun i => f i (x i)) ⁻¹' Set.univ.pi s = Set.univ.pi (fun i => f i ⁻¹' s i) := by
    ext x; simp [Set.mem_pi]
  rw [e, Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← h i, Measure.map_apply_of_aemeasurable (hf i) (hs i)]

theorem pinHaarEx_of_place (hP : PlaceHaar) : PinHaarEx := by
  intro D X u u' w hw
  set γ := gamW X u u' w with hγ
  have hrep : IsPtRep X u u' w γ := isPtRep_gamW X u u' hw
  choose μv cv hH hc0 hct hmap using hP D X u u' w γ hrep
  have hsf : ∀ v, SigmaFinite (μv v) := fun v => (hH v).1
  have hvol0 : Measure.pi (fun _ : FreeE w => (volume : Measure ℂ)) ≠ 0 := by
    rw [← Measure.measure_univ_ne_zero, Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => by
      rw [measure_univ_of_isAddLeftInvariant]; exact ENNReal.top_ne_zero
  have hae : ∀ v, AEMeasurable (stCoordV X u' w γ v) (μv v) := by
    intro v
    by_contra h
    have h2 := hmap v
    rw [Measure.map_of_not_aemeasurable h] at h2
    have h3 := congrArg (fun m : Measure _ => m Set.univ) h2.symm
    simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply] at h3
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact hc0 v h4
    · exact hvol0 (Measure.measure_univ_eq_zero.1 h4)
  obtain ⟨K, hK0, hKt, hK⟩ := muStab_eq X w
  haveI hsf2 : ∀ v, SigmaFinite (cv v • Measure.pi (fun _ : FreeE w => (volume : Measure ℂ))) :=
    fun v => sf_smul _ (hct v)
  have e1 : (Measure.pi μv).map (stCoord X u' w γ) =
      Measure.pi (fun v => cv v • Measure.pi (fun _ : FreeE w => (volume : Measure ℂ))) :=
    pi_map_lemma_3 μv _ (fun v => stCoordV X u' w γ v) hae hmap
  refine ⟨Measure.pi μv, (∏ v, cv v) * K⁻¹, ⟨inferInstance, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [← Measure.measure_univ_ne_zero, Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.2 fun v _ => Measure.measure_univ_ne_zero.2 (hH v).2.1
  · rw [stInf_eq_pi X u u' γ]
    have e : (Set.univ.pi (StV X u u' γ))ᶜ = ⋃ v, (fun y : X.B.I.Ginf => y v) ⁻¹' (StV X u u' γ v)ᶜ := by
      ext y; simp [Set.mem_pi]
    rw [e]
    exact measure_iUnion_null fun v => Measure.pi_eval_preimage_null (μ := μv) (hH v).2.2.1
  · intro s hs
    rw [stInf_eq_pi X u u' γ] at hs
    exact pi_map_lemma_3 μv μv (fun v x => s v * x) (fun v => (measurable_const_mul (s v)).aemeasurable)
      (fun v => (hH v).2.2.2 (s v) (hs v (Set.mem_univ v)))
  · exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ => hc0 v) (ENNReal.inv_ne_zero.2 hKt)
  · exact ENNReal.mul_ne_top (ENNReal.prod_ne_top fun v _ => hct v) (ENNReal.inv_ne_top.2 hK0)
  · rw [e1, pi_smul, hK, smul_smul, mul_assoc, ENNReal.inv_mul_cancel hK0 hKt, mul_one]

theorem stepPinExists_of_place (hP : PlaceHaar) : Formalism.L2.SG.NGAnalytic.StepPinExists := stepPinExists_of (pinHaarEx_of_place hP)

end Places

section Loc

def LocRootHaar : Prop :=
  ∀ (k r : ℕ), 1 ≤ k → ∀ (z z' : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    Formalism.QuantumDeterminants.inWb k r z' → 0 < Formalism.QuantumDeterminants.Tz k r z' →
    ∀ (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      g₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → Formalism.MainNotions.S.ZhatO k r z z' g₀ = ptMat p →
      ∃ (μ₀ : Measure (Formalism.QuantumDeterminants.Mt k r)) (c : ℝ≥0∞), Formalism.MainNotions.S.IsHaarOn (Formalism.MainNotions.S.Rset k r g₀) μ₀ ∧ c ≠ 0 ∧
        c ≠ ⊤ ∧ μ₀.map (Formalism.MainNotions.S.rootCoords k r z' p) = c • volume

end Loc

end Formalism.L2.SG.NGPin
