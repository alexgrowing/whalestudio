import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.QuotIndepPf

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Chart

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  {C : Type*} [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]

theorem chart_closed (S : Set H) (κ : H → C) (φ : C → H) (hκ : Continuous κ) (hφ : Continuous φ)
    (hφS : ∀ c, φ c ∈ S) (hφκ : ∀ y ∈ S, φ (κ y) = y) : IsClosed S := by
  have hS : S = {y | φ (κ y) = y} := by
    ext y
    constructor
    · exact hφκ y
    · intro h
      have h' : φ (κ y) = y := h
      exact h' ▸ hφS (κ y)
  rw [hS]
  exact isClosed_eq (hφ.comp hκ) continuous_id

theorem map_comm_eq {C' H' : Type*} [MeasurableSpace C'] [MeasurableSpace H'] (μC : Measure C') (φ : C' → H')
    (hφm : Measurable φ) (T : C' → C') (hT : MeasurePreserving T μC μC) (F : H' → H') (hFm : Measurable F)
    (hcomm : ∀ c, F (φ c) = φ (T c)) : (μC.map φ).map F = μC.map φ := by
  rw [Measure.map_map hFm hφm]
  have h : F ∘ φ = φ ∘ T := funext hcomm
  rw [h, ← Measure.map_map hφm hT.measurable, hT.map_eq]

theorem chart_haar (S : Set H) (κ : H → C) (φ : C → H) (μC : Measure C) (hκ : Continuous κ) (hφ : Continuous φ)
    (hφS : ∀ c, φ c ∈ S) (hφκ : ∀ y ∈ S, φ (κ y) = y) (hκφ : ∀ c, κ (φ c) = c)
    (h1 : (1 : H) ∈ S) (hmul : ∀ s ∈ S, ∀ t ∈ S, s * t ∈ S) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hL : ∀ s ∈ S, MeasurePreserving (fun c => κ (s * φ c)) μC μC)
    (hI : MeasurePreserving (fun c => κ (φ c)⁻¹) μC μC)
    [SigmaFinite μC] [IsFiniteMeasureOnCompacts μC] [Measure.IsOpenPosMeasure μC] [Nonempty C] :
    SigmaFinite (μC.map φ) ∧ μC.map φ ≠ 0 ∧ μC.map φ Sᶜ = 0 ∧
      (∀ s ∈ S, (μC.map φ).map (fun x => s * x) = μC.map φ) ∧
      (μC.map φ).map (fun s => s⁻¹) = μC.map φ ∧ (μC.map φ).map κ = μC ∧
      ∃ b : H → ℝ≥0∞, Measurable b ∧ (∀ x, b x ≠ ⊤) ∧ ∀ x, ∫⁻ s, b (s * x) ∂(μC.map φ) = 1 := by
  have hSc : IsClosed S := chart_closed S κ φ hκ hφ hφS hφκ
  have hrange : Set.range φ = S := by
    ext y; constructor
    · rintro ⟨c, rfl⟩; exact hφS c
    · intro hy; exact ⟨κ y, hφκ y hy⟩
  have hemb : MeasurableEmbedding φ :=
    MeasurableEmbedding.of_measurable_inverse hφ.measurable (hrange ▸ hSc.measurableSet)
      hκ.measurable hκφ
  have hσ : SigmaFinite (μC.map φ) := hemb.sigmaFinite_map
  have hμC0 : μC ≠ 0 := by
    intro h
    have h2 := (isOpen_univ.measure_pos μC Set.univ_nonempty).ne'
    rw [h] at h2; exact h2 rfl
  have hne : μC.map φ ≠ 0 := fun h => hμC0 ((Measure.map_eq_zero_iff hφ.measurable.aemeasurable).mp h)
  have hcompl : μC.map φ Sᶜ = 0 := by
    rw [Measure.map_apply hφ.measurable hSc.isOpen_compl.measurableSet]
    have h2 : φ ⁻¹' Sᶜ = ∅ := by ext c; simp [hφS c]
    rw [h2, measure_empty]
  have hleft : ∀ s ∈ S, (μC.map φ).map (fun x => s * x) = μC.map φ := fun s hs =>
    map_comm_eq μC φ hφ.measurable _ (hL s hs) _ (measurable_const_mul s)
      (fun c => (hφκ _ (hmul s hs _ (hφS c))).symm)
  have hinvν : (μC.map φ).map (fun s => s⁻¹) = μC.map φ :=
    map_comm_eq μC φ hφ.measurable _ hI _ measurable_inv (fun c => (hφκ _ (hinv _ (hφS c))).symm)
  have hκmap : (μC.map φ).map κ = μC := by
    rw [Measure.map_map hκ.measurable hφ.measurable]
    have h2 : κ ∘ φ = id := funext hκφ
    rw [h2, Measure.map_id]
  refine ⟨hσ, hne, hcompl, hleft, hinvν, hκmap, ?_⟩
  have hright : ∀ t ∈ S, (μC.map φ).map (fun x => x * t) = μC.map φ := by
    intro t ht
    have hc : (fun x : H => x * t) = (fun x : H => x⁻¹) ∘ (fun x => t⁻¹ * x) ∘ (fun x : H => x⁻¹) := by
      funext x; simp [_root_.mul_inv_rev]
    rw [hc, ← Measure.map_map measurable_inv ((measurable_const_mul _).comp measurable_inv),
      ← Measure.map_map (measurable_const_mul _) measurable_inv, hinvν, hleft _ (hinv t ht), hinvν]
  let S' : Subgroup H :=
    { carrier := S, mul_mem' := fun {a b} ha hb => hmul a ha b hb, one_mem' := h1,
      inv_mem' := fun {a} ha => hinv a ha }
  have hS'c : IsClosed (S' : Set H) := hSc
  let e : C ≃ₜ S' :=
    { toFun := fun c => ⟨φ c, hφS c⟩, invFun := fun y => κ y, left_inv := fun c => hκφ c,
      right_inv := fun y => Subtype.ext (hφκ y y.2), continuous_toFun := hφ.subtype_mk _,
      continuous_invFun := hκ.comp continuous_subtype_val }
  let μS : Measure S' := μC.map e.toMeasurableEquiv
  have hval : (μS.map Subtype.val : Measure H) = μC.map φ := by
    rw [Measure.map_map measurable_subtype_coe e.toMeasurableEquiv.measurable]
    rfl
  have hvemb : MeasurableEmbedding (Subtype.val : S' → H) :=
    MeasurableEmbedding.subtype_coe hS'c.measurableSet
  haveI : μS.IsMulRightInvariant := ⟨fun g => by
    have h2 : (μS.map (fun x => x * g)).map Subtype.val = μS.map Subtype.val := by
      rw [Measure.map_map measurable_subtype_coe (measurable_mul_const g)]
      have h3 : (Subtype.val ∘ fun x : S' => x * g) = (fun y : H => y * (g : H)) ∘ Subtype.val := by
        funext x; simp
      rw [h3, ← Measure.map_map (measurable_mul_const _) measurable_subtype_coe, hval, hright _ g.2]
    rw [← hvemb.comap_map (μS.map (fun x => x * g)), h2, hvemb.comap_map]⟩
  haveI : IsFiniteMeasureOnCompacts μS := ⟨fun K hK => by
    show μC.map e.toMeasurableEquiv K < ⊤
    rw [MeasurableEquiv.map_apply, Homeomorph.toMeasurableEquiv_coe, ← Homeomorph.image_symm]
    exact (hK.image e.symm.continuous).measure_lt_top⟩
  haveI : Measure.IsOpenPosMeasure μS := ⟨fun U hU hne' => by
    show μC.map e.toMeasurableEquiv U ≠ 0
    rw [MeasurableEquiv.map_apply, Homeomorph.toMeasurableEquiv_coe]
    exact (hU.preimage e.continuous).measure_ne_zero μC (hne'.preimage e.surjective)⟩
  obtain ⟨b, hb, hb1⟩ := Formalism.L2.SG.Pf.QuotIndep.QuotIndepPf.exists_bruhat S' hS'c μS
  have hb1' : ∀ x, ∫⁻ s, b (s * x) ∂(μC.map φ) = 1 := by
    intro x
    rw [← hval, lintegral_map (show Measurable (fun s : H => b (s * x)) from hb.comp (measurable_mul_const x)) measurable_subtype_coe]
    exact hb1 x
  refine ⟨fun x => if b x = ⊤ then 0 else b x, ?_, ?_, fun x => ?_⟩
  · exact Measurable.ite (hb (measurableSet_singleton ⊤)) measurable_const hb
  · intro x
    show (if b x = ⊤ then 0 else b x) ≠ ⊤
    split_ifs with h
    · exact ENNReal.zero_ne_top
    · exact h
  · rw [← hb1' x]
    apply lintegral_congr_ae
    have h4 := ae_lt_top (μ := μC.map φ) (show Measurable (fun s : H => b (s * x)) from hb.comp (measurable_mul_const x))
      (by rw [hb1' x]; exact ENNReal.one_ne_top)
    filter_upwards [h4] with s hs
    have hs' : b (s * x) ≠ ⊤ := hs.ne
    simp [hs']

end Chart

variable {D : D7}

theorem stCoordV_continuous (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) : Continuous (stCoordV X u' w γ v) := by
  unfold stCoordV Formalism.L2.SG.HidaSetting.hJ
  have hu : Continuous fun y : Formalism.REAL.UJ (X.B.I.ε v) => uMat ((γ v)⁻¹ * y * γ v) :=
    (Units.continuous_val.comp continuous_subtype_val).comp
      ((continuous_const.mul continuous_id).mul continuous_const)
  apply continuous_pi
  intro p
  exact continuous_const.mul
    (continuous_const.dotProduct (continuous_const.matrix_mulVec (hu.matrix_mulVec continuous_const)))

theorem muStabV_eq_smul (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : Point D.host.E (D.R.rS + 1)) :
    muStabV X w = ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi) ^ Fintype.card (FreeE w) •
      (volume : Measure (FreeE w → ℂ)) := by
  unfold muStabV
  have h : ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi) • (volume : Measure ℂ) =
      (ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi)).toNNReal • (volume : Measure ℂ) := by
    ext s hs
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def,
      ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]
  simp only [h]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, MeasureTheory.volume_pi, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]

def StVGeo (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ v : InfinitePlace X.B.I.F,
    ((1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ StV X u u' (gamW X u u' w) v ∧
      (∀ s ∈ StV X u u' (gamW X u u' w) v, ∀ t ∈ StV X u u' (gamW X u u' w) v,
        s * t ∈ StV X u u' (gamW X u u' w) v) ∧
      ∀ s ∈ StV X u u' (gamW X u u' w) v, s⁻¹ ∈ StV X u u' (gamW X u u' w) v) ∧
    ∃ φ : (FreeE w → ℂ) → Formalism.REAL.UJ (X.B.I.ε v), Continuous φ ∧
      (∀ c, φ c ∈ StV X u u' (gamW X u u' w) v) ∧
      (∀ y ∈ StV X u u' (gamW X u u' w) v, φ (stCoordV X u' w (gamW X u u' w) v y) = y) ∧
      (∀ c, stCoordV X u' w (gamW X u u' w) v (φ c) = c) ∧
      (∀ s ∈ StV X u u' (gamW X u u' w) v,
        MeasurePreserving (fun c => stCoordV X u' w (gamW X u u' w) v (s * φ c))) ∧
      MeasurePreserving (fun c => stCoordV X u' w (gamW X u u' w) v (φ c)⁻¹)

theorem muStabV_sigmaFinite (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : Point D.host.E (D.R.rS + 1)) :
    SigmaFinite (muStabV X w) := by
  unfold muStabV
  have h : ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi) • (volume : Measure ℂ) =
      (ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi)).toNNReal • (volume : Measure ℂ) := by
    ext s hs
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def,
      ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]
  simp only [h]
  infer_instance

theorem stCoord_measurable (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ : X.B.I.Ginf) : Measurable (stCoord X u' w γ) := by
  apply Continuous.measurable
  unfold stCoord Formalism.L2.SG.HidaSetting.hJ
  apply continuous_pi; intro v
  apply continuous_pi; intro p
  have hu : Continuous fun y : X.B.I.Ginf => uMat ((γ⁻¹ * y * γ) v) :=
    (Units.continuous_val.comp continuous_subtype_val).comp
      ((continuous_apply v).comp ((continuous_const.mul continuous_id).mul continuous_const))
  exact continuous_const.mul
    (continuous_const.dotProduct (continuous_const.matrix_mulVec (hu.matrix_mulVec continuous_const)))

theorem locUni_of (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hG : StVGeo X u u') : LocUni X u u' := by
  intro w hok μR hμR hmap v
  obtain ⟨⟨h1, hmul, hinv⟩, φ, hφ, hφS, hφκ, hκφ, hL, hI⟩ := hG w hok v
  have heq := muStabV_eq_smul X w
  haveI := muStabV_sigmaFinite X w
  have hct : ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi) ^ Fintype.card (FreeE w) ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hc0 : ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi) ^ Fintype.card (FreeE w) ≠ 0 := by
    rcases Nat.eq_zero_or_pos (Fintype.card (FreeE w)) with hcard | hcard
    · rw [hcard, pow_zero]; exact one_ne_zero
    · apply pow_ne_zero
      intro hK0
      apply hμR.2.1
      have hz : ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi) • (volume : Measure ℂ) = 0 := by
        rw [hK0, zero_smul]
      have h2 : (μR.map (stCoord X u' w (gamW X u u' w))) Set.univ = μR Set.univ := by
        rw [Measure.map_apply (stCoord_measurable X u' w _) MeasurableSet.univ, Set.preimage_univ]
      have hunivR : μR Set.univ = 0 := by
        rw [← h2, hmap]
        unfold muStab
        simp only [hz]
        haveI : Nonempty (FreeE w) := Fintype.card_pos_iff.mp hcard
        rw [Measure.pi_univ]
        apply Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary _))
        rw [Measure.pi_univ]
        apply Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary _))
        simp
      exact Measure.measure_univ_eq_zero.mp hunivR
  haveI : IsFiniteMeasureOnCompacts (muStabV X w) := ⟨fun Kc hKc => by
    rw [heq, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hct.lt_top hKc.measure_lt_top⟩
  haveI : Measure.IsOpenPosMeasure (muStabV X w) := by
    rw [heq]; exact Measure.isOpenPosMeasure_smul _ hc0
  have hMP : ∀ f : (FreeE w → ℂ) → (FreeE w → ℂ), MeasurePreserving f volume volume →
      MeasurePreserving f (muStabV X w) (muStabV X w) := by
    intro f hf
    rw [heq]
    exact ⟨hf.measurable, by rw [Measure.map_smul, hf.map_eq]⟩
  obtain ⟨hσ, hne, hc, hleft, hinvν, hκm, b, hb, hbt, hb1⟩ :=
    chart_haar (StV X u u' (gamW X u u' w) v) (stCoordV X u' w (gamW X u u' w) v) φ (muStabV X w)
      (stCoordV_continuous X u' w _ v) hφ hφS hφκ hκφ h1 hmul hinv (fun s hs => hMP _ (hL s hs))
      (hMP _ hI)
  exact ⟨(muStabV X w).map φ, ⟨hσ, hne, hc, hleft⟩, hinvν, hκm, b, hb, hbt, hb1⟩

theorem globProd_of (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hG : StVGeo X u u') :
    GlobProd X u u' := by
  intro w hok μR hμR hmap μRv hRv
  have hG' := fun v => (hG w hok v).2
  choose φ hφc hφS hφκ hκφ hL hI using hG'
  haveI : ∀ v, SigmaFinite (μRv v) := fun v => (hRv v).1.1
  let Φ : (InfinitePlace X.B.I.F → FreeE w → ℂ) → X.B.I.Ginf := fun c v => φ v (c v)
  have hΦm : Measurable Φ :=
    measurable_pi_lambda _ fun v => (hφc v).measurable.comp (measurable_pi_apply v)
  have hsc := stCoord_measurable X u' w (gamW X u u' w)
  have hleft : ∀ y ∈ StInf X u u' (gamW X u u' w), Φ (stCoord X u' w (gamW X u u' w) y) = y := by
    intro y hy
    funext v
    exact hφκ v (y v) ⟨hy.1 v, hy.2 v⟩
  have hae : ∀ᵐ y ∂μR, y ∈ StInf X u u' (gamW X u u' w) := ae_iff.mpr hμR.2.2.1
  have h1 : μR = (muStab X w).map Φ := by
    calc μR = μR.map id := Measure.map_id.symm
      _ = μR.map (Φ ∘ stCoord X u' w (gamW X u u' w)) :=
          Measure.map_congr (by filter_upwards [hae] with y hy; exact (hleft y hy).symm)
      _ = (μR.map (stCoord X u' w (gamW X u u' w))).map Φ := (Measure.map_map hΦm hsc).symm
      _ = (muStab X w).map Φ := by rw [hmap]
  have hae2 : ∀ᵐ y ∂(Measure.pi μRv), y ∈ StInf X u u' (gamW X u u' w) := by
    have h3 : ∀ v, ∀ᵐ y ∂(Measure.pi μRv), y v ∈ StV X u u' (gamW X u u' w) v := by
      intro v
      rw [ae_iff]
      exact Measure.pi_eval_preimage_null μRv (hRv v).1.2.2.1
    filter_upwards [ae_all_iff.mpr h3] with y hy
    exact ⟨fun v => (hy v).1, fun v => (hy v).2⟩
  have hall : ∀ v, (μRv v).map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w :=
    fun v => (hRv v).2
  haveI : ∀ v, SigmaFinite ((μRv v).map (stCoordV X u' w (gamW X u u' w) v)) := fun v => by
    rw [hall v]; exact muStabV_sigmaFinite X w
  have hmap2 : (Measure.pi μRv).map (stCoord X u' w (gamW X u u' w)) = muStab X w := by
    rw [show stCoord X u' w (gamW X u u' w) =
        (fun y v => stCoordV X u' w (gamW X u u' w) v (y v)) from rfl]
    rw [Measure.pi_map_pi (fun v => (stCoordV_continuous X u' w _ v).measurable.aemeasurable)]
    simp only [hall]
    rfl
  have h2 : Measure.pi μRv = (muStab X w).map Φ := by
    calc Measure.pi μRv = (Measure.pi μRv).map id := Measure.map_id.symm
      _ = (Measure.pi μRv).map (Φ ∘ stCoord X u' w (gamW X u u' w)) :=
          Measure.map_congr (by filter_upwards [hae2] with y hy; exact (hleft y hy).symm)
      _ = ((Measure.pi μRv).map (stCoord X u' w (gamW X u u' w))).map Φ :=
          (Measure.map_map hΦm hsc).symm
      _ = (muStab X w).map Φ := by rw [hmap2]
  rw [h1, h2]

theorem ooQuot_geo (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) (hR : StRel X u u') (hG : StVGeo X u u') :
    ∃ νl, (∀ w, OkPt X u u' w → LocPin X u u' w νl) ∧ Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' νq νl :=
  ooQuot_pin X u u' νq hN hR (locUni_of X u u' hG) (globProd_of X u u' hG)

end Formalism.L2.SG.Pf.Carrier.JointQuot
