import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSlice

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open PositivityTheory.RgBcC.Bridge (along atW)
open scoped Classical InnerProductSpace

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PositivityTheory.Rg.BcB.CG

namespace Slice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

abbrev RB (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : InfinitePlace E) : Type :=
  (InfinitePlace E → G a) × (({w : InfinitePlace E // w ≠ v} → G b) × Hf E a b)

def restB [MeasurableSpace (G a)] [MeasurableSpace (G b)] [MeasurableSpace (Hf E a b)] (μa : Measure (G a))
    (μb : Measure (G b)) (ν : Measure (Hf E a b)) (v : InfinitePlace E) : Measure (RB E a b v) :=
  (Measure.pi fun _ : InfinitePlace E => μa).prod ((Measure.pi fun _ : {w : InfinitePlace E // w ≠ v} => μb).prod ν)

def ιB (v : InfinitePlace E) (t : G b) : H E a b := splitH a b (1, (Pi.mulSingle v t, 1))

def σB (v : InfinitePlace E) (r : RB E a b v) : H E a b :=
  splitH a b (r.1, (fun w => if h : w = v then 1 else r.2.1 ⟨w, h⟩, r.2.2))

variable {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [Fintype κ]

abbrev ebB (M : Mods E b) (v : InfinitePlace E) (q : Ix (M v)) : (M v).V := stdOrthonormalBasis ℂ (M v).V q

def cB (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (i j : Io Ma Mb κ)
    (r : RB E a b v) : ℂ :=
  (∏ w, ent (Ma w) (ka w (r.1 w).val) (i.1.1 w) (j.1.1 w)) *
    (∏ w : {w : InfinitePlace E // w ≠ v}, ent (Mb w) (kb w (r.2.1 w).val) (i.1.2 w) (j.1.2 w)) * ψ i.2 j.2 r.2.2

section Meas

variable [MeasurableSpace (G a)] [MeasurableSpace (G b)] [MeasurableSpace (Hf E a b)]

def RvB (v : InfinitePlace E) (μa : Measure (G a)) (μb : Measure (G b)) (ν : Measure (Hf E a b)) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (p : H E a b) :
    (Mb v).V :=
  ∑ q : Ix (Mb v), (∑ j ∈ Finset.univ.filter (fun j : Io Ma Mb κ => j.1.2 v = q),
    ∫ r, cB v ka kb ψ i j r * f j (p * σB v r) ∂restB μa μb ν v) • ebB Mb v q

def FB (v : InfinitePlace E) (μa : Measure (G a)) (μb : Measure (G b)) (ν : Measure (Hf E a b)) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (m₁ : GA E a)
    (y : GA E b) : Mat b → (Mb v).V := fun x =>
  if hx : x ∈ GLs b then RvB v μa μb ν ka kb ψ f i ((m₁, y) * ιB v (GeneralLinearGroup.mkOfDetNeZero x hx)) else 0

end Meas

section Main

variable [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] {μa : Measure (G a)} [μa.IsHaarMeasure]
  {μb : Measure (G b)} [μb.IsHaarMeasure] {ν : Measure (Hf E a b)} [ν.IsHaarMeasure]

def eqB (v : InfinitePlace E) :
    ((InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) ≃ᵐ G b × RB E a b v :=
  ((MeasurableEquiv.refl (InfinitePlace E → G a)).prodCongr
    (((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : InfinitePlace E => G b) (fun w => w = v)).prodCongr
      (MeasurableEquiv.refl (Hf E a b))).trans
      (MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.funUnique {w : InfinitePlace E // w = v} (G b)).prodCongr
        (MeasurableEquiv.refl _))))).trans
  (MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodAssoc))

theorem eqB_symm_apply (v : InfinitePlace E) (q : G b × RB E a b v) :
    (eqB (a := a) v).symm q = (q.2.1, (fun w => if h : w = v then q.1 else q.2.2.1 ⟨w, h⟩, q.2.2.2)) := by
  rfl

theorem splitH_eqB_symm (v : InfinitePlace E) (q : G b × RB E a b v) :
    splitH a b ((eqB v).symm q) = ιB v q.1 * σB v q.2 := by
  rw [eqB_symm_apply, ιB, σB, ← map_mul]
  congr 1
  refine Prod.ext (by simp) (Prod.ext (funext fun w => ?_) (by simp))
  by_cases h : w = v
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

theorem measurePreserving_eqB (μa : Measure (G a)) [SigmaFinite μa] (μb : Measure (G b)) [SigmaFinite μb]
    (ν : Measure (Hf E a b)) [SigmaFinite ν] (v : InfinitePlace E) :
    MeasurePreserving (eqB (a := a) v) ((Measure.pi fun _ => μa).prod ((Measure.pi fun _ => μb).prod ν))
      (μb.prod (restB μa μb ν v)) := by
  have h1 := (measurePreserving_piEquivPiSubtypeProd (fun _ : InfinitePlace E => μb) (fun w => w = v)).prod
    (MeasurePreserving.id ν)
  have h2 := measurePreserving_prodAssoc (Measure.pi fun _ : {w : InfinitePlace E // w = v} => μb)
    (Measure.pi fun _ : {w : InfinitePlace E // ¬ w = v} => μb) ν
  have h3 := (measurePreserving_funUnique μb {w : InfinitePlace E // w = v}).prod
    (MeasurePreserving.id ((Measure.pi fun _ : {w : InfinitePlace E // ¬ w = v} => μb).prod ν))
  have he1 := h3.comp (h2.comp (by convert h1 <;> rfl))
  have h4 := (MeasurePreserving.id (Measure.pi fun _ : InfinitePlace E => μa)).prod he1
  have h5 := (measurePreserving_prodAssoc (Measure.pi fun _ : InfinitePlace E => μa) μb
    ((Measure.pi fun _ : {w : InfinitePlace E // ¬ w = v} => μb).prod ν)).symm _
  have h6 := (Measure.measurePreserving_swap (μ := Measure.pi fun _ : InfinitePlace E => μa) (ν := μb)).prod
    (MeasurePreserving.id ((Measure.pi fun _ : {w : InfinitePlace E // ¬ w = v} => μb).prod ν))
  have h7 := measurePreserving_prodAssoc μb (Measure.pi fun _ : InfinitePlace E => μa)
    ((Measure.pi fun _ : {w : InfinitePlace E // ¬ w = v} => μb).prod ν)
  exact h7.comp (h6.comp (h5.comp h4))

theorem integral_splitB (hF : CompatFub) (D : Dom E a b) (hC : Compat D μa μb ν) (v : InfinitePlace E)
    (Q : H E a b → ℂ) (hQ : Continuous Q) (hQs : HasCompactSupport Q) :
    Integrable (fun q : G b × RB E a b v => Q (ιB v q.1 * σB v q.2)) (μb.prod (restB μa μb ν v)) ∧
      ∫ g, Q g ∂D.μ = ∫ t, ∫ r, Q (ιB v t * σB v r) ∂restB μa μb ν v ∂μb := by
  haveI : SigmaFinite μa := inferInstance
  haveI : SigmaFinite μb := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite (Measure.pi fun _ : InfinitePlace E => μa) := inferInstance
  haveI : SigmaFinite (Measure.pi fun _ : InfinitePlace E => μb) := inferInstance
  haveI : SigmaFinite (Measure.pi fun _ : {w : InfinitePlace E // w ≠ v} => μb) := inferInstance
  haveI : SigmaFinite ((Measure.pi fun _ : InfinitePlace E => μb).prod ν) := inferInstance
  haveI : SigmaFinite (restB μa μb ν v) := by unfold restB; infer_instance
  haveI : IsFiniteMeasureOnCompacts (Measure.pi fun _ : InfinitePlace E => μa) := inferInstance
  haveI : IsFiniteMeasureOnCompacts (Measure.pi fun _ : InfinitePlace E => μb) := inferInstance
  haveI : IsFiniteMeasureOnCompacts ((Measure.pi fun _ : InfinitePlace E => μb).prod ν) := inferInstance
  set M := (Measure.pi fun _ : InfinitePlace E => μa).prod ((Measure.pi fun _ : InfinitePlace E => μb).prod ν) with hM
  haveI : IsFiniteMeasureOnCompacts M := by rw [hM]; infer_instance
  have hmp := measurePreserving_eqB (a := a) μa μb ν v
  have hQ' : Continuous (fun z => Q (splitH a b z)) := hQ.comp (splitH a b).continuous
  have hQs' : HasCompactSupport (fun z => Q (splitH a b z)) := hQs.comp_homeomorph (splitH a b).toHomeomorph
  have hI : Integrable (fun z => Q (splitH a b z)) M := hQ'.integrable_of_hasCompactSupport hQs'
  have hcomp : (fun z => Q (splitH a b z)) ∘ (eqB (a := a) v).symm = fun q => Q (ιB v q.1 * σB v q.2) := by
    funext q
    simp only [Function.comp_apply, splitH_eqB_symm]
  have hI2 : Integrable (fun q : G b × RB E a b v => Q (ιB v q.1 * σB v q.2)) (μb.prod (restB μa μb ν v)) := by
    rw [← hcomp]
    exact ((hmp.symm _).integrable_comp_emb (eqB v).symm.measurableEmbedding).2 hI
  refine ⟨hI2, ?_⟩
  have e1 : ∫ z, Q (splitH a b z) ∂M =
      ∫ ya, ∫ yb, ∫ h, Q (splitH a b (ya, (yb, h))) ∂ν ∂(Measure.pi fun _ => μb) ∂(Measure.pi fun _ => μa) := by
    rw [integral_prod _ hI]
    refine integral_congr_ae ?_
    filter_upwards [hI.prod_right_ae] with ya hya
    exact integral_prod _ hya
  have e2 : ∫ z, Q (splitH a b z) ∂M = ∫ q, Q (ιB v q.1 * σB v q.2) ∂(μb.prod (restB μa μb ν v)) := by
    rw [← (hmp.symm _).integral_comp' (g := fun z => Q (splitH a b z))]
    simp only [splitH_eqB_symm]
  rw [← integral_prod _ hI2, ← e2, e1]
  exact hF E a b D μa μb ν hC Q hQ hQs

theorem prod_split {X : Type} (v : InfinitePlace E) (F : InfinitePlace E → X → ℂ) (t : X)
    (r : {w : InfinitePlace E // w ≠ v} → X) :
    ∏ w, F w (if h : w = v then t else r ⟨w, h⟩) = F v t * ∏ w : {w : InfinitePlace E // w ≠ v}, F w (r w) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ v]
  simp only [dif_pos]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [dif_neg w.2]

theorem tens_ισB (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (i j : Io Ma Mb κ) (t : G b) (r : RB E a b v) :
    tens ka kb ψ i j (ιB v t * σB v r) = ent (Mb v) (kb v t.val) (i.1.2 v) (j.1.2 v) * cB v ka kb ψ i j r := by
  rw [← splitH_eqB_symm v (t, r), eqB_symm_apply]
  simp only [tens, entA, gInf_splitH₁, gInf_splitH₂, hFin_splitH, cB]
  have h := prod_split v (fun w (x : G b) => ent (Mb w) (kb w x.val) (i.1.2 w) (j.1.2 w)) t r.2.1
  rw [h]
  ring

theorem conv_sliceB (hF : CompatFub) (D : Dom E a b) (hC : Compat D μa μb ν) (v : InfinitePlace E) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (hT : IsTestM (tens ka kb ψ))
    (hf : ∀ i, Continuous (f i)) (i : Io Ma Mb κ) (p : H E a b) :
    conv D.μ (tens ka kb ψ) f i p =
      ∫ t, ⟪ebB Mb v (i.1.2 v), kb v t.val (RvB v μa μb ν ka kb ψ f i (p * ιB v t))⟫_ℂ ∂μb := by
  haveI : SigmaFinite μa := inferInstance
  haveI : SigmaFinite μb := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite (restB μa μb ν v) := by unfold restB; infer_instance
  have hQ : ∀ j, Continuous (fun g => tens ka kb ψ i j g * f j (p * g)) ∧
      HasCompactSupport (fun g => tens ka kb ψ i j g * f j (p * g)) := fun j =>
    ⟨(hT i j).1.mul ((hf j).comp (continuous_const.mul continuous_id)), (hT i j).2.mul_right⟩
  have hs := fun j => integral_splitB hF D hC v _ (hQ j).1 (hQ j).2
  have hpt : ∀ j t, ∫ r, tens ka kb ψ i j (ιB v t * σB v r) * f j (p * (ιB v t * σB v r)) ∂restB μa μb ν v =
      ent (Mb v) (kb v t.val) (i.1.2 v) (j.1.2 v) *
        ∫ r, cB v ka kb ψ i j r * f j (p * ιB v t * σB v r) ∂restB μa μb ν v := by
    intro j t
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [tens_ισB, mul_assoc]
  have hsplit : ∀ j, ∫ g, tens ka kb ψ i j g * f j (p * g) ∂D.μ = ∫ t, ent (Mb v) (kb v t.val) (i.1.2 v) (j.1.2 v) *
      ∫ r, cB v ka kb ψ i j r * f j (p * ιB v t * σB v r) ∂restB μa μb ν v ∂μb := fun j =>
    (hs j).2.trans (integral_congr_ae (ae_of_all _ fun t => hpt j t))
  have hint : ∀ j, Integrable (fun t => ent (Mb v) (kb v t.val) (i.1.2 v) (j.1.2 v) *
      ∫ r, cB v ka kb ψ i j r * f j (p * ιB v t * σB v r) ∂restB μa μb ν v) μb := fun j =>
    ((hs j).1.integral_prod_left).congr (ae_of_all _ fun t => hpt j t)
  show ∑ j, ∫ g, tens ka kb ψ i j g * f j (p * g) ∂D.μ = _
  rw [Finset.sum_congr rfl fun j _ => hsplit j, ← integral_finset_sum _ fun j _ => hint j]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [RvB, map_sum, map_smul, inner_sum, inner_smul_right]
  rw [← Finset.sum_fiberwise Finset.univ (fun j : Io Ma Mb κ => j.1.2 v)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.1 hj).2]
  simp only [ent, ebB]
  ring

theorem along_eqB (v : InfinitePlace E) (m₁ : GA E a) (y : GA E b) (φ : H E a b → ℂ) {x : Mat b} (hx : x ∈ GLs b) :
    along v y (fun z => φ (m₁, z)) x = φ ((m₁, y) * ιB v (GeneralLinearGroup.mkOfDetNeZero x hx)) := by
  set U : GL (Fin b) (Cinf E) := Units.map (Matrix.piRingEquiv (n := Fin b) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
    (MulEquiv.piUnits.symm (Pi.mulSingle v (GeneralLinearGroup.mkOfDetNeZero x hx))) with hU
  have e : atW v x = toL U.val := by
    funext i j w
    by_cases h : w = v
    · subst h; (simp [atW, hU, toL]) <;> rfl
    · simp [atW, hU, toL, h, Pi.mulSingle_eq_of_ne h]
  have e2 : (m₁, y) * ιB (a := a) v (GeneralLinearGroup.mkOfDetNeZero x hx) = (m₁, y * infGL E b U) := by
    simp [ιB, splitH_apply, infP, hU]
  rw [along, e, chart_val, e2]

omit [BorelSpace (G a)] [BorelSpace (G b)] [BorelSpace (Hf E a b)] in
theorem continuous_ιB (v : InfinitePlace E) : Continuous (ιB (a := a) (b := b) v) := by
  have h1 : Continuous fun t : G b => (Pi.mulSingle v t : InfinitePlace E → G b) := by
    refine continuous_pi fun w => ?_
    by_cases h : w = v
    · subst h; simp only [Pi.mulSingle_eq_same]; exact continuous_id
    · simpa [Pi.mulSingle_eq_of_ne h] using continuous_const
  exact (splitH a b).continuous.comp (continuous_const.prodMk (h1.prodMk continuous_const))

omit [BorelSpace (G a)] [BorelSpace (G b)] [BorelSpace (Hf E a b)] in
theorem continuous_σB (v : InfinitePlace E) : Continuous (σB (a := a) (b := b) v) := by
  refine (splitH a b).continuous.comp (continuous_fst.prodMk (Continuous.prodMk (continuous_pi fun w => ?_)
    (continuous_snd.comp continuous_snd)))
  by_cases h : w = v
  · simp only [h, dif_pos]; exact continuous_const
  · simp only [h, dif_neg, not_false_eq_true]
    exact (continuous_apply _).comp (continuous_fst.comp continuous_snd)

theorem ιB_mul (v : InfinitePlace E) (s t : G b) : ιB (a := a) v (s * t) = ιB v s * ιB v t := by
  rw [ιB, ιB, ιB, ← map_mul, Pi.mulSingle_mul]
  simp

omit [BorelSpace (G a)] [BorelSpace (G b)] [BorelSpace (Hf E a b)] in
theorem cB_props (v : InfinitePlace E) {ka : Kers Ma} {kb : Kers Mb} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i j : Io Ma Mb κ) :
    Continuous (cB v ka kb ψ i j) ∧ HasCompactSupport (cB v ka kb ψ i j) := by
  refine ⟨?_, ?_⟩
  · refine ((continuous_finset_prod _ fun w _ => ?_).mul (continuous_finset_prod _ fun w _ => ?_)).mul
      ((hψ i.2 j.2).1.comp (continuous_snd.comp continuous_snd))
    · exact continuous_ent ((hka w).1.comp ((continuous_apply w).comp continuous_fst)) _ _
    · exact continuous_ent ((hkb w).1.comp ((continuous_apply w).comp (continuous_fst.comp continuous_snd))) _ _
  · have hK : IsCompact ((Set.univ.pi fun w : InfinitePlace E => tsupport (fun t : G a => ka w t.val)) ×ˢ
        ((Set.univ.pi fun w : {w : InfinitePlace E // w ≠ v} => tsupport (fun t : G b => kb w t.val)) ×ˢ
          tsupport (ψ i.2 j.2))) :=
      (isCompact_univ_pi fun w => (hka w).2).prod
        ((isCompact_univ_pi fun w : {w : InfinitePlace E // w ≠ v} => (hkb w.1).2).prod (hψ i.2 j.2).2)
    refine HasCompactSupport.intro hK fun r hr => ?_
    by_contra hne
    apply hr
    have h1 := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
    have h2 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
    have h3 := right_ne_zero_of_mul hne
    refine ⟨fun w _ => ?_, fun w _ => ?_, subset_tsupport _ h3⟩
    · have h := Finset.prod_ne_zero_iff.1 h1 w (Finset.mem_univ _)
      refine subset_tsupport _ (show ka w (r.1 w).val ≠ 0 from fun h0 => h ?_)
      rw [h0, ent_zero]
    · have h := Finset.prod_ne_zero_iff.1 h2 w (Finset.mem_univ _)
      refine subset_tsupport _ (show kb w (r.2.1 w).val ≠ 0 from fun h0 => h ?_)
      rw [h0, ent_zero]

theorem continuous_RvB_comp (v : InfinitePlace E) {ka : Kers Ma} {kb : Kers Mb} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    {f : Io Ma Mb κ → H E a b → ℂ} (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i : Io Ma Mb κ) {X : Type} [TopologicalSpace X] [FirstCountableTopology X]
    [LocallyCompactSpace X] {φ : X → H E a b} (hφ : Continuous φ) :
    Continuous fun z : X => RvB v μa μb ν ka kb ψ f i (φ z) := by
  haveI : SigmaFinite μa := inferInstance
  haveI : SigmaFinite μb := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : IsLocallyFiniteMeasure (restB μa μb ν v) := by unfold restB; infer_instance
  have hcont : ∀ j, Continuous (fun z : X =>
      ∫ r, cB v ka kb ψ i j r * f j (φ z * σB v r) ∂restB μa μb ν v) := by
    intro j
    obtain ⟨hc, hcs⟩ := cB_props v hka hkb hψ i j
    have e : (fun z : X => ∫ r, cB v ka kb ψ i j r * f j (φ z * σB v r) ∂restB μa μb ν v) =
        fun z => ∫ r in tsupport (cB v ka kb ψ i j), cB v ka kb ψ i j r * f j (φ z * σB v r) ∂restB μa μb ν v :=
      funext fun z => (setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => by
        rw [image_eq_zero_of_notMem_tsupport hr, zero_mul]).symm
    rw [e]
    refine continuous_parametric_integral_of_continuous (f := fun z r => cB v ka kb ψ i j r * f j (φ z * σB v r))
      ?_ hcs
    exact (hc.comp continuous_snd).mul ((hf j).comp ((hφ.comp continuous_fst).mul
      ((continuous_σB v).comp continuous_snd)))
  simp only [RvB]
  exact continuous_finset_sum _ fun q _ => (continuous_finset_sum _ fun j _ => hcont j).smul continuous_const

theorem continuous_RvB (v : InfinitePlace E) {ka : Kers Ma} {kb : Kers Mb} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    {f : Io Ma Mb κ → H E a b → ℂ} (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i : Io Ma Mb κ) (p : H E a b) :
    Continuous fun z : G b => RvB v μa μb ν ka kb ψ f i (p * ιB v z) :=
  continuous_RvB_comp (μa := μa) (μb := μb) (ν := ν) v hf hka hkb hψ i
    (continuous_const.mul (continuous_ιB v))

theorem along_convB (hF : CompatFub) (D : Dom E a b) (hC : Compat D μa μb ν) (v : InfinitePlace E) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (hT : IsTestM (tens ka kb ψ))
    (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i : Io Ma Mb κ) (m₁ : GA E a) (y : GA E b) {x : Mat b} (hx : x ∈ GLs b) :
    along v y (fun z => conv D.μ (tens ka kb ψ) f i (m₁, z)) x =
      ⟪ebB Mb v (i.1.2 v), act μb (Mb v) (kb v) (FB v μa μb ν ka kb ψ f i m₁ y) x⟫_ℂ := by
  rw [along_eqB v m₁ y (fun p => conv D.μ (tens ka kb ψ) f i p) hx, conv_sliceB hF D hC v ka kb ψ f hT hf i]
  set p0 := (m₁, y) * ιB (a := a) v (GeneralLinearGroup.mkOfDetNeZero x hx) with hp0
  have hFB : ∀ t : G b, FB v μa μb ν ka kb ψ f i m₁ y (x * t.val) = RvB v μa μb ν ka kb ψ f i (p0 * ιB v t) := by
    intro t
    have hxt : x * t.val ∈ GLs b := GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs hx (val_mem_GLs t)
    have hm : GeneralLinearGroup.mkOfDetNeZero (x * t.val) hxt = GeneralLinearGroup.mkOfDetNeZero x hx * t :=
      Units.ext rfl
    simp only [FB, dif_pos hxt, hm, ιB_mul, hp0, mul_assoc]
  have hc : Continuous fun t : G b => kb v t.val (FB v μa μb ν ka kb ψ f i m₁ y (x * t.val)) := by
    simp only [hFB]
    exact (hkb v).1.clm_apply (continuous_RvB v hf hka hkb hψ i p0)
  have hcs : HasCompactSupport fun t : G b => kb v t.val (FB v μa μb ν ka kb ψ f i m₁ y (x * t.val)) :=
    HasCompactSupport.intro (hkb v).2 fun t ht => by
      rw [image_eq_zero_of_notMem_tsupport ht, ContinuousLinearMap.zero_apply]
  show _ = ⟪ebB Mb v (i.1.2 v), ∫ t : G b, kb v t.val (FB v μa μb ν ka kb ψ f i m₁ y (x * t.val)) ∂μb⟫_ℂ
  rw [← integral_inner (hc.integrable_of_hasCompactSupport hcs)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [hFB]

theorem RvB_update (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (q : Ix (Mb v)) (p : H E a b) :
    RvB v μa μb ν ka kb ψ f ((i.1.1, Function.update i.1.2 v q), i.2) p = RvB v μa μb ν ka kb ψ f i p := by
  have e : ∀ j r, cB v ka kb ψ ((i.1.1, Function.update i.1.2 v q), i.2) j r = cB v ka kb ψ i j r := by
    intro j r
    simp only [cB]
    congr 2
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Function.update_of_ne w.2]
  simp only [RvB, e]

theorem RvB_congr (v : InfinitePlace E) (ka : Kers Ma) {kb kb' : Kers Mb} (h : ∀ w, w ≠ v → kb' w = kb w)
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (p : H E a b) :
    RvB v μa μb ν ka kb' ψ f i p = RvB v μa μb ν ka kb ψ f i p := by
  have e : ∀ j r, cB v ka kb' ψ i j r = cB v ka kb ψ i j r := by
    intro j r
    simp only [cB]
    congr 2
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [h w w.2]
  simp only [RvB, e]

theorem continuousOn_FB (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (f : Io Ma Mb κ → H E a b → ℂ) (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i : Io Ma Mb κ) (m₁ : GA E a) (y : GA E b) :
    ContinuousOn (FB v μa μb ν ka kb ψ f i m₁ y) (GLs b) := by
  rw [continuousOn_iff_continuous_restrict]
  have hinv : ContinuousOn (fun x : Mat b => x⁻¹) (GLs b) := by
    have e : (fun x : Mat b => x⁻¹) = fun x => (x.det)⁻¹ • x.adjugate := by
      funext x; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [e]
    exact ((continuous_id.matrix_det).continuousOn.inv₀ fun x hx => hx).smul (continuous_id.matrix_adjugate).continuousOn
  have hm : Continuous fun x : GLs b => GeneralLinearGroup.mkOfDetNeZero x.1 x.2 := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have e : (fun x : GLs b => ((GeneralLinearGroup.mkOfDetNeZero x.1 x.2)⁻¹ : G b).val) = fun x => x.1⁻¹ :=
      funext fun x => Matrix.coe_units_inv _
    rw [e]
    exact hinv.comp_continuous continuous_subtype_val fun x => x.2
  show Continuous (fun x : GLs b => FB v μa μb ν ka kb ψ f i m₁ y x.1)
  have e : (fun x : GLs b => FB v μa μb ν ka kb ψ f i m₁ y x.1) =
      fun x : GLs b => RvB v μa μb ν ka kb ψ f i ((m₁, y) * ιB v (GeneralLinearGroup.mkOfDetNeZero x.1 x.2)) := by
    funext x
    simp only [FB, dif_pos x.2]
  rw [e]
  exact (continuous_RvB v hf hka hkb hψ i (m₁, y)).comp hm

end Main

end Slice

end PositivityTheory.Rg.BcB.CG

end
