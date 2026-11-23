import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.MultHasCompactSupport
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableG

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

abbrev RA (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : InfinitePlace E) : Type :=
  ({w : InfinitePlace E // w ≠ v} → G a) × ((InfinitePlace E → G b) × Hf E a b)

def restA [MeasurableSpace (G a)] [MeasurableSpace (G b)] [MeasurableSpace (Hf E a b)] (μa : Measure (G a))
    (μb : Measure (G b)) (ν : Measure (Hf E a b)) (v : InfinitePlace E) : Measure (RA E a b v) :=
  (Measure.pi fun _ : {w : InfinitePlace E // w ≠ v} => μa).prod ((Measure.pi fun _ : InfinitePlace E => μb).prod ν)

def ιA (v : InfinitePlace E) (t : G a) : H E a b := splitH a b (Pi.mulSingle v t, (1, 1))

def σA (v : InfinitePlace E) (r : RA E a b v) : H E a b :=
  splitH a b (fun w => if h : w = v then 1 else r.1 ⟨w, h⟩, r.2)

variable {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [Fintype κ]

abbrev eb (M : Mods E a) (v : InfinitePlace E) (q : Ix (M v)) : (M v).V := stdOrthonormalBasis ℂ (M v).V q

def cA (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (i j : Io Ma Mb κ)
    (r : RA E a b v) : ℂ :=
  (∏ w : {w : InfinitePlace E // w ≠ v}, ent (Ma w) (ka w (r.1 w).val) (i.1.1 w) (j.1.1 w)) *
    (∏ w, ent (Mb w) (kb w (r.2.1 w).val) (i.1.2 w) (j.1.2 w)) * ψ i.2 j.2 r.2.2

section Meas

variable [MeasurableSpace (G a)] [MeasurableSpace (G b)] [MeasurableSpace (Hf E a b)]

def Rv (v : InfinitePlace E) (μa : Measure (G a)) (μb : Measure (G b)) (ν : Measure (Hf E a b)) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (p : H E a b) :
    (Ma v).V :=
  ∑ q : Ix (Ma v), (∑ j ∈ Finset.univ.filter (fun j : Io Ma Mb κ => j.1.1 v = q),
    ∫ r, cA v ka kb ψ i j r * f j (p * σA v r) ∂restA μa μb ν v) • eb Ma v q

def FA (v : InfinitePlace E) (μa : Measure (G a)) (μb : Measure (G b)) (ν : Measure (Hf E a b)) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (y : GA E a)
    (m₂ : GA E b) : Mat a → (Ma v).V := fun x =>
  if hx : x ∈ GLs a then Rv v μa μb ν ka kb ψ f i ((y, m₂) * ιA v (GeneralLinearGroup.mkOfDetNeZero x hx)) else 0

end Meas

section Main

variable [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] {μa : Measure (G a)} [μa.IsHaarMeasure]
  {μb : Measure (G b)} [μb.IsHaarMeasure] {ν : Measure (Hf E a b)} [ν.IsHaarMeasure]

instance uniqueEqV (v : InfinitePlace E) : Unique {w : InfinitePlace E // w = v} :=
  ⟨⟨⟨v, rfl⟩⟩, fun w => Subtype.ext w.2⟩

def eqA (v : InfinitePlace E) :
    ((InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) ≃ᵐ G a × RA E a b v :=
  ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : InfinitePlace E => G a) (fun w => w = v)).prodCongr
    (MeasurableEquiv.refl _)).trans
    (MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.funUnique {w : InfinitePlace E // w = v} (G a)).prodCongr
      (MeasurableEquiv.refl _)))

theorem eqA_symm_apply (v : InfinitePlace E) (q : G a × RA E a b v) :
    (eqA (b := b) v).symm q = (fun w => if h : w = v then q.1 else q.2.1 ⟨w, h⟩, q.2.2) := by
  rfl

theorem splitH_eqA_symm (v : InfinitePlace E) (q : G a × RA E a b v) :
    splitH a b ((eqA v).symm q) = ιA v q.1 * σA v q.2 := by
  rw [eqA_symm_apply, ιA, σA, ← map_mul]
  congr 1
  refine Prod.ext (funext fun w => ?_) (by simp)
  by_cases h : w = v
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

theorem measurePreserving_eqA (μa : Measure (G a)) [SigmaFinite μa] (μb : Measure (G b)) [SigmaFinite μb]
    (ν : Measure (Hf E a b)) [SigmaFinite ν] (v : InfinitePlace E) :
    MeasurePreserving (eqA (b := b) v) ((Measure.pi fun _ => μa).prod ((Measure.pi fun _ => μb).prod ν))
      (μa.prod (restA μa μb ν v)) := by
  have h1 := (measurePreserving_piEquivPiSubtypeProd (fun _ : InfinitePlace E => μa) (fun w => w = v)).prod
    (MeasurePreserving.id ((Measure.pi fun _ : InfinitePlace E => μb).prod ν))
  have h2 := measurePreserving_prodAssoc (Measure.pi fun _ : {w : InfinitePlace E // w = v} => μa)
    (Measure.pi fun _ : {w : InfinitePlace E // ¬ w = v} => μa) ((Measure.pi fun _ : InfinitePlace E => μb).prod ν)
  have h3 := (measurePreserving_funUnique μa {w : InfinitePlace E // w = v}).prod
    (MeasurePreserving.id ((Measure.pi fun _ : {w : InfinitePlace E // ¬ w = v} => μa).prod
      ((Measure.pi fun _ : InfinitePlace E => μb).prod ν)))
  exact h3.comp (h2.comp (by convert h1; rfl))

theorem integral_split (hF : CompatFub) (D : Dom E a b) (hC : Compat D μa μb ν) (v : InfinitePlace E)
    (Q : H E a b → ℂ) (hQ : Continuous Q) (hQs : HasCompactSupport Q) :
    Integrable (fun q : G a × RA E a b v => Q (ιA v q.1 * σA v q.2)) (μa.prod (restA μa μb ν v)) ∧
      ∫ g, Q g ∂D.μ = ∫ t, ∫ r, Q (ιA v t * σA v r) ∂restA μa μb ν v ∂μa := by
  haveI : SigmaFinite μa := inferInstance
  haveI : SigmaFinite μb := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite (Measure.pi fun _ : InfinitePlace E => μa) := inferInstance
  haveI : SigmaFinite (Measure.pi fun _ : InfinitePlace E => μb) := inferInstance
  haveI : SigmaFinite (Measure.pi fun _ : {w : InfinitePlace E // w ≠ v} => μa) := inferInstance
  haveI : SigmaFinite ((Measure.pi fun _ : InfinitePlace E => μb).prod ν) := inferInstance
  haveI : SigmaFinite (restA μa μb ν v) := by unfold restA; infer_instance
  haveI : IsFiniteMeasureOnCompacts (Measure.pi fun _ : InfinitePlace E => μa) := inferInstance
  haveI : IsFiniteMeasureOnCompacts (Measure.pi fun _ : InfinitePlace E => μb) := inferInstance
  haveI : IsFiniteMeasureOnCompacts ((Measure.pi fun _ : InfinitePlace E => μb).prod ν) := inferInstance
  set M := (Measure.pi fun _ : InfinitePlace E => μa).prod ((Measure.pi fun _ : InfinitePlace E => μb).prod ν) with hM
  haveI : IsFiniteMeasureOnCompacts M := by rw [hM]; infer_instance
  have hmp := measurePreserving_eqA (b := b) μa μb ν v
  have hQ' : Continuous (fun z => Q (splitH a b z)) := hQ.comp (splitH a b).continuous
  have hQs' : HasCompactSupport (fun z => Q (splitH a b z)) := hQs.comp_homeomorph (splitH a b).toHomeomorph
  have hI : Integrable (fun z => Q (splitH a b z)) M := hQ'.integrable_of_hasCompactSupport hQs'
  have hcomp : (fun z => Q (splitH a b z)) ∘ (eqA (b := b) v).symm = fun q => Q (ιA v q.1 * σA v q.2) := by
    funext q
    simp only [Function.comp_apply, splitH_eqA_symm]
  have hI2 : Integrable (fun q : G a × RA E a b v => Q (ιA v q.1 * σA v q.2)) (μa.prod (restA μa μb ν v)) := by
    rw [← hcomp]
    exact ((hmp.symm _).integrable_comp_emb (eqA v).symm.measurableEmbedding).2 hI
  refine ⟨hI2, ?_⟩
  have e1 : ∫ z, Q (splitH a b z) ∂M =
      ∫ ya, ∫ yb, ∫ h, Q (splitH a b (ya, (yb, h))) ∂ν ∂(Measure.pi fun _ => μb) ∂(Measure.pi fun _ => μa) := by
    rw [integral_prod _ hI]
    refine integral_congr_ae ?_
    filter_upwards [hI.prod_right_ae] with ya hya
    exact integral_prod _ hya
  have e2 : ∫ z, Q (splitH a b z) ∂M = ∫ q, Q (ιA v q.1 * σA v q.2) ∂(μa.prod (restA μa μb ν v)) := by
    rw [← (hmp.symm _).integral_comp' (g := fun z => Q (splitH a b z))]
    simp only [splitH_eqA_symm]
  rw [← integral_prod _ hI2, ← e2, e1]
  exact hF E a b D μa μb ν hC Q hQ hQs

theorem tens_ισ (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (i j : Io Ma Mb κ)
    (t : G a) (r : RA E a b v) :
    tens ka kb ψ i j (ιA v t * σA v r) = ent (Ma v) (ka v t.val) (i.1.1 v) (j.1.1 v) * cA v ka kb ψ i j r := by
  rw [← splitH_eqA_symm v (t, r), eqA_symm_apply]
  simp only [tens, entA, gInf_splitH₁, gInf_splitH₂, hFin_splitH, cA]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ v]
  have e : ∀ w : {w : InfinitePlace E // w ≠ v},
      (if h : (w : InfinitePlace E) = v then t else r.1 ⟨w, h⟩) = r.1 w := fun w => by rw [dif_neg w.2]
  simp only [dif_pos, e]
  ring

theorem conv_slice (hF : CompatFub) (D : Dom E a b) (hC : Compat D μa μb ν) (v : InfinitePlace E) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (hT : IsTestM (tens ka kb ψ))
    (hf : ∀ i, Continuous (f i)) (i : Io Ma Mb κ) (p : H E a b) :
    conv D.μ (tens ka kb ψ) f i p =
      ∫ t, ⟪eb Ma v (i.1.1 v), ka v t.val (Rv v μa μb ν ka kb ψ f i (p * ιA v t))⟫_ℂ ∂μa := by
  haveI : SigmaFinite μa := inferInstance
  haveI : SigmaFinite μb := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite (restA μa μb ν v) := by unfold restA; infer_instance
  have hQ : ∀ j, Continuous (fun g => tens ka kb ψ i j g * f j (p * g)) ∧
      HasCompactSupport (fun g => tens ka kb ψ i j g * f j (p * g)) := fun j =>
    ⟨(hT i j).1.mul ((hf j).comp (continuous_const.mul continuous_id)), (hT i j).2.mul_right⟩
  have hs := fun j => integral_split hF D hC v _ (hQ j).1 (hQ j).2
  have hpt : ∀ j t, ∫ r, tens ka kb ψ i j (ιA v t * σA v r) * f j (p * (ιA v t * σA v r)) ∂restA μa μb ν v =
      ent (Ma v) (ka v t.val) (i.1.1 v) (j.1.1 v) *
        ∫ r, cA v ka kb ψ i j r * f j (p * ιA v t * σA v r) ∂restA μa μb ν v := by
    intro j t
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [tens_ισ, mul_assoc]
  have hsplit : ∀ j, ∫ g, tens ka kb ψ i j g * f j (p * g) ∂D.μ = ∫ t, ent (Ma v) (ka v t.val) (i.1.1 v) (j.1.1 v) *
      ∫ r, cA v ka kb ψ i j r * f j (p * ιA v t * σA v r) ∂restA μa μb ν v ∂μa := fun j =>
    (hs j).2.trans (integral_congr_ae (ae_of_all _ fun t => hpt j t))
  have hint : ∀ j, Integrable (fun t => ent (Ma v) (ka v t.val) (i.1.1 v) (j.1.1 v) *
      ∫ r, cA v ka kb ψ i j r * f j (p * ιA v t * σA v r) ∂restA μa μb ν v) μa := fun j =>
    ((hs j).1.integral_prod_left).congr (ae_of_all _ fun t => hpt j t)
  show ∑ j, ∫ g, tens ka kb ψ i j g * f j (p * g) ∂D.μ = _
  rw [Finset.sum_congr rfl fun j _ => hsplit j, ← integral_finset_sum _ fun j _ => hint j]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [Rv, map_sum, map_smul, inner_sum, inner_smul_right]
  rw [← Finset.sum_fiberwise Finset.univ (fun j : Io Ma Mb κ => j.1.1 v)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.1 hj).2]
  simp only [ent, eb]
  ring

theorem along_eq (v : InfinitePlace E) (y : GA E a) (m₂ : GA E b) (φ : H E a b → ℂ) {x : Mat a} (hx : x ∈ GLs a) :
    along v y (fun z => φ (z, m₂)) x = φ ((y, m₂) * ιA v (GeneralLinearGroup.mkOfDetNeZero x hx)) := by
  set U : GL (Fin a) (Cinf E) := Units.map (Matrix.piRingEquiv (n := Fin a) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
    (MulEquiv.piUnits.symm (Pi.mulSingle v (GeneralLinearGroup.mkOfDetNeZero x hx))) with hU
  have e : atW v x = toL U.val := by
    funext i j w
    by_cases h : w = v
    · subst h; (simp [atW, hU, toL]) <;> rfl
    · simp [atW, hU, toL, h, Pi.mulSingle_eq_of_ne h]
  have e2 : (y, m₂) * ιA (b := b) v (GeneralLinearGroup.mkOfDetNeZero x hx) = (y * infGL E a U, m₂) := by
    simp [ιA, splitH_apply, infP, hU]
  rw [along, e, chart_val, e2]

omit [BorelSpace (G a)] [BorelSpace (G b)] [BorelSpace (Hf E a b)] in
theorem continuous_ιA (v : InfinitePlace E) : Continuous (ιA (a := a) (b := b) v) := by
  have h1 : Continuous fun t : G a => (Pi.mulSingle v t : InfinitePlace E → G a) := by
    refine continuous_pi fun w => ?_
    by_cases h : w = v
    · subst h; simp only [Pi.mulSingle_eq_same]; exact continuous_id
    · simpa [Pi.mulSingle_eq_of_ne h] using continuous_const
  exact (splitH a b).continuous.comp (h1.prodMk continuous_const)

omit [BorelSpace (G a)] [BorelSpace (G b)] [BorelSpace (Hf E a b)] in
theorem continuous_σA (v : InfinitePlace E) : Continuous (σA (a := a) (b := b) v) := by
  refine (splitH a b).continuous.comp (Continuous.prodMk (continuous_pi fun w => ?_) continuous_snd)
  by_cases h : w = v
  · simp only [h, dif_pos]; exact continuous_const
  · simp only [h, dif_neg, not_false_eq_true]; exact (continuous_apply _).comp continuous_fst

theorem ιA_mul (v : InfinitePlace E) (s t : G a) : ιA (b := b) v (s * t) = ιA v s * ιA v t := by
  rw [ιA, ιA, ιA, ← map_mul, Pi.mulSingle_mul]
  simp

omit [BorelSpace (G a)] [BorelSpace (G b)] [BorelSpace (Hf E a b)] in
theorem cA_props (v : InfinitePlace E) {ka : Kers Ma} {kb : Kers Mb} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i j : Io Ma Mb κ) :
    Continuous (cA v ka kb ψ i j) ∧ HasCompactSupport (cA v ka kb ψ i j) := by
  refine ⟨?_, ?_⟩
  · refine ((continuous_finset_prod _ fun w _ => ?_).mul (continuous_finset_prod _ fun w _ => ?_)).mul
      ((hψ i.2 j.2).1.comp (continuous_snd.comp continuous_snd))
    · exact continuous_ent ((hka w).1.comp ((continuous_apply w).comp continuous_fst)) _ _
    · exact continuous_ent ((hkb w).1.comp ((continuous_apply w).comp (continuous_fst.comp continuous_snd))) _ _
  · have hK : IsCompact ((Set.univ.pi fun w : {w : InfinitePlace E // w ≠ v} => tsupport (fun t : G a => ka w t.val)) ×ˢ
        ((Set.univ.pi fun w : InfinitePlace E => tsupport (fun t : G b => kb w t.val)) ×ˢ tsupport (ψ i.2 j.2))) :=
      (isCompact_univ_pi fun w : {w : InfinitePlace E // w ≠ v} => (hka w.1).2).prod
        ((isCompact_univ_pi fun w => (hkb w).2).prod (hψ i.2 j.2).2)
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

theorem continuous_Rv_comp (v : InfinitePlace E) {ka : Kers Ma} {kb : Kers Mb} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    {f : Io Ma Mb κ → H E a b → ℂ} (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i : Io Ma Mb κ) {X : Type} [TopologicalSpace X] [FirstCountableTopology X]
    [LocallyCompactSpace X] {φ : X → H E a b} (hφ : Continuous φ) :
    Continuous fun z : X => Rv v μa μb ν ka kb ψ f i (φ z) := by
  haveI : SigmaFinite μa := inferInstance
  haveI : SigmaFinite μb := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : IsLocallyFiniteMeasure (restA μa μb ν v) := by unfold restA; infer_instance
  have hcont : ∀ j, Continuous (fun z : X =>
      ∫ r, cA v ka kb ψ i j r * f j (φ z * σA v r) ∂restA μa μb ν v) := by
    intro j
    obtain ⟨hc, hcs⟩ := cA_props v hka hkb hψ i j
    have e : (fun z : X => ∫ r, cA v ka kb ψ i j r * f j (φ z * σA v r) ∂restA μa μb ν v) =
        fun z => ∫ r in tsupport (cA v ka kb ψ i j), cA v ka kb ψ i j r * f j (φ z * σA v r) ∂restA μa μb ν v :=
      funext fun z => (setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => by
        rw [image_eq_zero_of_notMem_tsupport hr, zero_mul]).symm
    rw [e]
    refine continuous_parametric_integral_of_continuous (f := fun z r => cA v ka kb ψ i j r * f j (φ z * σA v r))
      ?_ hcs
    exact (hc.comp continuous_snd).mul ((hf j).comp ((hφ.comp continuous_fst).mul
      ((continuous_σA v).comp continuous_snd)))
  simp only [Rv]
  exact continuous_finset_sum _ fun q _ => (continuous_finset_sum _ fun j _ => hcont j).smul continuous_const

theorem continuous_Rv (v : InfinitePlace E) {ka : Kers Ma} {kb : Kers Mb} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    {f : Io Ma Mb κ → H E a b → ℂ} (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i : Io Ma Mb κ) (p : H E a b) :
    Continuous fun z : G a => Rv v μa μb ν ka kb ψ f i (p * ιA v z) :=
  continuous_Rv_comp (μa := μa) (μb := μb) (ν := ν) v hf hka hkb hψ i
    (continuous_const.mul (continuous_ιA v))

theorem along_conv (hF : CompatFub) (D : Dom E a b) (hC : Compat D μa μb ν) (v : InfinitePlace E) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (hT : IsTestM (tens ka kb ψ))
    (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i : Io Ma Mb κ) (y : GA E a) (m₂ : GA E b) {x : Mat a} (hx : x ∈ GLs a) :
    along v y (fun z => conv D.μ (tens ka kb ψ) f i (z, m₂)) x =
      ⟪eb Ma v (i.1.1 v), act μa (Ma v) (ka v) (FA v μa μb ν ka kb ψ f i y m₂) x⟫_ℂ := by
  rw [along_eq v y m₂ (fun p => conv D.μ (tens ka kb ψ) f i p) hx, conv_slice hF D hC v ka kb ψ f hT hf i]
  set p0 := (y, m₂) * ιA (b := b) v (GeneralLinearGroup.mkOfDetNeZero x hx) with hp0
  have hFA : ∀ t : G a, FA v μa μb ν ka kb ψ f i y m₂ (x * t.val) = Rv v μa μb ν ka kb ψ f i (p0 * ιA v t) := by
    intro t
    have hxt : x * t.val ∈ GLs a := GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs hx (val_mem_GLs t)
    have hm : GeneralLinearGroup.mkOfDetNeZero (x * t.val) hxt = GeneralLinearGroup.mkOfDetNeZero x hx * t :=
      Units.ext rfl
    simp only [FA, dif_pos hxt, hm, ιA_mul, hp0, mul_assoc]
  have hc : Continuous fun t : G a => ka v t.val (FA v μa μb ν ka kb ψ f i y m₂ (x * t.val)) := by
    simp only [hFA]
    exact (hka v).1.clm_apply (continuous_Rv v hf hka hkb hψ i p0)
  have hcs : HasCompactSupport fun t : G a => ka v t.val (FA v μa μb ν ka kb ψ f i y m₂ (x * t.val)) :=
    HasCompactSupport.intro (hka v).2 fun t ht => by
      rw [image_eq_zero_of_notMem_tsupport ht, ContinuousLinearMap.zero_apply]
  show _ = ⟪eb Ma v (i.1.1 v), ∫ t : G a, ka v t.val (FA v μa μb ν ka kb ψ f i y m₂ (x * t.val)) ∂μa⟫_ℂ
  rw [← integral_inner (hc.integrable_of_hasCompactSupport hcs)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [hFA]

theorem Rv_update (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (q : Ix (Ma v)) (p : H E a b) :
    Rv v μa μb ν ka kb ψ f ((Function.update i.1.1 v q, i.1.2), i.2) p = Rv v μa μb ν ka kb ψ f i p := by
  have e : ∀ j r, cA v ka kb ψ ((Function.update i.1.1 v q, i.1.2), i.2) j r = cA v ka kb ψ i j r := by
    intro j r
    simp only [cA]
    congr 2
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Function.update_of_ne w.2]
  simp only [Rv, e]

theorem Rv_congr (v : InfinitePlace E) {ka ka' : Kers Ma} (h : ∀ w, w ≠ v → ka' w = ka w) (kb : Kers Mb)
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (p : H E a b) :
    Rv v μa μb ν ka' kb ψ f i p = Rv v μa μb ν ka kb ψ f i p := by
  have e : ∀ j r, cA v ka' kb ψ i j r = cA v ka kb ψ i j r := by
    intro j r
    simp only [cA]
    congr 2
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [h w w.2]
  simp only [Rv, e]

theorem continuousOn_FA (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (f : Io Ma Mb κ → H E a b → ℂ) (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i : Io Ma Mb κ) (y : GA E a) (m₂ : GA E b) :
    ContinuousOn (FA v μa μb ν ka kb ψ f i y m₂) (GLs a) := by
  rw [continuousOn_iff_continuous_restrict]
  have hinv : ContinuousOn (fun x : Mat a => x⁻¹) (GLs a) := by
    have e : (fun x : Mat a => x⁻¹) = fun x => (x.det)⁻¹ • x.adjugate := by
      funext x; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [e]
    exact ((continuous_id.matrix_det).continuousOn.inv₀ fun x hx => hx).smul (continuous_id.matrix_adjugate).continuousOn
  have hm : Continuous fun x : GLs a => GeneralLinearGroup.mkOfDetNeZero x.1 x.2 := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have e : (fun x : GLs a => ((GeneralLinearGroup.mkOfDetNeZero x.1 x.2)⁻¹ : G a).val) = fun x => x.1⁻¹ :=
      funext fun x => Matrix.coe_units_inv _
    rw [e]
    exact hinv.comp_continuous continuous_subtype_val fun x => x.2
  show Continuous (fun x : GLs a => FA v μa μb ν ka kb ψ f i y m₂ x.1)
  have e : (fun x : GLs a => FA v μa μb ν ka kb ψ f i y m₂ x.1) =
      fun x : GLs a => Rv v μa μb ν ka kb ψ f i ((y, m₂) * ιA v (GeneralLinearGroup.mkOfDetNeZero x.1 x.2)) := by
    funext x
    simp only [FA, dif_pos x.2]
  rw [e]
  exact (continuous_Rv v hf hka hkb hψ i (y, m₂)).comp hm

end Main

end Slice

end PositivityTheory.Rg.BcB.CG

end
