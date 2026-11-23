import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSliceB
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.KernelDerivativeFarZero

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical InnerProductSpace

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PositivityTheory.Rg.BcB.CG

namespace Slice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
variable {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [Fintype κ]
variable [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] {μa : Measure (G a)} [μa.IsHaarMeasure]
  {μb : Measure (G b)} [μb.IsHaarMeasure] {ν : Measure (Hf E a b)} [ν.IsHaarMeasure]

def StB (v : InfinitePlace E) (μa : Measure (G a)) (μb : Measure (G b)) (ν : Measure (Hf E a b)) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (q : Ix (Mb v))
    (p : H E a b) : (Mb v).V :=
  ∑ j ∈ Finset.univ.filter (fun j : Io Ma Mb κ => j.1.2 v = q),
    ∫ r, cB v ka kb ψ i j r • RvB v μa μb ν ka kb ψ f j (p * σB v r) ∂restB μa μb ν v

def FtB (v : InfinitePlace E) (μa : Measure (G a)) (μb : Measure (G b)) (ν : Measure (Hf E a b)) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (q : Ix (Mb v))
    (m₁ : GA E a) (y : GA E b) : Mat b → (Mb v).V := fun x =>
  if hx : x ∈ GLs b then StB v μa μb ν ka kb ψ f i q ((m₁, y) * ιB v (GeneralLinearGroup.mkOfDetNeZero x hx)) else 0

theorem σB_ιB (v : InfinitePlace E) (t : G b) (r : RB E a b v) : σB v r * ιB v t = ιB v t * σB v r := by
  rw [σB, ιB, ← map_mul, ← map_mul]
  congr 1
  refine Prod.ext (by simp) (Prod.ext (funext fun w => ?_) (by simp))
  by_cases h : w = v
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

theorem cB_update_right (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (i j : Io Ma Mb κ) (q : Ix (Mb v)) (r : RB E a b v) :
    cB v ka kb ψ i ((j.1.1, Function.update j.1.2 v q), j.2) r = cB v ka kb ψ i j r := by
  simp only [cB]
  congr 2
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Function.update_of_ne w.2]

theorem StB_indep (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (q q' : Ix (Mb v)) (p : H E a b) :
    StB v μa μb ν ka kb ψ f i q p = StB v μa μb ν ka kb ψ f i q' p := by
  unfold StB
  refine Finset.sum_nbij' (fun j => ((j.1.1, Function.update j.1.2 v q'), j.2))
    (fun j => ((j.1.1, Function.update j.1.2 v q), j.2)) ?_ ?_ ?_ ?_ ?_
  · intro j _; simp
  · intro j _; simp
  · intro j hj
    have h := (Finset.mem_filter.1 hj).2
    simp only [Function.update_idem]
    rw [← h, Function.update_eq_self]
  · intro j hj
    have h := (Finset.mem_filter.1 hj).2
    simp only [Function.update_idem]
    rw [← h, Function.update_eq_self]
  · intro j _
    simp only [cB_update_right, RvB_update]

set_option synthInstance.maxHeartbeats 200000 in
theorem continuous_StB (v : InfinitePlace E) {ka : Kers Ma} {kb : Kers Mb} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    {f : Io Ma Mb κ → H E a b → ℂ} (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i : Io Ma Mb κ) (q : Ix (Mb v)) (p : H E a b) :
    Continuous fun z : G b => StB v μa μb ν ka kb ψ f i q (p * ιB v z) := by
  haveI : SigmaFinite μa := inferInstance
  haveI : SigmaFinite μb := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : IsLocallyFiniteMeasure (restB μa μb ν v) := by unfold restB; infer_instance
  haveI : SecondCountableTopology (RB E a b v) := inferInstance
  haveI : LocallyCompactSpace (RB E a b v) := inferInstance
  haveI : FirstCountableTopology (G b × RB E a b v) := inferInstance
  haveI : LocallyCompactSpace (G b × RB E a b v) := inferInstance
  unfold StB
  refine continuous_finset_sum _ fun j _ => ?_
  obtain ⟨hc, hcs⟩ := cB_props v hka hkb hψ i j
  have e : (fun z : G b => ∫ r, cB v ka kb ψ i j r • RvB v μa μb ν ka kb ψ f j (p * ιB v z * σB v r) ∂restB μa μb ν v) =
      fun z => ∫ r in tsupport (cB v ka kb ψ i j),
        cB v ka kb ψ i j r • RvB v μa μb ν ka kb ψ f j (p * ιB v z * σB v r) ∂restB μa μb ν v :=
    funext fun z => (setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => by
      rw [image_eq_zero_of_notMem_tsupport hr, zero_smul]).symm
  rw [e]
  refine continuous_parametric_integral_of_continuous
    (f := fun z r => cB v ka kb ψ i j r • RvB v μa μb ν ka kb ψ f j (p * ιB v z * σB v r)) ?_ hcs
  exact (hc.comp continuous_snd).smul (continuous_RvB_comp v hf hka hkb hψ j
    (φ := fun q : G b × RB E a b v => p * ιB v q.1 * σB v q.2)
    ((continuous_const.mul ((continuous_ιB v).comp continuous_fst)).mul ((continuous_σB v).comp continuous_snd)))

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem RvB_eq (hF : CompatFub) (D : Dom E a b) (hC : Compat D μa μb ν) (v : InfinitePlace E) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (hT : IsTestM (tens ka kb ψ))
    (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) {c : ℂ} (hc : c ≠ 0) (hrep : conv D.μ (tens ka kb ψ) f = c • f) (i : Io Ma Mb κ)
    (q0 : Ix (Mb v)) (p : H E a b) :
    RvB v μa μb ν ka kb ψ f i p = c⁻¹ • ∫ t, kb v t.val (StB v μa μb ν ka kb ψ f i q0 (p * ιB v t)) ∂μb := by
  haveI : SigmaFinite μa := inferInstance
  haveI : SigmaFinite μb := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite (restB μa μb ν v) := by unfold restB; infer_instance
  haveI : IsFiniteMeasureOnCompacts (restB μa μb ν v) := by unfold restB; infer_instance
  haveI : IsFiniteMeasureOnCompacts ((restB μa μb ν v).prod μb) := inferInstance
  haveI : SecondCountableTopology (RB E a b v) := inferInstance
  haveI : LocallyCompactSpace (RB E a b v) := inferInstance
  haveI : FirstCountableTopology (RB E a b v × G b) := inferInstance
  haveI : LocallyCompactSpace (RB E a b v × G b) := inferInstance
  set K : G b → ((Mb v).V →L[ℂ] (Mb v).V) := fun t => kb v t.val with hK
  have hKc : Continuous K := (hkb v).1
  have hKs : HasCompactSupport K := (hkb v).2
  have hfj : ∀ j P, f j P = c⁻¹ * ∫ t, ⟪ebB Mb v (j.1.2 v), K t (RvB v μa μb ν ka kb ψ f j (P * ιB v t))⟫_ℂ ∂μb := by
    intro j P
    have h := congrFun (congrFun hrep j) P
    rw [conv_sliceB hF D hC v ka kb ψ f hT hf j P] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  obtain ⟨g, hg⟩ : ∃ g : Io Ma Mb κ → RB E a b v × G b → ℂ, g = fun j q =>
      cB v ka kb ψ i j q.1 * ⟪ebB Mb v (j.1.2 v), K q.2 (RvB v μa μb ν ka kb ψ f j (p * ιB v q.2 * σB v q.1))⟫_ℂ :=
    ⟨_, rfl⟩
  have hRc : ∀ j, Continuous fun q : RB E a b v × G b => RvB v μa μb ν ka kb ψ f j (p * ιB v q.2 * σB v q.1) :=
    fun j => continuous_RvB_comp v hf hka hkb hψ j
      ((continuous_const.mul ((continuous_ιB v).comp continuous_snd)).mul ((continuous_σB v).comp continuous_fst))
  have hgi : ∀ j, Integrable (g j) ((restB μa μb ν v).prod μb) := by
    intro j
    obtain ⟨hc1, hcs1⟩ := cB_props v hka hkb hψ i j
    rw [hg]
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hc1.comp continuous_fst).mul (continuous_const.inner ((hKc.comp continuous_snd).clm_apply (hRc j)))
    · refine HasCompactSupport.intro (IsCompact.prod hcs1 hKs) fun q hq => ?_
      simp only [Set.mem_prod, not_and_or] at hq
      rcases hq with hq | hq
      · simp only [image_eq_zero_of_notMem_tsupport hq, zero_mul]
      · simp only [image_eq_zero_of_notMem_tsupport hq, ContinuousLinearMap.zero_apply, inner_zero_right,
          mul_zero]
  have hI : ∀ j, ∫ r, cB v ka kb ψ i j r * f j (p * σB v r) ∂restB μa μb ν v =
      c⁻¹ * ∫ t, ∫ r, g j (r, t) ∂restB μa μb ν v ∂μb := by
    intro j
    have e1 : ∀ r, cB v ka kb ψ i j r * f j (p * σB v r) = c⁻¹ * ∫ t, g j (r, t) ∂μb := by
      intro r
      rw [hfj j, mul_left_comm, ← integral_const_mul]
      refine congrArg (c⁻¹ * ·) (integral_congr_ae (ae_of_all _ fun t => ?_))
      rw [hg]
      beta_reduce
      rw [show p * σB v r * ιB v t = p * ιB v t * σB v r by rw [mul_assoc, σB_ιB, ← mul_assoc]]
    rw [integral_congr_ae (ae_of_all _ e1), integral_const_mul,
      integral_integral_swap (f := fun r t => g j (r, t)) (hgi j)]
  have hWi : Integrable (fun t => K t (StB v μa μb ν ka kb ψ f i q0 (p * ιB v t))) μb := by
    refine Continuous.integrable_of_hasCompactSupport (hKc.clm_apply (continuous_StB v hf hka hkb hψ i q0 p)) ?_
    exact HasCompactSupport.intro hKs fun t ht => by
      rw [image_eq_zero_of_notMem_tsupport ht, ContinuousLinearMap.zero_apply]
  have hsum : ∀ q, ∑ j ∈ Finset.univ.filter (fun j : Io Ma Mb κ => j.1.2 v = q),
      ∫ r, cB v ka kb ψ i j r * f j (p * σB v r) ∂restB μa μb ν v =
      c⁻¹ * ⟪ebB Mb v q, ∫ t, K t (StB v μa μb ν ka kb ψ f i q0 (p * ιB v t)) ∂μb⟫_ℂ := by
    intro q
    simp only [hI]
    rw [← Finset.mul_sum, ← integral_finset_sum _ fun j _ => (hgi j).integral_prod_right]
    congr 1
    rw [← integral_inner hWi]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    beta_reduce
    rw [StB_indep v ka kb ψ f i q0 q]
    simp only [StB, map_sum, inner_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjq : j.1.2 v = q := (Finset.mem_filter.1 hj).2
    obtain ⟨hc1, hcs1⟩ := cB_props v hka hkb hψ i j
    have hR1 : Continuous fun r : RB E a b v => RvB v μa μb ν ka kb ψ f j (p * ιB v t * σB v r) :=
      continuous_RvB_comp v hf hka hkb hψ j (continuous_const.mul (continuous_σB v))
    have hi1 : Integrable (fun r => cB v ka kb ψ i j r • RvB v μa μb ν ka kb ψ f j (p * ιB v t * σB v r))
        (restB μa μb ν v) :=
      (hc1.smul hR1).integrable_of_hasCompactSupport (HasCompactSupport.intro hcs1 fun r hr => by
        show cB v ka kb ψ i j r • RvB v μa μb ν ka kb ψ f j (p * ιB v t * σB v r) = 0
        rw [image_eq_zero_of_notMem_tsupport hr, zero_smul])
    rw [← ContinuousLinearMap.integral_comp_comm (K t) hi1, ← integral_inner ((K t).integrable_comp hi1)]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    rw [hg]
    beta_reduce
    simp only [map_smul, inner_smul_right, hjq]
  conv_lhs => rw [RvB]
  simp only [hsum, mul_smul]
  rw [← Finset.smul_sum, OrthonormalBasis.sum_repr']

theorem FB_eq_act (hF : CompatFub) (D : Dom E a b) (hC : Compat D μa μb ν) (v : InfinitePlace E) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (hT : IsTestM (tens ka kb ψ))
    (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) {c : ℂ} (hc : c ≠ 0) (hrep : conv D.μ (tens ka kb ψ) f = c • f) (i : Io Ma Mb κ)
    (q0 : Ix (Mb v)) (m₁ : GA E a) (y : GA E b) {x : Mat b} (hx : x ∈ GLs b) :
    FB v μa μb ν ka kb ψ f i m₁ y x = c⁻¹ • act μb (Mb v) (kb v) (FtB v μa μb ν ka kb ψ f i q0 m₁ y) x := by
  rw [FB, dif_pos hx, RvB_eq hF D hC v ka kb ψ f hT hf hka hkb hψ hc hrep i q0]
  congr 1
  show _ = ∫ t : G b, kb v t.val (FtB v μa μb ν ka kb ψ f i q0 m₁ y (x * t.val)) ∂μb
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  have hxt : x * t.val ∈ GLs b := GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs hx (val_mem_GLs t)
  have hm : GeneralLinearGroup.mkOfDetNeZero (x * t.val) hxt = GeneralLinearGroup.mkOfDetNeZero x hx * t :=
    Units.ext rfl
  simp only [FtB, dif_pos hxt, hm, ιB_mul, mul_assoc]

theorem continuousOn_FtB (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (f : Io Ma Mb κ → H E a b → ℂ) (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i : Io Ma Mb κ) (q : Ix (Mb v)) (m₁ : GA E a) (y : GA E b) :
    ContinuousOn (FtB v μa μb ν ka kb ψ f i q m₁ y) (GLs b) := by
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
  show Continuous (fun x : GLs b => FtB v μa μb ν ka kb ψ f i q m₁ y x.1)
  have e : (fun x : GLs b => FtB v μa μb ν ka kb ψ f i q m₁ y x.1) =
      fun x : GLs b => StB v μa μb ν ka kb ψ f i q ((m₁, y) * ιB v (GeneralLinearGroup.mkOfDetNeZero x.1 x.2)) := by
    funext x
    simp only [FtB, dif_pos x.2]
  rw [e]
  exact (continuous_StB v hf hka hkb hψ i q (m₁, y)).comp hm

theorem FB_mem_CE (hF : CompatFub) (D : Dom E a b) (hC : Compat D μa μb ν) (v : InfinitePlace E) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (hT : IsTestM (tens ka kb ψ))
    (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) {c : ℂ} (hc : c ≠ 0) (hrep : conv D.μ (tens ka kb ψ) f = c • f) {val : Inf b → ℂ} {T : ℝ}
    (hkv : IsMult μb (Mb v) (kb v) val T) (i : Io Ma Mb κ) (m₁ : GA E a) (y : GA E b) :
    FB v μa μb ν ka kb ψ f i m₁ y ∈ CE (Mb v) := by
  have hA := GelP.act_mem_CE_of_mult μb hkv
    (continuousOn_FtB (μa := μa) (μb := μb) (ν := ν) v ka kb ψ f hf hka hkb hψ i (i.1.2 v) m₁ y)
  letI : NormedAddCommGroup (Mat b) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mat b) := Matrix.normedSpace
  refine ⟨(hA.1.const_smul c⁻¹).congr fun x hx =>
    FB_eq_act hF D hC v ka kb ψ f hT hf hka hkb hψ hc hrep i (i.1.2 v) m₁ y hx, ?_⟩
  intro g hg k
  have hgk : g * k.1 ∈ GLs b := GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs hg (GlobalTheory.CompanionTheory.WaveAll.unitary_mem_GLs k)
  rw [FB_eq_act hF D hC v ka kb ψ f hT hf hka hkb hψ hc hrep i (i.1.2 v) m₁ y hgk,
    FB_eq_act hF D hC v ka kb ψ f hT hf hka hkb hψ hc hrep i (i.1.2 v) m₁ y hg, hA.2 g hg k, map_smul]

theorem gelB (hW : WaveEx) (hF : CompatFub) (hTT : TensTest) (D : Dom E a b) (hC : Compat D μa μb ν)
    (v : InfinitePlace E) {ka : Kers Ma} {kb : Kers Mb} {va : InfinitePlace E → Inf a → ℂ}
    {vb : InfinitePlace E → Inf b → ℂ} {T : ℝ} {ψ : Matrix κ κ (Hf E a b → ℂ)} {f : Io Ma Mb κ → H E a b → ℂ}
    {g : ℝ → ℝ} {s : Bool} {m : ℕ} (hka : IsMults μa ka va T) (hkb : IsMults μb kb vb T) (hψ : IsFinM ψ)
    (hg : IsBump g T) (hf : ∀ i, Continuous (f i)) {c c' : ℂ} (hc : c ≠ 0)
    (hrep : conv D.μ (tens ka kb ψ) f = c • f) (k' : Mat b → ((Mb v).V →L[ℂ] (Mb v).V))
    (hk0 : IsKer μb (Mb v) [] g (kb v)) (hk' : IsKer μb (Mb v) [(s, m)] g k')
    (hrep' : conv D.μ (tens ka (Function.update kb v k') ψ) f = c' • f) (i : Io Ma Mb κ) (m₁ : GA E a) (y : GA E b)
    {x : Mat b} (hx : x ∈ GLs b) :
    gel s m (PositivityTheory.RgBcC.Bridge.along v y fun z => f i (m₁, z)) x =
      (c' / c) • PositivityTheory.RgBcC.Bridge.along v y (fun z => f i (m₁, z)) x := by
  set kb₂ := Function.update kb v k' with hkb₂
  have hkb₂m : IsMults μb kb₂ (Function.update vb v (fun χ => zVal [(s, m)] χ * coshT g (cas χ))) T := by
    intro w
    by_cases h : w = v
    · subst h; simp only [hkb₂, Function.update_self]; exact GelP.isMult_of_isKer μb hg hk'
    · simp only [hkb₂, Function.update_of_ne h]; exact hkb w
  have hkac : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val) :=
    fun w => ⟨mult_continuous (hka w), mult_hasCompactSupport (hka w)⟩
  have hkc : ∀ {k : Kers Mb} {vk : InfinitePlace E → Inf b → ℂ}, IsMults μb k vk T →
      ∀ w, Continuous (fun t : G b => k w t.val) ∧ HasCompactSupport (fun t : G b => k w t.val) :=
    fun h w => ⟨mult_continuous (h w), mult_hasCompactSupport (h w)⟩
  have hT := (hTT E a b μa μb Ma Mb κ ka kb va vb T ψ hka hkb hψ).1
  have hT₂ := (hTT E a b μa μb Ma Mb κ ka kb₂ va _ T ψ hka hkb₂m hψ).1
  have hFB : FB v μa μb ν ka kb₂ ψ f i m₁ y = FB v μa μb ν ka kb ψ f i m₁ y := by
    funext z
    unfold FB
    split_ifs with hz
    · rw [RvB_congr v ka (fun w hw => Function.update_of_ne hw _ _)]
    · rfl
  have hCE := FB_mem_CE hF D hC v ka kb ψ f hT hf hkac (hkc hkb) hψ hc hrep (hkb v) i m₁ y
  have hFc := continuousOn_FB v ka kb ψ f hf hkac (hkc hkb) hψ i m₁ y (μa := μa) (μb := μb) (ν := ν)
  refine GelP.gel_eigen_of_act μb hW hk0 hk' (hkb v) hCE hFc (ebB Mb v (i.1.2 v)) hc ?_ ?_ hx
  · intro x' hx'
    have h := along_convB hF D hC v ka kb ψ f hT hf hkac (hkc hkb) hψ i m₁ y hx'
    rw [hrep, along_eqB v m₁ y _ hx'] at h
    rw [along_eqB v m₁ y (f i) hx', ← h]
    simp [Pi.smul_apply]
  · intro x' hx'
    have h := along_convB hF D hC v ka kb₂ ψ f hT₂ hf hkac (hkc hkb₂m) hψ i m₁ y hx'
    rw [hrep', along_eqB v m₁ y _ hx', hFB] at h
    simp only [hkb₂, Function.update_self] at h
    rw [along_eqB v m₁ y (f i) hx', ← h]
    simp [Pi.smul_apply]

end Slice

end PositivityTheory.Rg.BcB.CG

end
