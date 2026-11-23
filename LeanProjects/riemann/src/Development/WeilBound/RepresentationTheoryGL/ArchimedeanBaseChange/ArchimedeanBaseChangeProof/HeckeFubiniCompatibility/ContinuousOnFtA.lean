import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSlice
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

def St (v : InfinitePlace E) (μa : Measure (G a)) (μb : Measure (G b)) (ν : Measure (Hf E a b)) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (q : Ix (Ma v))
    (p : H E a b) : (Ma v).V :=
  ∑ j ∈ Finset.univ.filter (fun j : Io Ma Mb κ => j.1.1 v = q),
    ∫ r, cA v ka kb ψ i j r • Rv v μa μb ν ka kb ψ f j (p * σA v r) ∂restA μa μb ν v

def FtA (v : InfinitePlace E) (μa : Measure (G a)) (μb : Measure (G b)) (ν : Measure (Hf E a b)) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (q : Ix (Ma v))
    (y : GA E a) (m₂ : GA E b) : Mat a → (Ma v).V := fun x =>
  if hx : x ∈ GLs a then St v μa μb ν ka kb ψ f i q ((y, m₂) * ιA v (GeneralLinearGroup.mkOfDetNeZero x hx)) else 0

theorem σA_ιA (v : InfinitePlace E) (t : G a) (r : RA E a b v) : σA v r * ιA v t = ιA v t * σA v r := by
  rw [σA, ιA, ← map_mul, ← map_mul]
  congr 1
  refine Prod.ext (funext fun w => ?_) (by
    show r.2 * 1 = 1 * r.2
    rw [mul_one, one_mul])
  by_cases h : w = v
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

theorem cA_update_right (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (i j : Io Ma Mb κ) (q : Ix (Ma v)) (r : RA E a b v) :
    cA v ka kb ψ i ((Function.update j.1.1 v q, j.1.2), j.2) r = cA v ka kb ψ i j r := by
  simp only [cA]
  congr 2
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Function.update_of_ne w.2]

theorem St_indep (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (f : Io Ma Mb κ → H E a b → ℂ) (i : Io Ma Mb κ) (q q' : Ix (Ma v)) (p : H E a b) :
    St v μa μb ν ka kb ψ f i q p = St v μa μb ν ka kb ψ f i q' p := by
  unfold St
  refine Finset.sum_nbij' (fun j => ((Function.update j.1.1 v q', j.1.2), j.2))
    (fun j => ((Function.update j.1.1 v q, j.1.2), j.2)) ?_ ?_ ?_ ?_ ?_
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
    simp only [cA_update_right, Rv_update]

set_option synthInstance.maxHeartbeats 200000 in
theorem continuous_St (v : InfinitePlace E) {ka : Kers Ma} {kb : Kers Mb} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    {f : Io Ma Mb κ → H E a b → ℂ} (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i : Io Ma Mb κ) (q : Ix (Ma v)) (p : H E a b) :
    Continuous fun z : G a => St v μa μb ν ka kb ψ f i q (p * ιA v z) := by
  haveI : SigmaFinite μa := inferInstance
  haveI : SigmaFinite μb := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : IsLocallyFiniteMeasure (restA μa μb ν v) := by unfold restA; infer_instance
  haveI : SecondCountableTopology (RA E a b v) := inferInstance
  haveI : LocallyCompactSpace (RA E a b v) := inferInstance
  haveI : FirstCountableTopology (G a × RA E a b v) := inferInstance
  haveI : LocallyCompactSpace (G a × RA E a b v) := inferInstance
  unfold St
  refine continuous_finset_sum _ fun j _ => ?_
  obtain ⟨hc, hcs⟩ := cA_props v hka hkb hψ i j
  have e : (fun z : G a => ∫ r, cA v ka kb ψ i j r • Rv v μa μb ν ka kb ψ f j (p * ιA v z * σA v r) ∂restA μa μb ν v) =
      fun z => ∫ r in tsupport (cA v ka kb ψ i j),
        cA v ka kb ψ i j r • Rv v μa μb ν ka kb ψ f j (p * ιA v z * σA v r) ∂restA μa μb ν v :=
    funext fun z => (setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => by
      rw [image_eq_zero_of_notMem_tsupport hr, zero_smul]).symm
  rw [e]
  refine continuous_parametric_integral_of_continuous
    (f := fun z r => cA v ka kb ψ i j r • Rv v μa μb ν ka kb ψ f j (p * ιA v z * σA v r)) ?_ hcs
  exact (hc.comp continuous_snd).smul (continuous_Rv_comp v hf hka hkb hψ j
    (φ := fun q : G a × RA E a b v => p * ιA v q.1 * σA v q.2)
    ((continuous_const.mul ((continuous_ιA v).comp continuous_fst)).mul ((continuous_σA v).comp continuous_snd)))

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem Rv_eq (hF : CompatFub) (D : Dom E a b) (hC : Compat D μa μb ν) (v : InfinitePlace E) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (hT : IsTestM (tens ka kb ψ))
    (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) {c : ℂ} (hc : c ≠ 0) (hrep : conv D.μ (tens ka kb ψ) f = c • f) (i : Io Ma Mb κ)
    (q0 : Ix (Ma v)) (p : H E a b) :
    Rv v μa μb ν ka kb ψ f i p = c⁻¹ • ∫ t, ka v t.val (St v μa μb ν ka kb ψ f i q0 (p * ιA v t)) ∂μa := by
  haveI : SigmaFinite μa := inferInstance
  haveI : SigmaFinite μb := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite (restA μa μb ν v) := by unfold restA; infer_instance
  haveI : IsFiniteMeasureOnCompacts (restA μa μb ν v) := by unfold restA; infer_instance
  haveI : IsFiniteMeasureOnCompacts ((restA μa μb ν v).prod μa) := inferInstance
  haveI : SecondCountableTopology (RA E a b v) := inferInstance
  haveI : LocallyCompactSpace (RA E a b v) := inferInstance
  haveI : FirstCountableTopology (RA E a b v × G a) := inferInstance
  haveI : LocallyCompactSpace (RA E a b v × G a) := inferInstance
  set K : G a → ((Ma v).V →L[ℂ] (Ma v).V) := fun t => ka v t.val with hK
  have hKc : Continuous K := (hka v).1
  have hKs : HasCompactSupport K := (hka v).2
  have hfj : ∀ j P, f j P = c⁻¹ * ∫ t, ⟪eb Ma v (j.1.1 v), K t (Rv v μa μb ν ka kb ψ f j (P * ιA v t))⟫_ℂ ∂μa := by
    intro j P
    have h := congrFun (congrFun hrep j) P
    rw [conv_slice hF D hC v ka kb ψ f hT hf j P] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  obtain ⟨g, hg⟩ : ∃ g : Io Ma Mb κ → RA E a b v × G a → ℂ, g = fun j q =>
      cA v ka kb ψ i j q.1 * ⟪eb Ma v (j.1.1 v), K q.2 (Rv v μa μb ν ka kb ψ f j (p * ιA v q.2 * σA v q.1))⟫_ℂ :=
    ⟨_, rfl⟩
  have hRc : ∀ j, Continuous fun q : RA E a b v × G a => Rv v μa μb ν ka kb ψ f j (p * ιA v q.2 * σA v q.1) :=
    fun j => continuous_Rv_comp v hf hka hkb hψ j
      ((continuous_const.mul ((continuous_ιA v).comp continuous_snd)).mul ((continuous_σA v).comp continuous_fst))
  have hgi : ∀ j, Integrable (g j) ((restA μa μb ν v).prod μa) := by
    intro j
    obtain ⟨hc1, hcs1⟩ := cA_props v hka hkb hψ i j
    rw [hg]
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hc1.comp continuous_fst).mul (continuous_const.inner ((hKc.comp continuous_snd).clm_apply (hRc j)))
    · refine HasCompactSupport.intro (IsCompact.prod hcs1 hKs) fun q hq => ?_
      simp only [Set.mem_prod, not_and_or] at hq
      rcases hq with hq | hq
      · simp only [image_eq_zero_of_notMem_tsupport hq, zero_mul]
      · simp only [image_eq_zero_of_notMem_tsupport hq, ContinuousLinearMap.zero_apply, inner_zero_right,
          mul_zero]
  have hI : ∀ j, ∫ r, cA v ka kb ψ i j r * f j (p * σA v r) ∂restA μa μb ν v =
      c⁻¹ * ∫ t, ∫ r, g j (r, t) ∂restA μa μb ν v ∂μa := by
    intro j
    have e1 : ∀ r, cA v ka kb ψ i j r * f j (p * σA v r) = c⁻¹ * ∫ t, g j (r, t) ∂μa := by
      intro r
      rw [hfj j, mul_left_comm, ← integral_const_mul]
      refine congrArg (c⁻¹ * ·) (integral_congr_ae (ae_of_all _ fun t => ?_))
      rw [hg]
      beta_reduce
      rw [show p * σA v r * ιA v t = p * ιA v t * σA v r by rw [mul_assoc, σA_ιA, ← mul_assoc]]
    rw [integral_congr_ae (ae_of_all _ e1), integral_const_mul,
      integral_integral_swap (f := fun r t => g j (r, t)) (hgi j)]
  have hWi : Integrable (fun t => K t (St v μa μb ν ka kb ψ f i q0 (p * ιA v t))) μa := by
    refine Continuous.integrable_of_hasCompactSupport (hKc.clm_apply (continuous_St v hf hka hkb hψ i q0 p)) ?_
    exact HasCompactSupport.intro hKs fun t ht => by
      rw [image_eq_zero_of_notMem_tsupport ht, ContinuousLinearMap.zero_apply]
  have hsum : ∀ q, ∑ j ∈ Finset.univ.filter (fun j : Io Ma Mb κ => j.1.1 v = q),
      ∫ r, cA v ka kb ψ i j r * f j (p * σA v r) ∂restA μa μb ν v =
      c⁻¹ * ⟪eb Ma v q, ∫ t, K t (St v μa μb ν ka kb ψ f i q0 (p * ιA v t)) ∂μa⟫_ℂ := by
    intro q
    simp only [hI]
    rw [← Finset.mul_sum, ← integral_finset_sum _ fun j _ => (hgi j).integral_prod_right]
    congr 1
    rw [← integral_inner hWi]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    beta_reduce
    rw [St_indep v ka kb ψ f i q0 q]
    simp only [St, map_sum, inner_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjq : j.1.1 v = q := (Finset.mem_filter.1 hj).2
    obtain ⟨hc1, hcs1⟩ := cA_props v hka hkb hψ i j
    have hR1 : Continuous fun r : RA E a b v => Rv v μa μb ν ka kb ψ f j (p * ιA v t * σA v r) :=
      continuous_Rv_comp v hf hka hkb hψ j (continuous_const.mul (continuous_σA v))
    have hi1 : Integrable (fun r => cA v ka kb ψ i j r • Rv v μa μb ν ka kb ψ f j (p * ιA v t * σA v r))
        (restA μa μb ν v) :=
      (hc1.smul hR1).integrable_of_hasCompactSupport (HasCompactSupport.intro hcs1 fun r hr => by
        show cA v ka kb ψ i j r • Rv v μa μb ν ka kb ψ f j (p * ιA v t * σA v r) = 0
        rw [image_eq_zero_of_notMem_tsupport hr, zero_smul])
    rw [← ContinuousLinearMap.integral_comp_comm (K t) hi1, ← integral_inner ((K t).integrable_comp hi1)]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    rw [hg]
    beta_reduce
    simp only [map_smul, inner_smul_right, hjq]
  conv_lhs => rw [Rv]
  simp only [hsum, mul_smul]
  rw [← Finset.smul_sum, OrthonormalBasis.sum_repr']

theorem FA_eq_act (hF : CompatFub) (D : Dom E a b) (hC : Compat D μa μb ν) (v : InfinitePlace E) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (hT : IsTestM (tens ka kb ψ))
    (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) {c : ℂ} (hc : c ≠ 0) (hrep : conv D.μ (tens ka kb ψ) f = c • f) (i : Io Ma Mb κ)
    (q0 : Ix (Ma v)) (y : GA E a) (m₂ : GA E b) {x : Mat a} (hx : x ∈ GLs a) :
    FA v μa μb ν ka kb ψ f i y m₂ x = c⁻¹ • act μa (Ma v) (ka v) (FtA v μa μb ν ka kb ψ f i q0 y m₂) x := by
  rw [FA, dif_pos hx, Rv_eq hF D hC v ka kb ψ f hT hf hka hkb hψ hc hrep i q0]
  congr 1
  show _ = ∫ t : G a, ka v t.val (FtA v μa μb ν ka kb ψ f i q0 y m₂ (x * t.val)) ∂μa
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  have hxt : x * t.val ∈ GLs a := GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs hx (val_mem_GLs t)
  have hm : GeneralLinearGroup.mkOfDetNeZero (x * t.val) hxt = GeneralLinearGroup.mkOfDetNeZero x hx * t :=
    Units.ext rfl
  simp only [FtA, dif_pos hxt, hm, ιA_mul, mul_assoc]

theorem continuousOn_FtA (v : InfinitePlace E) (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (f : Io Ma Mb κ → H E a b → ℂ) (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) (i : Io Ma Mb κ) (q : Ix (Ma v)) (y : GA E a) (m₂ : GA E b) :
    ContinuousOn (FtA v μa μb ν ka kb ψ f i q y m₂) (GLs a) := by
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
  show Continuous (fun x : GLs a => FtA v μa μb ν ka kb ψ f i q y m₂ x.1)
  have e : (fun x : GLs a => FtA v μa μb ν ka kb ψ f i q y m₂ x.1) =
      fun x : GLs a => St v μa μb ν ka kb ψ f i q ((y, m₂) * ιA v (GeneralLinearGroup.mkOfDetNeZero x.1 x.2)) := by
    funext x
    simp only [FtA, dif_pos x.2]
  rw [e]
  exact (continuous_St v hf hka hkb hψ i q (y, m₂)).comp hm

theorem FA_mem_CE (hF : CompatFub) (D : Dom E a b) (hC : Compat D μa μb ν) (v : InfinitePlace E) (ka : Kers Ma)
    (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (hT : IsTestM (tens ka kb ψ))
    (hf : ∀ i, Continuous (f i))
    (hka : ∀ w, Continuous (fun t : G a => ka w t.val) ∧ HasCompactSupport (fun t : G a => ka w t.val))
    (hkb : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val))
    (hψ : IsFinM ψ) {c : ℂ} (hc : c ≠ 0) (hrep : conv D.μ (tens ka kb ψ) f = c • f) {val : Inf a → ℂ} {T : ℝ}
    (hkv : IsMult μa (Ma v) (ka v) val T) (i : Io Ma Mb κ) (y : GA E a) (m₂ : GA E b) :
    FA v μa μb ν ka kb ψ f i y m₂ ∈ CE (Ma v) := by
  have hA := GelP.act_mem_CE_of_mult μa hkv
    (continuousOn_FtA (μa := μa) (μb := μb) (ν := ν) v ka kb ψ f hf hka hkb hψ i (i.1.1 v) y m₂)
  letI : NormedAddCommGroup (Mat a) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mat a) := Matrix.normedSpace
  refine ⟨(hA.1.const_smul c⁻¹).congr fun x hx =>
    FA_eq_act hF D hC v ka kb ψ f hT hf hka hkb hψ hc hrep i (i.1.1 v) y m₂ hx, ?_⟩
  intro g hg k
  have hgk : g * k.1 ∈ GLs a := GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs hg (GlobalTheory.CompanionTheory.WaveAll.unitary_mem_GLs k)
  rw [FA_eq_act hF D hC v ka kb ψ f hT hf hka hkb hψ hc hrep i (i.1.1 v) y m₂ hgk,
    FA_eq_act hF D hC v ka kb ψ f hT hf hka hkb hψ hc hrep i (i.1.1 v) y m₂ hg, hA.2 g hg k, map_smul]

theorem gelA (hW : WaveEx) (hF : CompatFub) (hTT : TensTest) (D : Dom E a b) (hC : Compat D μa μb ν)
    (v : InfinitePlace E) {ka : Kers Ma} {kb : Kers Mb} {va : InfinitePlace E → Inf a → ℂ}
    {vb : InfinitePlace E → Inf b → ℂ} {T : ℝ} {ψ : Matrix κ κ (Hf E a b → ℂ)} {f : Io Ma Mb κ → H E a b → ℂ}
    {g : ℝ → ℝ} {s : Bool} {m : ℕ} (hka : IsMults μa ka va T) (hkb : IsMults μb kb vb T) (hψ : IsFinM ψ)
    (hg : IsBump g T) (hf : ∀ i, Continuous (f i)) {c c' : ℂ} (hc : c ≠ 0)
    (hrep : conv D.μ (tens ka kb ψ) f = c • f) (k' : Mat a → ((Ma v).V →L[ℂ] (Ma v).V))
    (hk0 : IsKer μa (Ma v) [] g (ka v)) (hk' : IsKer μa (Ma v) [(s, m)] g k')
    (hrep' : conv D.μ (tens (Function.update ka v k') kb ψ) f = c' • f) (i : Io Ma Mb κ) (y : GA E a) (m₂ : GA E b)
    {x : Mat a} (hx : x ∈ GLs a) :
    gel s m (PositivityTheory.RgBcC.Bridge.along v y fun z => f i (z, m₂)) x =
      (c' / c) • PositivityTheory.RgBcC.Bridge.along v y (fun z => f i (z, m₂)) x := by
  set ka₂ := Function.update ka v k' with hka₂
  have hka₂m : IsMults μa ka₂ (Function.update va v (fun χ => zVal [(s, m)] χ * coshT g (cas χ))) T := by
    intro w
    by_cases h : w = v
    · subst h; simp only [hka₂, Function.update_self]; exact GelP.isMult_of_isKer μa hg hk'
    · simp only [hka₂, Function.update_of_ne h]; exact hka w
  have hkc : ∀ {k : Kers Ma} {vk : InfinitePlace E → Inf a → ℂ}, IsMults μa k vk T →
      ∀ w, Continuous (fun t : G a => k w t.val) ∧ HasCompactSupport (fun t : G a => k w t.val) :=
    fun h w => ⟨mult_continuous (h w), mult_hasCompactSupport (h w)⟩
  have hkbc : ∀ w, Continuous (fun t : G b => kb w t.val) ∧ HasCompactSupport (fun t : G b => kb w t.val) :=
    fun w => ⟨mult_continuous (hkb w), mult_hasCompactSupport (hkb w)⟩
  have hT := (hTT E a b μa μb Ma Mb κ ka kb va vb T ψ hka hkb hψ).1
  have hT₂ := (hTT E a b μa μb Ma Mb κ ka₂ kb _ vb T ψ hka₂m hkb hψ).1
  have hFA : FA v μa μb ν ka₂ kb ψ f i y m₂ = FA v μa μb ν ka kb ψ f i y m₂ := by
    funext z
    unfold FA
    split_ifs with hz
    · rw [Rv_congr v (fun w hw => Function.update_of_ne hw _ _)]
    · rfl
  have hCE := FA_mem_CE hF D hC v ka kb ψ f hT hf (hkc hka) hkbc hψ hc hrep (hka v) i y m₂
  have hFc := continuousOn_FA v ka kb ψ f hf (hkc hka) hkbc hψ i y m₂ (μa := μa) (μb := μb) (ν := ν)
  refine GelP.gel_eigen_of_act μa hW hk0 hk' (hka v) hCE hFc (eb Ma v (i.1.1 v)) hc ?_ ?_ hx
  · intro x' hx'
    have h := along_conv hF D hC v ka kb ψ f hT hf (hkc hka) hkbc hψ i y m₂ hx'
    rw [hrep, along_eq v y m₂ _ hx'] at h
    rw [along_eq v y m₂ (f i) hx', ← h]
    simp [Pi.smul_apply]
  · intro x' hx'
    have h := along_conv hF D hC v ka₂ kb ψ f hT₂ hf (hkc hka₂m) hkbc hψ i y m₂ hx'
    rw [hrep', along_eq v y m₂ _ hx', hFA] at h
    simp only [hka₂, Function.update_self] at h
    rw [along_eq v y m₂ (f i) hx', ← h]
    simp [Pi.smul_apply]

end Slice

end PositivityTheory.Rg.BcB.CG

end
