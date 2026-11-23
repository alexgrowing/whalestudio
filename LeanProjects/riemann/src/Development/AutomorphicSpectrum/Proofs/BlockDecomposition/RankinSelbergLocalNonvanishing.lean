import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open MeasureTheory Matrix Filter Topology GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.R
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped ValuativeRel ComplexConjugate

namespace GlobalTheory.CompanionTheory.RSNonvanish

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem fourier_step {ψ : AddChar F Circle} (hψ : IsStd ψ) {G : Fˣ → ℂ} (hG : Integrable G (multHaar F))
    (hf : ∀ x : F, ∫ a : Fˣ, G a * (ψ (-((a : F) * x)) : ℂ) ∂multHaar F = 0)
    {M : ℤ} {G0 : ℂ} (h0 : G0 ≠ 0) (hc : ∀ a : Fˣ, (1 - (a : F)) ∈ valBall F M → G a = G0) : False := by
  classical
  obtain ⟨hψc, hψ1, hcond⟩ := hψ
  set μ := selfDualMeasure ψ with hμ
  set H : Set F := (valBall F (-M) : Set F) with hH
  have hHm : MeasurableSet H := measurableSet_valBall _
  have hHfin : μ H < ⊤ := (isCompact_valBall (-M)).measure_lt_top
  have hHpos : 0 < μ H := (isOpen_valBall (-M)).measure_pos μ ⟨0, zero_mem _⟩
  haveI : IsFiniteMeasure (μ.restrict H) := ⟨by simpa using hHfin⟩
  have hcirc : Continuous fun z : Circle => (z : ℂ) := continuous_subtype_val
  let u : F × Fˣ → ℂ := fun p => (ψ p.1 : ℂ) * (ψ (-((p.2 : F) * p.1)) : ℂ)
  have hum : Measurable u := by
    have hv : Measurable fun p : F × Fˣ => ((p.2 : Fˣ) : F) := measurableEmbedding_units_val.measurable.comp measurable_snd
    have h1 : Measurable fun p : F × Fˣ => (ψ p.1 : ℂ) :=
      (hcirc.comp hψc).measurable.comp measurable_fst
    have h2 : Measurable fun p : F × Fˣ => (ψ (-((p.2 : F) * p.1)) : ℂ) :=
      (hcirc.comp hψc).measurable.comp ((hv.mul measurable_fst).neg)
    exact h1.mul h2
  have hint : Integrable (fun p : F × Fˣ => (ψ p.1 : ℂ) * (G p.2 * (ψ (-((p.2 : F) * p.1)) : ℂ)))
      ((μ.restrict H).prod (multHaar F)) := by
    have hGp : Integrable (fun p : F × Fˣ => G p.2) ((μ.restrict H).prod (multHaar F)) :=
      hG.comp_snd _
    have := hGp.bdd_mul (c := 1) (f := u) hum.aestronglyMeasurable
      (Eventually.of_forall fun p => by simp only [u, norm_mul, Circle.norm_coe, mul_one]; exact le_rfl)
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [u]; ring
  have hswap := integral_integral_swap (f := fun x a => (ψ x : ℂ) * (G a * (ψ (-((a : F) * x)) : ℂ)))
    (μ := μ.restrict H) (ν := multHaar F) hint
  have hleft : ∫ x in H, ∫ a, (ψ x : ℂ) * (G a * (ψ (-((a : F) * x)) : ℂ)) ∂multHaar F ∂μ = 0 := by
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
    show ∫ a, (ψ x : ℂ) * (G a * (ψ (-((a : F) * x)) : ℂ)) ∂multHaar F = 0
    rw [integral_const_mul, hf x, mul_zero]
  let S : Set Fˣ := {a | (1 - (a : F)) ∈ valBall F M}
  have hSo : IsOpen S := (isOpen_valBall M).preimage (continuous_const.sub Units.continuous_val)
  have hSm : MeasurableSet S := by
    have : MeasurableSet ((fun a : Fˣ => 1 - (a : F)) ⁻¹' (valBall F M : Set F)) :=
      (measurable_const.sub measurableEmbedding_units_val.measurable) (measurableSet_valBall M)
    exact this
  have hinner : ∀ a : Fˣ, ∫ x in H, (ψ x : ℂ) * (G a * (ψ (-((a : F) * x)) : ℂ)) ∂μ =
      S.indicator (fun a => G a * (μ.real H : ℂ)) a := by
    intro a
    have e : ∀ x, (ψ x : ℂ) * (G a * (ψ (-((a : F) * x)) : ℂ)) = G a * ((ψ.mulShift (1 - (a : F)) x : Circle) : ℂ) := by
      intro x
      have : ψ.mulShift (1 - (a : F)) x = ψ x * ψ (-((a : F) * x)) := by
        rw [AddChar.mulShift_apply, ← AddChar.map_add_eq_mul]; congr 1; ring
      rw [this, Circle.coe_mul]; ring
    simp_rw [e]
    rw [integral_const_mul, hH, integral_valBall_char]
    have hiff : IsTrivialOn (ψ.mulShift (1 - (a : F))) (-M) ↔ a ∈ S := by
      rw [isTrivialOn_mulShift_iff_mem hψc hψ1, hcond]; simp [S]
    by_cases ha : a ∈ S
    · rw [if_pos (hiff.2 ha), Set.indicator_of_mem ha]
    · rw [if_neg (fun h => ha (hiff.1 h)), Set.indicator_of_notMem ha, mul_zero]
  have hright : ∫ a, ∫ x in H, (ψ x : ℂ) * (G a * (ψ (-((a : F) * x)) : ℂ)) ∂μ ∂multHaar F =
      (G0 * (μ.real H : ℂ)) * ((multHaar F).real S : ℂ) := by
    simp_rw [hinner]
    rw [integral_indicator hSm, setIntegral_congr_fun hSm (g := fun _ => G0 * (μ.real H : ℂ))
      (fun a ha => by simp only []; rw [hc a ha]), setIntegral_const, Complex.real_smul]
    ring
  have hSfin : multHaar F S < ⊤ := by
    have hIS : IntegrableOn G S (multHaar F) := hG.integrableOn
    have hcongr : IntegrableOn (fun _ => G0) S (multHaar F) :=
      hIS.congr_fun (fun a ha => hc a ha) hSm
    exact ((integrableOn_const_iff (by simp)).1 hcongr).resolve_left (by simpa using h0)
  have hSpos : 0 < multHaar F S := hSo.measure_pos _ ⟨1, by simp [S]⟩
  have hz := hswap.symm.trans hleft |>.symm
  rw [hright] at hswap
  have hμr : μ.real H ≠ 0 := (ENNReal.toReal_pos hHpos.ne' hHfin.ne).ne'
  have hSr : (multHaar F).real S ≠ 0 := (ENNReal.toReal_pos hSpos.ne' hSfin.ne).ne'
  have : (G0 * (μ.real H : ℂ)) * ((multHaar F).real S : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h0 (by exact_mod_cast hμr)) (by exact_mod_cast hSr)
  exact this (by rw [← hswap]; exact hleft)

def low (y : F) : GL (Fin 2) F :=
  ⟨!![1, 0; y, 1], !![1, 0; -y, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem dg_uni (a : Fˣ) (n : F) : dg2 a 1 * uni2 n = uni2 ((a : F) * n) * dg2 a 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem dg_dg (a b d : Fˣ) : dg2 a 1 * dg2 b d = dg2 d d * dg2 (a * b * d⁻¹) 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem borel_eq (b d : Fˣ) (x : F) :
    GodementSectionLocal.borelElt b d x = uni2 (x * ((d⁻¹ : Fˣ) : F)) * dg2 b d := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni2, dg2, GodementSectionLocal.borelElt_val, Matrix.mul_apply, Fin.sum_univ_two]

theorem mp_of_ord (u : Fˣ) (h : ord (u : F) = 0) (s : ℂ) : mp u s = 1 := by
  have := modulus_cpow_eq_zpow u s
  simp only [mp, this, h, zpow_zero]

theorem Av_mul {ψ : AddChar F Circle} {ω : Fˣ →* ℂˣ} (hω : ∀ z, ‖((ω z : ℂˣ) : ℂ)‖ = 1)
    {W W' : GL (Fin 2) F → ℂ} (hW : Law ψ ω W) (hW' : Law ψ ω W') (c : Fˣ →* ℂˣ) (s : ℂ) (n : F)
    (b d : Fˣ) (hbd : ord ((b * d⁻¹ : Fˣ) : F) = 0) (k : GL (Fin 2) F)
    (hk : ∀ g, W (g * k) = W g) (hk' : ∀ g, W' (g * k) = W' g) :
    Av W W' c s (uni2 n * dg2 b d * k) = (((c (b * d⁻¹))⁻¹ : ℂˣ) : ℂ) * Av W W' c s 1 := by
  have e1 : ∀ (Y : GL (Fin 2) F → ℂ), Law ψ ω Y → (∀ g, Y (g * k) = Y g) → ∀ a : Fˣ,
      Y (dg2 a 1 * (uni2 n * dg2 b d * k)) =
        (ψ ((a : F) * n) : ℂ) * ((ω d : ℂˣ) : ℂ) * Y (dg2 (a * b * d⁻¹) 1 * 1) := by
    intro Y hY hYk a
    rw [← mul_assoc, hYk, ← mul_assoc, dg_uni, mul_assoc, hY.1, dg_dg, hY.2, mul_one]
    ring
  set t : Fˣ := b * d⁻¹ with ht
  let Gf : Fˣ → ℂ := fun a => W (dg2 a 1 * 1) * conj (W' (dg2 a 1 * 1)) * ((c a : ℂˣ) : ℂ) * mp a (s - 1)
  have hpt : ∀ a : Fˣ, W (dg2 a 1 * (uni2 n * dg2 b d * k)) * conj (W' (dg2 a 1 * (uni2 n * dg2 b d * k))) *
      ((c a : ℂˣ) : ℂ) * mp a (s - 1) = (((c t)⁻¹ : ℂˣ) : ℂ) * Gf (t * a) := by
    intro a
    have hta : a * b * d⁻¹ = t * a := by rw [ht, mul_comm (b * d⁻¹) a, mul_assoc]
    have hmp : mp (t * a) (s - 1) = mp a (s - 1) := by
      have h1 : mp (t * a) (s - 1) = mp t (s - 1) * mp a (s - 1) :=
        GodementSectionLocal.modPow_mul (t : F) (a : F) (s - 1)
      rw [h1, mp_of_ord t hbd, one_mul]
    have hc1 : (((c t)⁻¹ : ℂˣ) : ℂ) * ((c (t * a) : ℂˣ) : ℂ) = ((c a : ℂˣ) : ℂ) := by
      rw [map_mul c t a, ← Units.val_mul, inv_mul_cancel_left]
    have hψ1 : (ψ ((a : F) * n) : ℂ) * conj (ψ ((a : F) * n) : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]; simp
    have hω1 : ((ω d : ℂˣ) : ℂ) * conj ((ω d : ℂˣ) : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hω d]; simp
    simp only [Gf]
    rw [e1 W hW hk a, e1 W' hW' hk' a, hta, hmp, map_mul (starRingEnd ℂ), map_mul (starRingEnd ℂ)]
    calc _ = ((ψ ((a : F) * n) : ℂ) * conj (ψ ((a : F) * n) : ℂ)) * (((ω d : ℂˣ) : ℂ) * conj ((ω d : ℂˣ) : ℂ)) *
          (W (dg2 (t * a) 1 * 1) * conj (W' (dg2 (t * a) 1 * 1)) * ((c a : ℂˣ) : ℂ) * mp a (s - 1)) := by ring
      _ = _ := by rw [hψ1, hω1, ← hc1]; ring
  have h1 : Av W W' c s (uni2 n * dg2 b d * k) = ∫ a, (((c t)⁻¹ : ℂˣ) : ℂ) * Gf (t * a) ∂multHaar F :=
    integral_congr_ae (Eventually.of_forall hpt)
  rw [h1, integral_const_mul, integral_mul_left_eq_self Gf t]
  rfl

theorem smul_mem_ball {x y : F} {n : ℤ} (hx : x ∈ valBall F 0) (hy : y ∈ valBall F n) :
    x * y ∈ valBall F n := by
  by_cases h0 : x = 0
  · rw [h0, zero_mul]; exact zero_mem _
  by_cases h1 : y = 0
  · rw [h1, mul_zero]; exact zero_mem _
  rw [mem_valBall_iff_le_ord (mul_ne_zero h0 h1), ord_mul h0 h1]
  rw [mem_valBall_iff_le_ord h0] at hx
  rw [mem_valBall_iff_le_ord h1] at hy
  omega

def boxI (L : ℤ) : (Fin 2 → F) → ℂ := Set.indicator {r | r 0 ∈ valBall F L ∧ r 1 - 1 ∈ valBall F L} 1

theorem boxI_sb {L : ℤ} (hL : 1 ≤ L) : SB (boxI L : (Fin 2 → F) → ℂ) := by
  have hcl : IsClopen ({r | r 0 ∈ valBall F L ∧ r 1 - 1 ∈ valBall F L} : Set (Fin 2 → F)) := by
    have hb : IsClopen (valBall F L : Set F) := ⟨isClosed_valBall L, isOpen_valBall L⟩
    exact (hb.preimage (continuous_apply 0)).inter
      (hb.preimage ((continuous_apply 1).sub continuous_const))
  refine ⟨(LocallyConstant.indicator (LocallyConstant.const (Fin 2 → F) (1 : ℂ)) hcl).isLocallyConstant, ?_⟩
  refine HasCompactSupport.intro (K := Set.pi Set.univ fun _ => (valBall F 0 : Set F))
    (isCompact_univ_pi fun _ => isCompact_valBall 0) fun r hr => ?_
  refine Set.indicator_of_notMem (fun h => hr fun i _ => ?_) _
  have hsub : valBall F L ≤ valBall F 0 := valBall_antitone (by omega)
  have h1 : (1 : F) ∈ valBall F 0 := by
    rw [mem_valBall_iff_le_ord one_ne_zero, ord_one]
  fin_cases i
  · exact hsub h.1
  · simpa using add_mem (hsub h.2) h1

theorem ord_of_sub_one {L : ℤ} (hL : 1 ≤ L) {x : F} (hx : x - 1 ∈ valBall F L) : ord x = 0 := by
  have h : x - 1 ∈ valBall F (ord (1 : F) + 1) := by
    rw [ord_one]; exact valBall_antitone (by omega) hx
  have := (ord_add_eq (one_ne_zero) h).2
  rw [ord_one] at this
  simpa using this

theorem slice_low {L : ℤ} (hL : 1 ≤ L) {y : F} (hy : y ∈ valBall F L) (t : F) :
    GodementSectionLocal.slice (boxI L) (low y) t = Set.indicator {t : F | t - 1 ∈ valBall F L} 1 t := by
  have hsub : valBall F L ≤ valBall F 0 := valBall_antitone (by omega)
  have h1 : (1 : F) ∈ valBall F 0 := by
    rw [mem_valBall_iff_le_ord one_ne_zero, ord_one]
  have hr : (![0, t] ᵥ* ((low y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      ![t * y, t] := by
    rw [GodementSectionLocal.vecMul_zero_cons]
    ext j
    fin_cases j <;> simp [low]
  simp only [GodementSectionLocal.slice, boxI, hr]
  by_cases ht : t - 1 ∈ valBall F L
  · have ht0 : t ∈ valBall F 0 := by simpa using add_mem (hsub ht) h1
    rw [Set.indicator_of_mem (show _ ∈ {t : F | t - 1 ∈ valBall F L} from ht),
      Set.indicator_of_mem]
    · rfl
    · exact ⟨smul_mem_ball ht0 hy, ht⟩
  · rw [Set.indicator_of_notMem (show t ∉ {t : F | t - 1 ∈ valBall F L} from ht),
      Set.indicator_of_notMem]
    exact fun h => ht h.2

def SU (L : ℤ) : Set Fˣ := {u | (u : F) - 1 ∈ valBall F L}

theorem measurableSet_SU (L : ℤ) : MeasurableSet (SU L : Set Fˣ) :=
  (measurableEmbedding_units_val.measurable.sub measurable_const) (measurableSet_valBall L)

theorem isOpen_SU (L : ℤ) : IsOpen (SU L : Set Fˣ) :=
  (isOpen_valBall L).preimage (Units.continuous_val.sub continuous_const)

theorem section_low {L : ℤ} (hL : 1 ≤ L) {y : F} (hy : y ∈ valBall F L) {c : Fˣ →* ℂˣ}
    (hc : ∀ u ∈ (SU L : Set Fˣ), c u = 1) (hord : ∀ u ∈ (SU L : Set Fˣ), ord (u : F) = 0) (s : ℂ) :
    GodementSectionLocal.localSection c c⁻¹ s (boxI L) (low y) = ((multHaar F).real (SU L) : ℂ) := by
  have hdet : GodementSectionLocal.detU (low y) = 1 := by
    apply Units.ext
    simp [GodementSectionLocal.detU, Matrix.GeneralLinearGroup.val_det_apply, low, Matrix.det_fin_two]
  simp only [GodementSectionLocal.localSection, hdet, map_one, Units.val_one, one_mul]
  have h1 : GodementSectionLocal.modPow (1 : F) s = 1 := by simp [GodementSectionLocal.modPow]
  rw [h1, one_mul, localZeta]
  have hpt : ∀ u : Fˣ, GodementSectionLocal.slice (boxI L) (low y) (u : F) *
      (((c * (c⁻¹)⁻¹) u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ (2 * s) =
      (SU L : Set Fˣ).indicator (fun _ => (1 : ℂ)) u := by
    intro u
    rw [slice_low hL hy]
    by_cases hu : u ∈ (SU L : Set Fˣ)
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show (u : F) ∈ {t : F | t - 1 ∈ valBall F L} from hu)]
      have e := mp_of_ord u (hord u hu) (2 * s)
      simp only [mp] at e
      simp [hc u hu, e]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (show (u : F) ∉ {t : F | t - 1 ∈ valBall F L} from hu)]
      simp
  simp_rw [hpt]
  rw [integral_indicator (measurableSet_SU L), setIntegral_const, Complex.real_smul, mul_one]

theorem section_zero {L : ℤ} (hL : 1 ≤ L) {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2)
    (hy : κ 1 0 ∉ valBall F L) (c : Fˣ →* ℂˣ) (s : ℂ) :
    GodementSectionLocal.localSection c c⁻¹ s (boxI L) κ = 0 := by
  have hs : ∀ t : F, t ≠ 0 → GodementSectionLocal.slice (boxI L) κ t = 0 := by
    intro t ht0
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨h0, h1⟩
    rw [GodementSectionLocal.vecMul_zero_cons] at h0 h1
    have hint := (GLnLocal.mem_integralGL_iff F 2).1 hκ
    have h11 : κ 1 1 ∈ valBall F 0 := mem_valBall_zero_iff.2 (hint.1 1 1)
    have hk10 : κ 1 0 ≠ 0 := fun h => hy (h ▸ zero_mem _)
    have hk11 : κ 1 1 ≠ 0 := by
      intro h
      have : (t * (κ : Matrix (Fin 2) (Fin 2) F) 1 1) - 1 = -1 := by
        show t * κ 1 1 - 1 = -1
        rw [h]; simp
      rw [this] at h1
      have h2 : (1 : F) ∈ valBall F L := by simpa using neg_mem h1
      rw [mem_valBall_iff_le_ord one_ne_zero, ord_one] at h2
      omega
    have htk : t * κ 1 1 ≠ 0 := mul_ne_zero ht0 hk11
    have hord0 : ord (t * κ 1 1) = 0 := ord_of_sub_one hL h1
    rw [ord_mul ht0 hk11] at hord0
    rw [mem_valBall_iff_le_ord hk11] at h11
    change t * κ 1 0 ∈ valBall F L at h0
    rw [mem_valBall_iff_le_ord (mul_ne_zero ht0 hk10), ord_mul ht0 hk10] at h0
    exact hy ((mem_valBall_iff_le_ord hk10).2 (by omega))
  simp only [GodementSectionLocal.localSection, localZeta]
  have : ∀ u : Fˣ, GodementSectionLocal.slice (boxI L) κ (u : F) *
      (((c * (c⁻¹)⁻¹) u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ (2 * s) = 0 := by
    intro u; rw [hs _ u.ne_zero]; simp
  simp_rw [this]
  simp

theorem decomp {L : ℤ} (hL : 1 ≤ L) {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2)
    (hy : κ 1 0 ∈ valBall F L) : ∃ (b d : Fˣ) (x γ : F), ord (b : F) = 0 ∧ ord (d : F) = 0 ∧
      γ ∈ valBall F L ∧ κ = GodementSectionLocal.borelElt b d x * low γ := by
  have hdet0 := GodementSectionLocal.ord_det_eq_zero hκ
  have hdetf : ((GodementSectionLocal.detU κ : Fˣ) : F) = κ 0 0 * κ 1 1 - κ 0 1 * κ 1 0 := by
    simp [GodementSectionLocal.detU, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hint := (GLnLocal.mem_integralGL_iff F 2).1 hκ
  have hi : ∀ i j, κ i j ∈ valBall F 0 := fun i j => mem_valBall_zero_iff.2 (hint.1 i j)
  have hnot : κ 1 1 ∉ valBall F 1 := by
    intro h
    have h3 : ((GodementSectionLocal.detU κ : Fˣ) : F) ∈ valBall F 1 := by
      rw [hdetf]
      exact sub_mem (smul_mem_ball (hi 0 0) h)
        (smul_mem_ball (hi 0 1) (valBall_antitone hL hy))
    rw [mem_valBall_iff_le_ord (Units.ne_zero _)] at h3
    have : ord (((GodementSectionLocal.detU κ : Fˣ)) : F) = 0 := hdet0
    omega
  have hne : κ 1 1 ≠ 0 := fun h => hnot (h ▸ zero_mem _)
  have hord : ord (κ 1 1) = 0 := by
    have h0 := (mem_valBall_iff_le_ord hne).1 (hi 1 1)
    have h1 : ¬ (1 ≤ ord (κ 1 1)) := fun h => hnot ((mem_valBall_iff_le_ord hne).2 h)
    omega
  have hinv : (κ 1 1)⁻¹ ∈ valBall F 0 := by
    rw [mem_valBall_iff_le_ord (inv_ne_zero hne), ord_inv hne, hord]; simp
  refine ⟨GodementSectionLocal.detU κ * (Units.mk0 _ hne)⁻¹, Units.mk0 _ hne, κ 0 1, (κ 1 1)⁻¹ * κ 1 0,
    ?_, hord, smul_mem_ball hinv hy, ?_⟩
  · have hd : ((GodementSectionLocal.detU κ : Fˣ) : F) ≠ 0 := Units.ne_zero _
    have e : (((GodementSectionLocal.detU κ * (Units.mk0 _ hne)⁻¹ : Fˣ)) : F) =
        ((GodementSectionLocal.detU κ : Fˣ) : F) * (κ 1 1)⁻¹ := by simp
    have hd0 : ord (((GodementSectionLocal.detU κ : Fˣ)) : F) = 0 := hdet0
    rw [e, ord_mul hd (inv_ne_zero hne), ord_inv hne, hord, hd0]; simp
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GodementSectionLocal.borelElt_val, low, Matrix.mul_apply, Fin.sum_univ_two, hdetf]
    all_goals field_simp
    all_goals ring

theorem sec_Av {ψ : AddChar F Circle} {ω : Fˣ →* ℂˣ} (hω : ∀ z, ‖((ω z : ℂˣ) : ℂ)‖ = 1)
    {W W' : GL (Fin 2) F → ℂ} (hW : Law ψ ω W) (hW' : Law ψ ω W') {c : Fˣ →* ℂˣ} (s : ℂ) {L : ℤ}
    (hL : 1 ≤ L) (hc : ∀ u ∈ (SU L : Set Fˣ), c u = 1)
    (hk : ∀ γ ∈ valBall F L, ∀ g, W (g * low γ) = W g)
    (hk' : ∀ γ ∈ valBall F L, ∀ g, W' (g * low γ) = W' g)
    {κ : GL (Fin 2) F} (hκ : κ ∈ integralGL F 2) (hy : κ 1 0 ∈ valBall F L) :
    GodementSectionLocal.localSection c c⁻¹ s (boxI L) κ * Av W W' c s κ =
      ((multHaar F).real (SU L) : ℂ) * Av W W' c s 1 := by
  obtain ⟨b, d, x, γ, hb, hd, hγ, rfl⟩ := decomp hL hκ hy
  have hbd : ord ((b * d⁻¹ : Fˣ) : F) = 0 := by
    have e : (((b * d⁻¹ : Fˣ)) : F) = (b : F) * (d : F)⁻¹ := by simp
    rw [e, ord_mul b.ne_zero (inv_ne_zero d.ne_zero), ord_inv d.ne_zero, hb, hd]; simp
  have hA := Av_mul hω hW hW' c s (x * ((d⁻¹ : Fˣ) : F)) b d hbd (low γ) (hk γ hγ) (hk' γ hγ)
  rw [← borel_eq] at hA
  have h1 := GodementSectionLocal.localSection_borelElt_mul c c⁻¹ s (boxI L) b d x (low γ)
  have hs := section_low hL hγ hc (fun u hu => ord_of_sub_one hL hu) s
  have hmb : GodementSectionLocal.modPow (b : F) s = 1 := mp_of_ord b hb s
  have hmd : GodementSectionLocal.modPow (d : F) (-s) = 1 := mp_of_ord d hd (-s)
  rw [hA, h1, hs, hmb, hmd]
  have hcc : ((c b : ℂˣ) : ℂ) * (((c⁻¹ d : ℂˣ)) : ℂ) * (((c (b * d⁻¹))⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, ← Units.val_mul]
    simp [map_mul, map_inv]
  linear_combination (((multHaar F).real (SU L) : ℂ) * Av W W' c s 1) * hcc

theorem Av_one_eq_zero [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
    (m : Measure (integralGL F 2)) [m.IsHaarMeasure] [IsProbabilityMeasure m]
    {ψ : AddChar F Circle} {ω : Fˣ →* ℂˣ} (hω : ∀ z, ‖((ω z : ℂˣ) : ℂ)‖ = 1)
    {W W' : GL (Fin 2) F → ℂ} (hW : Law ψ ω W) (hW' : Law ψ ω W') {c : Fˣ →* ℂˣ} (s : ℂ) {L : ℤ}
    (hL : 1 ≤ L) (hc : ∀ u ∈ (SU L : Set Fˣ), c u = 1)
    (hk : ∀ γ ∈ valBall F L, ∀ g, W (g * low γ) = W g)
    (hk' : ∀ γ ∈ valBall F L, ∀ g, W' (g * low γ) = W' g)
    (hZ : Zv m W W' (boxI L) c s = 0) : Av W W' c s 1 = 0 := by
  set C : ℂ := ((multHaar F).real (SU L) : ℂ) * Av W W' c s 1 with hC
  let T : Set (integralGL F 2) := {κ | κ.1 1 0 ∈ valBall F L}
  have hcont : Continuous fun κ : integralGL F 2 => κ.1 1 0 :=
    (continuous_id.matrix_elem 1 0).comp (Units.continuous_val.comp continuous_subtype_val)
  have hTo : IsOpen T := (isOpen_valBall L).preimage hcont
  have hpt : ∀ κ : integralGL F 2, GodementSectionLocal.localSection c c⁻¹ s (boxI L) κ.1 * Av W W' c s κ.1 =
      T.indicator (fun _ => C) κ := by
    intro κ
    by_cases h : κ ∈ T
    · rw [Set.indicator_of_mem h]
      exact sec_Av hω hW hW' s hL hc hk hk' κ.2 h
    · rw [Set.indicator_of_notMem h, section_zero hL κ.2 h, zero_mul]
  have hz : Zv m W W' (boxI L) c s = (m.real T : ℂ) * C := by
    unfold Zv
    simp_rw [hpt]
    rw [integral_indicator hTo.measurableSet, setIntegral_const, Complex.real_smul]
  have hTpos : 0 < m T := hTo.measure_pos m ⟨1, by
    show ((1 : integralGL F 2) : GL (Fin 2) F) 1 0 ∈ valBall F L
    simp [zero_mem]⟩
  have hTr : m.real T ≠ 0 := (ENNReal.toReal_pos hTpos.ne' (measure_ne_top m T)).ne'
  have hSo : 0 < multHaar F (SU L : Set Fˣ) := (isOpen_SU L).measure_pos _ ⟨1, by simp [SU, zero_mem]⟩
  have hSf : multHaar F (SU L : Set Fˣ) < ⊤ := by
    have hcpt : IsCompact (unitFiltrationUnits F 0 : Set Fˣ) := isCompact_unitFiltrationUnits_zero
    refine lt_of_le_of_lt (measure_mono fun u hu => ?_) hcpt.measure_lt_top
    exact mem_unitFiltrationUnits_zero_iff_ord.2 (ord_of_sub_one hL hu)
  have hSr : (multHaar F).real (SU L) ≠ 0 := (ENNReal.toReal_pos hSo.ne' hSf.ne).ne'
  rw [hz] at hZ
  have hC0 : C = 0 := (mul_eq_zero.1 hZ).resolve_left (by exact_mod_cast hTr)
  exact (mul_eq_zero.1 hC0).resolve_left (by exact_mod_cast hSr)

theorem continuous_low : Continuous (low : F → GL (Fin 2) F) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [low, Function.comp_def] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [low] <;> fun_prop

theorem continuous_dg : Continuous (fun a : Fˣ => (dg2 a 1 : GL (Fin 2) F)) := by
  have h1 : Continuous fun a : Fˣ => (a : F) := Units.continuous_val
  have h2 : Continuous fun a : Fˣ => (a : F)⁻¹ := by
    have h3 : Continuous fun a : Fˣ => ((a⁻¹ : Fˣ) : F) := Units.continuous_val.comp continuous_inv
    simpa using h3
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [dg2, Function.comp_def] <;> first | exact h1 | fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [dg2] <;> first | exact h2 | fun_prop

theorem exists_level {c : Fˣ →* ℂˣ} (hc : Continuous c) (U : OpenSubgroup (GL (Fin 2) F)) :
    ∃ L : ℕ, 1 ≤ L ∧ (∀ u ∈ (SU (L : ℤ) : Set Fˣ), c u = 1) ∧ (∀ γ ∈ valBall F (L : ℤ), low γ ∈ U) ∧
      ∀ u ∈ (SU (L : ℤ) : Set Fˣ), (dg2 u 1 : GL (Fin 2) F) ∈ U := by
  obtain ⟨n0, hn0⟩ := exists_unitFiltrationUnits_le_ker hc
  have hl0 : low (0 : F) = 1 := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [low]
  have hd1 : (dg2 (1 : Fˣ) 1 : GL (Fin 2) F) = 1 := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [dg2]
  have S1 : (fun a : Fˣ => (dg2 a 1 : GL (Fin 2) F)) ⁻¹' (U : Set (GL (Fin 2) F)) ∈ 𝓝 (1 : Fˣ) :=
    (U.isOpen.preimage continuous_dg).mem_nhds (by simp [hd1, one_mem])
  have S2 : low ⁻¹' (U : Set (GL (Fin 2) F)) ∈ 𝓝 (0 : F) :=
    (U.isOpen.preimage continuous_low).mem_nhds (by simp [hl0, one_mem])
  obtain ⟨n1, -, hn1⟩ := hasBasis_nhds_one_unitFiltrationUnits.mem_iff.1 S1
  obtain ⟨n2, -, hn2⟩ := hasBasis_nhds_zero_valBall.mem_iff.1 S2
  refine ⟨max (max n0 n1) n2.toNat + 1, by omega, ?_, ?_, ?_⟩
  · intro u hu
    have hm : u ∈ unitFiltrationUnits F (max (max n0 n1) n2.toNat + 1) :=
      (mem_unitFiltrationUnits_iff_valBall (by omega)).2 hu
    exact hn0 (unitFiltrationUnits_antitone (by omega) hm)
  · intro γ hγ
    exact hn2 (valBall_antitone (by omega) hγ)
  · intro u hu
    have hm : u ∈ unitFiltrationUnits F (max (max n0 n1) n2.toNat + 1) :=
      (mem_unitFiltrationUnits_iff_valBall (by omega)).2 hu
    exact hn1 (unitFiltrationUnits_antitone (by omega) hm)

theorem conj_char (ψ : AddChar F Circle) (y : F) : conj ((ψ y : Circle) : ℂ) = ((ψ (-y) : Circle) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem rankin_selberg_nonvanishing_of_whittaker : Ad3.Loc2 → Ad3.R.A10 → Ad3.R.A11 := by
  intro hL hA F _ _ _ _ _ _ ψ hψ _ _ m _ _ μ₁ μ₂ c h1 h2 hc W hW hW1 s hs
  obtain ⟨hWh, -⟩ := hL F ψ hψ μ₁ μ₂ h1 h2
  by_contra hno
  push Not at hno
  have hω : ∀ z, ‖(((μ₁ * μ₂) z : ℂˣ) : ℂ)‖ = 1 := by
    intro z
    simp [h1.2 z, h2.2 z]
  have hLaw : ∀ Y ∈ V2 ψ μ₁ μ₂, Law ψ (μ₁ * μ₂) Y := fun Y hY =>
    ⟨hWh.psi Y hY, fun z g => hWh.cen Y hY z g⟩
  have hlw := hLaw W hW
  obtain ⟨U, hU⟩ := hWh.smooth W hW
  have hAv : ∀ x : F, Av W (fun g => W (g * uni2 x)) c s 1 = 0 := by
    intro x
    have hW' := hWh.stable W hW (uni2 x)
    obtain ⟨U', hU'⟩ := hWh.smooth _ hW'
    obtain ⟨L, hL1, hcL, hlow, -⟩ := exists_level hc.1 (U ⊓ U')
    refine Av_one_eq_zero m hω hlw (hLaw _ hW') s (L := (L : ℤ)) (by exact_mod_cast hL1) hcL
      (fun γ hγ g => hU g _ (hlow γ hγ).1) (fun γ hγ g => hU' g _ (hlow γ hγ).2) ?_
    exact hno x _ (boxI_sb (by exact_mod_cast hL1))
  let G : Fˣ → ℂ := fun a => W (dg2 a 1 * 1) * conj (W (dg2 a 1 * 1)) * ((c a : ℂˣ) : ℂ) * mp a (s - 1)
  have hG : Integrable G (multHaar F) :=
    ((hA F ψ hψ m μ₁ μ₂ c h1 h2 hc W hW W hW).1 s hs).1 1 (one_mem _)
  have hf : ∀ x : F, ∫ a : Fˣ, G a * (ψ (-((a : F) * x)) : ℂ) ∂multHaar F = 0 := by
    intro x
    rw [← hAv x]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show G a * (ψ (-((a : F) * x)) : ℂ) = W (dg2 a 1 * 1) * conj (W (dg2 a 1 * 1 * uni2 x)) *
      ((c a : ℂˣ) : ℂ) * mp a (s - 1)
    simp only [G, mul_one]
    rw [dg_uni, hlw.1, map_mul (starRingEnd ℂ), conj_char]
    ring
  obtain ⟨M, hM1, hcM, -, hdM⟩ := exists_level hc.1 U
  refine fourier_step hψ hG hf (M := (M : ℤ)) (G0 := W 1 * conj (W 1))
    (mul_ne_zero hW1 ((map_ne_zero _).2 hW1)) fun a ha => ?_
  have ha' : a ∈ (SU (M : ℤ) : Set Fˣ) := by
    show (a : F) - 1 ∈ valBall F (M : ℤ)
    simpa using neg_mem ha
  have hord : ord (a : F) = 0 := ord_of_sub_one (L := (M : ℤ)) (by exact_mod_cast hM1) ha'
  have hWa : W (dg2 a 1 * 1) = W 1 := by
    have := hU 1 _ (hdM a ha')
    rw [one_mul] at this
    rw [mul_one, this]
  simp only [G]
  rw [hWa, hcM a ha', mp_of_ord a hord]
  simp

end GlobalTheory.CompanionTheory.RSNonvanish

end
