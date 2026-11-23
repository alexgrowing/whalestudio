import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRAsmPS

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

namespace PSC

open Asm

variable {TT : ℝ}

theorem ev_ann {ζ : ℂ} (h : TT < Complex.normSq ζ) : ∀ᶠ w in nhds ζ, TT < Complex.normSq w :=
  (isOpen_lt continuous_const Complex.continuous_normSq).mem_nhds h

theorem fderiv_congr {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f g : ℂ → V}
    (h : ∀ ζ : ℂ, TT < Complex.normSq ζ → f ζ = g ζ) {ζ : ℂ} (hζ : TT < Complex.normSq ζ) :
    fderiv ℝ f ζ = fderiv ℝ g ζ :=
  Filter.EventuallyEq.fderiv_eq ((ev_ann hζ).mono h)

theorem dZ_congr {f g : ℂ → ℂ} (h : ∀ ζ : ℂ, TT < Complex.normSq ζ → f ζ = g ζ) {ζ : ℂ}
    (hζ : TT < Complex.normSq ζ) : NF.dZ f ζ = NF.dZ g ζ := by
  simp only [NF.dZ, fderiv_congr h hζ]

theorem dZb_congr {f g : ℂ → ℂ} (h : ∀ ζ : ℂ, TT < Complex.normSq ζ → f ζ = g ζ) {ζ : ℂ}
    (hζ : TT < Complex.normSq ζ) : NF.dZb f ζ = NF.dZb g ζ := by
  simp only [NF.dZb, fderiv_congr h hζ]

theorem dZ_add {f g : ℂ → ℂ} {ζ : ℂ} (hf : DifferentiableAt ℝ f ζ) (hg : DifferentiableAt ℝ g ζ) :
    NF.dZ (fun w => f w + g w) ζ = NF.dZ f ζ + NF.dZ g ζ := by
  have h : HasFDerivAt (fun w => f w + g w) (fderiv ℝ f ζ + fderiv ℝ g ζ) ζ := hf.hasFDerivAt.add hg.hasFDerivAt
  simp only [NF.dZ, h.fderiv, add_apply]
  ring

theorem dZb_add {f g : ℂ → ℂ} {ζ : ℂ} (hf : DifferentiableAt ℝ f ζ) (hg : DifferentiableAt ℝ g ζ) :
    NF.dZb (fun w => f w + g w) ζ = NF.dZb f ζ + NF.dZb g ζ := by
  have h : HasFDerivAt (fun w => f w + g w) (fderiv ℝ f ζ + fderiv ℝ g ζ) ζ := hf.hasFDerivAt.add hg.hasFDerivAt
  simp only [NF.dZb, h.fderiv, add_apply]
  ring

theorem dZ_mul {f g : ℂ → ℂ} {ζ : ℂ} (hf : DifferentiableAt ℝ f ζ) (hg : DifferentiableAt ℝ g ζ) :
    NF.dZ (fun w => f w * g w) ζ = f ζ * NF.dZ g ζ + g ζ * NF.dZ f ζ := by
  have h : HasFDerivAt (fun w => f w * g w) (f ζ • fderiv ℝ g ζ + g ζ • fderiv ℝ f ζ) ζ :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  simp only [NF.dZ, h.fderiv, add_apply, smul_apply, smul_eq_mul]
  ring

theorem dZb_mul {f g : ℂ → ℂ} {ζ : ℂ} (hf : DifferentiableAt ℝ f ζ) (hg : DifferentiableAt ℝ g ζ) :
    NF.dZb (fun w => f w * g w) ζ = f ζ * NF.dZb g ζ + g ζ * NF.dZb f ζ := by
  have h : HasFDerivAt (fun w => f w * g w) (f ζ • fderiv ℝ g ζ + g ζ • fderiv ℝ f ζ) ζ :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  simp only [NF.dZb, h.fderiv, add_apply, smul_apply, smul_eq_mul]
  ring

theorem dZ_const (c ζ : ℂ) : NF.dZ (fun _ => c) ζ = 0 := by
  have h : HasFDerivAt (fun _ : ℂ => c) (0 : ℂ →L[ℝ] ℂ) ζ := hasFDerivAt_const c ζ
  simp [NF.dZ, h.fderiv]

theorem dZb_const (c ζ : ℂ) : NF.dZb (fun _ => c) ζ = 0 := by
  have h : HasFDerivAt (fun _ : ℂ => c) (0 : ℂ →L[ℝ] ℂ) ζ := hasFDerivAt_const c ζ
  simp [NF.dZb, h.fderiv]

theorem dZ_id (ζ : ℂ) : NF.dZ id ζ = 1 := by
  have h : HasFDerivAt (id : ℂ → ℂ) (ContinuousLinearMap.id ℝ ℂ) ζ := hasFDerivAt_id ζ
  simp only [NF.dZ, h.fderiv, ContinuousLinearMap.id_apply, Complex.I_mul_I]
  norm_num

theorem dZb_id (ζ : ℂ) : NF.dZb id ζ = 0 := by
  have h : HasFDerivAt (id : ℂ → ℂ) (ContinuousLinearMap.id ℝ ℂ) ζ := hasFDerivAt_id ζ
  simp only [NF.dZb, h.fderiv, ContinuousLinearMap.id_apply, Complex.I_mul_I]
  norm_num

theorem conj_hasFDerivAt (ζ : ℂ) : HasFDerivAt (fun w : ℂ => conj w) (Complex.conjCLE : ℂ →L[ℝ] ℂ) ζ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt

theorem dZ_conj (ζ : ℂ) : NF.dZ (fun w : ℂ => conj w) ζ = 0 := by
  simp only [NF.dZ, (conj_hasFDerivAt ζ).fderiv, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one,
    Complex.conj_I, mul_neg, Complex.I_mul_I]
  norm_num

theorem dZb_conj (ζ : ℂ) : NF.dZb (fun w : ℂ => conj w) ζ = 1 := by
  simp only [NF.dZb, (conj_hasFDerivAt ζ).fderiv, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one,
    Complex.conj_I, mul_neg, Complex.I_mul_I]
  norm_num

structure DPS (TT : ℝ) (f : ℂ → ℂ) : Prop where
  diff : ∀ ζ : ℂ, TT < Complex.normSq ζ → DifferentiableAt ℝ f ζ
  ps : PS TT f
  dz : PS TT (NF.dZ f)
  dzb : PS TT (NF.dZb f)

theorem DPS.congr {f g : ℂ → ℂ} (hf : DPS TT f) (h : ∀ ζ : ℂ, TT < Complex.normSq ζ → g ζ = f ζ) : DPS TT g where
  diff := fun ζ hζ => (hf.diff ζ hζ).congr_of_eventuallyEq ((ev_ann hζ).mono h)
  ps := PS.congr hf.ps h
  dz := PS.congr hf.dz fun _ hζ => dZ_congr h hζ
  dzb := PS.congr hf.dzb fun _ hζ => dZb_congr h hζ

theorem DPS.const (TT : ℝ) (c : ℂ) : DPS TT (fun _ => c) where
  diff := fun _ _ => differentiableAt_const c
  ps := PS.const TT c
  dz := PS.congr (PS.const TT 0) fun ζ _ => dZ_const c ζ
  dzb := PS.congr (PS.const TT 0) fun ζ _ => dZb_const c ζ

theorem PS.id (TT : ℝ) : PS TT id := ⟨0, MvPolynomial.X 0, fun ζ _ => by simp⟩

theorem PS.conj (TT : ℝ) : PS TT (fun ζ => conj ζ) := ⟨0, MvPolynomial.X 1, fun ζ _ => by simp⟩

theorem PS.sig (TT : ℝ) : PS TT (sig TT) := ⟨0, MvPolynomial.X 2, fun ζ _ => by simp⟩

theorem gg_ne {ζ : ℂ} (h : TT < Complex.normSq ζ) : gg TT ζ ≠ 0 := by
  simp only [gg, ne_eq, Complex.ofReal_eq_zero]
  exact (sub_pos.2 h).ne'

theorem PS.ggi (TT : ℝ) : PS TT (fun ζ => (gg TT ζ)⁻¹) :=
  ⟨1, 1, fun ζ hζ => by rw [pow_one, mul_inv_cancel₀ (gg_ne hζ), map_one]⟩

theorem DPS.id (TT : ℝ) : DPS TT id where
  diff := fun _ _ => differentiableAt_id
  ps := PS.id TT
  dz := PS.congr (PS.const TT 1) fun ζ _ => dZ_id ζ
  dzb := PS.congr (PS.const TT 0) fun ζ _ => dZb_id ζ

theorem DPS.conj (TT : ℝ) : DPS TT (fun ζ => conj ζ) where
  diff := fun ζ _ => (conj_hasFDerivAt ζ).differentiableAt
  ps := PS.conj TT
  dz := PS.congr (PS.const TT 0) fun ζ _ => dZ_conj ζ
  dzb := PS.congr (PS.const TT 1) fun ζ _ => dZb_conj ζ

theorem DPS.add {f g : ℂ → ℂ} (hf : DPS TT f) (hg : DPS TT g) : DPS TT (fun ζ => f ζ + g ζ) where
  diff := fun ζ hζ => (hf.diff ζ hζ).add (hg.diff ζ hζ)
  ps := PS.add hf.ps hg.ps
  dz := PS.congr (PS.add hf.dz hg.dz) fun ζ hζ => dZ_add (hf.diff ζ hζ) (hg.diff ζ hζ)
  dzb := PS.congr (PS.add hf.dzb hg.dzb) fun ζ hζ => dZb_add (hf.diff ζ hζ) (hg.diff ζ hζ)

theorem DPS.mul {f g : ℂ → ℂ} (hf : DPS TT f) (hg : DPS TT g) : DPS TT (fun ζ => f ζ * g ζ) where
  diff := fun ζ hζ => (hf.diff ζ hζ).mul (hg.diff ζ hζ)
  ps := PS.mul hf.ps hg.ps
  dz := PS.congr (PS.add (PS.mul hf.ps hg.dz) (PS.mul hg.ps hf.dz)) fun ζ hζ => dZ_mul (hf.diff ζ hζ) (hg.diff ζ hζ)
  dzb := PS.congr (PS.add (PS.mul hf.ps hg.dzb) (PS.mul hg.ps hf.dzb))
    fun ζ hζ => dZb_mul (hf.diff ζ hζ) (hg.diff ζ hζ)

theorem DPS.pow {f : ℂ → ℂ} (hf : DPS TT f) (m : ℕ) : DPS TT (fun ζ => f ζ ^ m) := by
  induction m with
  | zero => exact (DPS.const TT 1).congr fun ζ _ => pow_zero _
  | succ m ih => exact (ih.mul hf).congr fun ζ _ => pow_succ _ _

theorem gg_eq (TT : ℝ) (ζ : ℂ) : gg TT ζ = id ζ * conj ζ + (-(TT : ℂ)) := by
  simp only [gg, id, Complex.mul_conj]
  push_cast
  ring

theorem gg_diff (TT : ℝ) (ζ : ℂ) : DifferentiableAt ℝ (gg TT) ζ := by
  have h : gg TT = fun w => id w * conj w + (-(TT : ℂ)) := funext (gg_eq TT)
  rw [h]
  exact (differentiableAt_id.mul (conj_hasFDerivAt ζ).differentiableAt).add (differentiableAt_const _)

theorem dZ_gg (TT : ℝ) (ζ : ℂ) : NF.dZ (gg TT) ζ = conj ζ := by
  have h : gg TT = fun w => id w * conj w + (-(TT : ℂ)) := funext (gg_eq TT)
  rw [h, dZ_add (f := fun w => id w * conj w) (g := fun _ => -(TT : ℂ))
    (differentiableAt_id.mul (conj_hasFDerivAt ζ).differentiableAt) (differentiableAt_const _),
    dZ_mul (f := id) (g := fun w => conj w) differentiableAt_id (conj_hasFDerivAt ζ).differentiableAt,
    dZ_const, dZ_id, dZ_conj]
  ring

theorem dZb_gg (TT : ℝ) (ζ : ℂ) : NF.dZb (gg TT) ζ = ζ := by
  have h : gg TT = fun w => id w * conj w + (-(TT : ℂ)) := funext (gg_eq TT)
  rw [h, dZb_add (f := fun w => id w * conj w) (g := fun _ => -(TT : ℂ))
    (differentiableAt_id.mul (conj_hasFDerivAt ζ).differentiableAt) (differentiableAt_const _),
    dZb_mul (f := id) (g := fun w => conj w) differentiableAt_id (conj_hasFDerivAt ζ).differentiableAt,
    dZb_const, dZb_id, dZb_conj]
  simp

theorem normSq_diff (ζ : ℂ) : DifferentiableAt ℝ (fun w : ℂ => Complex.normSq w) ζ := by
  have h : (fun w : ℂ => Complex.normSq w) =
      fun w => Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w := by
    funext w
    simp [Complex.normSq_apply]
  rw [h]
  exact (Complex.reCLM.differentiableAt.mul Complex.reCLM.differentiableAt).add
    (Complex.imCLM.differentiableAt.mul Complex.imCLM.differentiableAt)

theorem sig_diff {ζ : ℂ} (h : TT < Complex.normSq ζ) : DifferentiableAt ℝ (sig TT) ζ := by
  have h1 : DifferentiableAt ℝ (fun w : ℂ => Real.sqrt (Complex.normSq w - TT)) ζ :=
    ((normSq_diff ζ).sub_const TT).sqrt (sub_pos.2 h).ne'
  exact Complex.ofRealCLM.differentiableAt.comp ζ h1

theorem ggi_diff {ζ : ℂ} (h : TT < Complex.normSq ζ) : DifferentiableAt ℝ (fun w => (gg TT w)⁻¹) ζ := by
  have h1 : DifferentiableAt ℝ (fun w : ℂ => (Complex.normSq w - TT)⁻¹) ζ :=
    ((normSq_diff ζ).sub_const TT).inv (sub_pos.2 h).ne'
  have h2 : (fun w => (gg TT w)⁻¹) = fun w => Complex.ofRealCLM ((Complex.normSq w - TT)⁻¹) := by
    funext w
    simp [gg]
  rw [h2]
  exact Complex.ofRealCLM.differentiableAt.comp ζ h1

theorem sig_sq {ζ : ℂ} (h : TT < Complex.normSq ζ) : sig TT ζ * sig TT ζ = gg TT ζ := by
  simp only [sig, gg, ← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt (sub_pos.2 h).le]

theorem sig_ne {ζ : ℂ} (h : TT < Complex.normSq ζ) : sig TT ζ ≠ 0 := fun h0 =>
  gg_ne h (by rw [← sig_sq h, h0, mul_zero])

theorem dZ_sig {ζ : ℂ} (h : TT < Complex.normSq ζ) :
    NF.dZ (sig TT) ζ = (1 / 2 : ℂ) * (conj ζ * (sig TT ζ * (gg TT ζ)⁻¹)) := by
  have h1 : NF.dZ (fun w => sig TT w * sig TT w) ζ = conj ζ := by
    rw [dZ_congr (fun w hw => sig_sq hw) h, dZ_gg]
  rw [dZ_mul (sig_diff h) (sig_diff h)] at h1
  have hs := sig_ne h
  rw [← sig_sq h, ← h1]
  field_simp
  ring

theorem dZb_sig {ζ : ℂ} (h : TT < Complex.normSq ζ) :
    NF.dZb (sig TT) ζ = (1 / 2 : ℂ) * (ζ * (sig TT ζ * (gg TT ζ)⁻¹)) := by
  have h1 : NF.dZb (fun w => sig TT w * sig TT w) ζ = ζ := by
    rw [dZb_congr (fun w hw => sig_sq hw) h, dZb_gg]
  rw [dZb_mul (sig_diff h) (sig_diff h)] at h1
  have hs := sig_ne h
  rw [← sig_sq h]
  nth_rewrite 2 [← h1]
  field_simp
  ring

theorem dZ_ggi {ζ : ℂ} (h : TT < Complex.normSq ζ) :
    NF.dZ (fun w => (gg TT w)⁻¹) ζ = (-1 : ℂ) * (conj ζ * ((gg TT ζ)⁻¹ * (gg TT ζ)⁻¹)) := by
  have h1 : NF.dZ (fun w => gg TT w * (gg TT w)⁻¹) ζ = 0 := by
    rw [dZ_congr (fun w hw => mul_inv_cancel₀ (gg_ne hw)) h, dZ_const]
  rw [dZ_mul (gg_diff TT ζ) (ggi_diff h), dZ_gg] at h1
  have hs := gg_ne h
  have h2 : NF.dZ (fun w => (gg TT w)⁻¹) ζ = -((gg TT ζ)⁻¹ * ((gg TT ζ)⁻¹ * conj ζ)) := by
    rw [eq_neg_iff_add_eq_zero, ← mul_zero (gg TT ζ)⁻¹, ← h1, mul_add, inv_mul_cancel_left₀ hs]
  rw [h2]
  ring

theorem dZb_ggi {ζ : ℂ} (h : TT < Complex.normSq ζ) :
    NF.dZb (fun w => (gg TT w)⁻¹) ζ = (-1 : ℂ) * (ζ * ((gg TT ζ)⁻¹ * (gg TT ζ)⁻¹)) := by
  have h1 : NF.dZb (fun w => gg TT w * (gg TT w)⁻¹) ζ = 0 := by
    rw [dZb_congr (fun w hw => mul_inv_cancel₀ (gg_ne hw)) h, dZb_const]
  rw [dZb_mul (gg_diff TT ζ) (ggi_diff h), dZb_gg] at h1
  have hs := gg_ne h
  have h2 : NF.dZb (fun w => (gg TT w)⁻¹) ζ = -((gg TT ζ)⁻¹ * ((gg TT ζ)⁻¹ * ζ)) := by
    rw [eq_neg_iff_add_eq_zero, ← mul_zero (gg TT ζ)⁻¹, ← h1, mul_add, inv_mul_cancel_left₀ hs]
  rw [h2]
  ring

theorem DPS.sig (TT : ℝ) : DPS TT (sig TT) where
  diff := fun _ hζ => sig_diff hζ
  ps := PS.sig TT
  dz := PS.congr (PS.mul (PS.const TT (1 / 2)) (PS.mul (PS.conj TT) (PS.mul (PS.sig TT) (PS.ggi TT))))
    fun _ hζ => dZ_sig hζ
  dzb := PS.congr (PS.mul (PS.const TT (1 / 2)) (PS.mul (PS.id TT) (PS.mul (PS.sig TT) (PS.ggi TT))))
    fun _ hζ => dZb_sig hζ

theorem DPS.ggi (TT : ℝ) : DPS TT (fun ζ => (gg TT ζ)⁻¹) where
  diff := fun _ hζ => ggi_diff hζ
  ps := PS.ggi TT
  dz := PS.congr (PS.mul (PS.const TT (-1)) (PS.mul (PS.conj TT) (PS.mul (PS.ggi TT) (PS.ggi TT))))
    fun _ hζ => dZ_ggi hζ
  dzb := PS.congr (PS.mul (PS.const TT (-1)) (PS.mul (PS.id TT) (PS.mul (PS.ggi TT) (PS.ggi TT))))
    fun _ hζ => dZb_ggi hζ

theorem DPS.coord (TT : ℝ) (i : Fin 3) : DPS TT (fun ζ => (![ζ, conj ζ, PR.sig TT ζ] : Fin 3 → ℂ) i) := by
  fin_cases i
  · exact DPS.id TT
  · exact DPS.conj TT
  · exact DPS.sig TT

theorem DPS.eval (TT : ℝ) (p : MvPolynomial (Fin 3) ℂ) :
    DPS TT (fun ζ => MvPolynomial.eval ![ζ, conj ζ, PR.sig TT ζ] p) := by
  induction p using MvPolynomial.induction_on with
  | C a => exact (DPS.const TT a).congr fun ζ _ => MvPolynomial.eval_C a
  | add p q hp hq => exact (hp.add hq).congr fun ζ _ => map_add _ p q
  | mul_X p i hp => exact (hp.mul (DPS.coord TT i)).congr fun ζ _ => by rw [map_mul, MvPolynomial.eval_X]

theorem DPS.of_PS {f : ℂ → ℂ} (hf : PS TT f) : DPS TT f := by
  obtain ⟨m, p, hp⟩ := hf
  refine (((DPS.ggi TT).pow m).mul (DPS.eval TT p)).congr fun ζ hζ => ?_
  rw [← hp ζ hζ, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (gg_ne hζ), one_pow, one_mul]

theorem PSV.of_fintype {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*} [Fintype ι] (a : ι → ℂ → ℂ) (v : ι → V)
    (ha : ∀ i, PS TT (a i)) {f : ℂ → V} (hf : ∀ ζ : ℂ, TT < Complex.normSq ζ → f ζ = ∑ i, a i ζ • v i) :
    PSV TT f := by
  refine ⟨Fintype.card ι, fun j => a ((Fintype.equivFin ι).symm j), fun j => v ((Fintype.equivFin ι).symm j),
    fun j => ha _, fun ζ hζ => ?_⟩
  rw [hf ζ hζ]
  exact ((Fintype.equivFin ι).symm.sum_comp (fun i => a i ζ • v i)).symm

theorem PSV.add {V : Type*} [AddCommGroup V] [Module ℂ V] {f g : ℂ → V} (hf : PSV TT f) (hg : PSV TT g) :
    PSV TT (fun ζ => f ζ + g ζ) := by
  obtain ⟨n, a, v, ha, hf⟩ := hf
  obtain ⟨n', a', v', ha', hg⟩ := hg
  refine PSV.of_fintype (ι := Fin n ⊕ Fin n') (Sum.elim a a') (Sum.elim v v') ?_ fun ζ hζ => ?_
  · rintro (i | i)
    · exact ha i
    · exact ha' i
  · rw [hf ζ hζ, hg ζ hζ, Fintype.sum_sum_type]
    rfl

theorem PSV.smul {V : Type*} [AddCommGroup V] [Module ℂ V] {a : ℂ → ℂ} {f : ℂ → V} (ha : PS TT a) (hf : PSV TT f) :
    PSV TT (fun ζ => a ζ • f ζ) := by
  obtain ⟨n, b, v, hb, hf⟩ := hf
  refine ⟨n, fun i ζ => a ζ * b i ζ, v, fun i => PS.mul ha (hb i), fun ζ hζ => ?_⟩
  show a ζ • f ζ = ∑ i, (a ζ * b i ζ) • v i
  rw [hf ζ hζ, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _

theorem PSV.map {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (L : V →ₗ[ℂ] V')
    {f : ℂ → V} (hf : PSV TT f) : PSV TT (fun ζ => L (f ζ)) := by
  obtain ⟨n, b, v, hb, hf⟩ := hf
  refine ⟨n, b, fun i => L (v i), hb, fun ζ hζ => ?_⟩
  show L (f ζ) = ∑ i, b i ζ • L (v i)
  rw [hf ζ hζ, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul _ _ _

theorem PSV.const {V : Type*} [AddCommGroup V] [Module ℂ V] (TT : ℝ) (v : V) : PSV TT (fun _ => v) :=
  ⟨1, fun _ _ => 1, fun _ => v, fun _ => PS.const TT 1, fun ζ _ => by simp⟩

theorem fderiv_sum {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ} (a : Fin n → ℂ → ℂ) (v : Fin n → V)
    (ha : ∀ i, PS TT (a i)) {f : ℂ → V} (hf : ∀ ζ : ℂ, TT < Complex.normSq ζ → f ζ = ∑ i, a i ζ • v i) {ζ : ℂ}
    (hζ : TT < Complex.normSq ζ) : fderiv ℝ f ζ = ∑ i, (fderiv ℝ (a i) ζ).smulRight (v i) := by
  have hd : HasFDerivAt (fun w => ∑ i, a i w • v i) (∑ i, (fderiv ℝ (a i) ζ).smulRight (v i)) ζ :=
    HasFDerivAt.fun_sum fun i _ => ((DPS.of_PS (ha i)).diff ζ hζ).hasFDerivAt.smul_const (v i)
  rw [fderiv_congr hf hζ, hd.fderiv]

theorem PSV.dZV {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : ℂ → V} (hf : PSV TT f) :
    PSV TT (CP.dZV f) := by
  obtain ⟨n, a, v, ha, hf⟩ := hf
  refine ⟨n, fun i => NF.dZ (a i), v, fun i => (DPS.of_PS (ha i)).dz, fun ζ hζ => ?_⟩
  simp only [CP.dZV, NF.dZ, fderiv_sum a v ha hf hζ, sum_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← sub_smul, smul_smul]

theorem PSV.dZbV {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : ℂ → V} (hf : PSV TT f) :
    PSV TT (CP.dZbV f) := by
  obtain ⟨n, a, v, ha, hf⟩ := hf
  refine ⟨n, fun i => NF.dZb (a i), v, fun i => (DPS.of_PS (ha i)).dzb, fun ζ hζ => ?_⟩
  simp only [CP.dZbV, NF.dZb, fderiv_sum a v ha hf hζ, sum_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [Finset.smul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← add_smul, smul_smul]

end PSC

open Asm in
theorem polynomial_shift_calculation : PSCalc := by
  intro TT _
  refine ⟨PS.const TT, PSC.PS.id TT, PSC.PS.conj TT, PSC.PS.sig TT, PSC.PS.ggi TT,
    fun f g hf hg => ⟨PS.add hf hg, PS.mul hf hg⟩,
    fun f hf => ⟨(PSC.DPS.of_PS hf).dz, (PSC.DPS.of_PS hf).dzb⟩, ?_⟩
  intro V V' _ _ _ _
  exact ⟨fun f g hf hg => PSC.PSV.add hf hg, fun a f ha hf => PSC.PSV.smul ha hf, fun L f hf => PSC.PSV.map L hf,
    fun f hf => ⟨PSC.PSV.dZV hf, PSC.PSV.dZbV hf⟩, fun v => PSC.PSV.const TT v⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
