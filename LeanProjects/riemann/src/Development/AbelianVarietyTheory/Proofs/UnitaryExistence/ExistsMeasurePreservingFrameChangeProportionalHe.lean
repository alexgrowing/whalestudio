import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeterssonFrameChange

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

variable {r : ℕ}

def Sim (S g : Matrix (Fin r) (Fin r) ℂ) (c : ℂ) : Prop := gᵀ * S * g.map (starRingEnd ℂ) = c • S

theorem Sim.mul {S g h : Matrix (Fin r) (Fin r) ℂ} {c d : ℂ} (hg : Sim S g c) (hh : Sim S h d) :
    Sim S (g * h) (c * d) := by
  unfold Sim at *
  rw [Matrix.transpose_mul, Matrix.map_mul]
  calc _ = hᵀ * (gᵀ * S * g.map (starRingEnd ℂ)) * h.map (starRingEnd ℂ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, Matrix.mul_smul, Matrix.smul_mul, hh, smul_smul]

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma det_ne_zero_of_form_eq {K G M : Matrix (Fin r) (Fin r) ℂ} (hK : K.det ≠ 0)
    (h : Mᵀ * G * M.map (starRingEnd ℂ) = K) : M.det ≠ 0 := by
  intro hM0
  apply hK
  rw [← h, det_mul, det_mul, det_transpose, hM0, zero_mul, zero_mul]

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma form_smul_left_automorphic_membership (c : ℂ) (K A : Matrix (Fin r) (Fin r) ℂ) :
    Aᵀ * (c • K) * A.map (starRingEnd ℂ) = c • (Aᵀ * K * A.map (starRingEnd ℂ)) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma form_smul_right_automorphic_membership (a : ℝ) (K A : Matrix (Fin r) (Fin r) ℂ) :
    ((a : ℂ) • A)ᵀ * K * ((a : ℂ) • A).map (starRingEnd ℂ) =
      ((a ^ 2 : ℝ) : ℂ) • (Aᵀ * K * A.map (starRingEnd ℂ)) := by
  rw [transpose_smul]
  have : ((a : ℂ) • A).map (starRingEnd ℂ) = (a : ℂ) • A.map (starRingEnd ℂ) := by
    ext i j
    simp
  rw [this, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  push_cast
  ring

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma form_mul' (K A B : Matrix (Fin r) (Fin r) ℂ) :
    (A * B)ᵀ * K * (A * B).map (starRingEnd ℂ) =
      Bᵀ * (Aᵀ * K * A.map (starRingEnd ℂ)) * B.map (starRingEnd ℂ) := by
  rw [transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma form_one' (K : Matrix (Fin r) (Fin r) ℂ) :
    (1 : Matrix (Fin r) (Fin r) ℂ)ᵀ * K * (1 : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = K := by
  simp [Matrix.map_one]

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma form_conj_eq_of_similitude {J B g : Matrix (Fin r) (Fin r) ℂ} {c : ℂ} (hc : c ≠ 0) (hB : B.det ≠ 0)
    (hsim : Bᵀ * J * B.map (starRingEnd ℂ) = c • J) (hg : gᵀ * J * g.map (starRingEnd ℂ) = J) :
    (B⁻¹ * g * B)ᵀ * J * (B⁻¹ * g * B).map (starRingEnd ℂ) = J := by
  have hinv : (B⁻¹)ᵀ * J * (B⁻¹).map (starRingEnd ℂ) = c⁻¹ • J := by
    have h1 : (B * B⁻¹)ᵀ * J * (B * B⁻¹).map (starRingEnd ℂ) = J := by
      rw [mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB), form_one']
    rw [form_mul', hsim, form_smul_left_automorphic_membership] at h1
    calc (B⁻¹)ᵀ * J * (B⁻¹).map (starRingEnd ℂ)
        = c⁻¹ • (c • ((B⁻¹)ᵀ * J * (B⁻¹).map (starRingEnd ℂ))) := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • J := by rw [h1]
  rw [form_mul', form_mul', hinv, form_smul_left_automorphic_membership, hg, form_smul_left_automorphic_membership, hsim, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
private lemma exists_transport_haarU_pi {ι : Type} (Ψ Ψ' : Finset ι) (p p' : ℕ) (hΨ : Ψ = Ψ')
    (hp : p = p') :
    ∃ e : (Ψ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r p) ≃ᵐ (Ψ' → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r p'),
      MeasurePreserving e (Measure.pi fun _ => _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.haarU r p)
        (Measure.pi fun _ => _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.haarU r p') ∧
      ∀ t (τ : Ψ) (τ' : Ψ'), τ.1 = τ'.1 → ((e t τ' : GL (Fin r) ℂ)) = (t τ : GL (Fin r) ℂ) := by
  subst hΨ hp
  refine ⟨MeasurableEquiv.refl _, MeasurePreserving.id _, fun t τ τ' h => ?_⟩
  rw [Subtype.ext h]
  rfl

set_option autoImplicit false in
open MeasureTheory Topology Matrix NumberField in
open scoped ENNReal in
variable {r : ℕ} in
theorem _root_.GlobalTheory.PeterssonFrameChange.frame_change : ∀ (E : Type) [Field E]
    [NumberField E] [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (y' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X'.Ψ r), X.Ψ = X'.Ψ → X.p0 = X'.p0 → y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.OrthFr X →
    y' ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.OrthFr X' →
    (∀ (τ : X.Ψ), ∃ t : ℝ, t ≠ 0 ∧ X'.Gm.map τ.1 = (t : ℂ) • X.Gm.map τ.1) →
    ∃ (e : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X ≃ᵐ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X')
      (α : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X)
      (u : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X),
      MeasurePreserving e (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.haarR X) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.haarR X') ∧
      Measurable α ∧ (∀ t, α (α t) = u⁻¹ * t * u) ∧
      ∀ t (τ : X.Ψ) (τ' : X'.Ψ), τ.1 = τ'.1 →
        _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' τ' * ((e (α t) τ' : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
            (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' τ')⁻¹ =
          _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ)⁻¹ := by
  intro E _ _ _ r X X' y y' hΨ hp hy hy' hG
  choose tf htf hGt using hG
  set J := _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.sgnMat r X.p0 with hJdef
  have hJJ : J * J = 1 := by
    rw [hJdef, _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.sgnMat, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> simp
  have hJdet : J.det ≠ 0 := by
    intro h
    have := congrArg det hJJ
    rw [det_mul, h, zero_mul, det_one] at this
    exact zero_ne_one this
  let τ' : X.Ψ → X'.Ψ := fun τ => ⟨τ.1, hΨ ▸ τ.2⟩
  have hy0 : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ) = J := hy
  have hy0' : ∀ τ : X'.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X'.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' τ) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.sgnMat r X'.p0 := hy'
  have hM : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ)ᵀ * X.Gm.map τ.1 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ).map (starRingEnd ℂ) = J := by
    intro τ
    have := hy0 τ
    rwa [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq] at this
  have hM' : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))ᵀ * X'.Gm.map τ.1 *
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ)).map (starRingEnd ℂ) = J := by
    intro τ
    have := hy0' (τ' τ)
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq, ← hp] at this
    exact this
  have hMdet : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ).det ≠ 0 := fun τ => det_ne_zero_of_form_eq hJdet (hM τ)
  have hM'det : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ)).det ≠ 0 := fun τ => det_ne_zero_of_form_eq hJdet (hM' τ)
  set B : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ =>
    ((Real.sqrt |tf τ| : ℝ) : ℂ) • ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ)⁻¹ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ)) with hBdef
  set s : X.Ψ → ℂ := fun τ => ((|tf τ| / tf τ : ℝ) : ℂ) with hsdef
  have hs0 : ∀ τ, s τ ≠ 0 := by
    intro τ
    simp only [hsdef]
    exact_mod_cast div_ne_zero (abs_ne_zero.mpr (htf τ)) (htf τ)
  have hs2 : ∀ τ, s τ * s τ = 1 := by
    intro τ
    simp only [hsdef]
    rw [← Complex.ofReal_mul, ← sq, div_pow, sq_abs, div_self (pow_ne_zero _ (htf τ)), Complex.ofReal_one]
  have hsim : ∀ τ : X.Ψ, (B τ)ᵀ * J * (B τ).map (starRingEnd ℂ) = s τ • J := by
    intro τ
    have ht := htf τ
    have h1 : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))ᵀ * X.Gm.map τ.1 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ)).map (starRingEnd ℂ) =
        ((tf τ : ℝ) : ℂ)⁻¹ • J := by
      have := hM' τ
      rw [hGt τ, form_smul_left_automorphic_membership] at this
      rw [← this, smul_smul, inv_mul_cancel₀ (by exact_mod_cast ht), one_smul]
    simp only [hBdef, hsdef]
    rw [form_smul_right_automorphic_membership, Real.sq_sqrt (abs_nonneg _)]
    conv_lhs => rw [← hM τ]
    rw [← form_mul', mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (hMdet τ)), h1, smul_smul]
    congr 1
    push_cast
    ring
  have hBdet : ∀ τ, (B τ).det ≠ 0 := by
    intro τ
    refine det_ne_zero_of_form_eq ?_ (hsim τ)
    rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ (hs0 τ)) hJdet
  let Bu : X.Ψ → GL (Fin r) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (B τ) (hBdet τ)
  have hBu : ∀ τ, ((Bu τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = B τ := fun τ => rfl
  have hBuinv : ∀ τ, (((Bu τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (B τ)⁻¹ := by
    intro τ
    rw [Matrix.coe_units_inv, hBu]
  have hmem : ∀ g : GL (Fin r) ℂ, g ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r X.p0 ↔
      (g : Matrix (Fin r) (Fin r) ℂ)ᵀ * J * (g : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = J :=
    fun g => Iff.rfl
  have hαmem : ∀ (g : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r X.p0) (τ : X.Ψ),
      (Bu τ)⁻¹ * (g : GL (Fin r) ℂ) * Bu τ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r X.p0 := by
    intro g τ
    rw [hmem, Units.val_mul, Units.val_mul, hBuinv, hBu]
    exact form_conj_eq_of_similitude (hs0 τ) (hBdet τ) (hsim τ) ((hmem g).mp g.2)
  have humem : ∀ τ : X.Ψ, Bu τ * Bu τ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r X.p0 := by
    intro τ
    rw [hmem, Units.val_mul, hBu, form_mul', hsim, form_smul_left_automorphic_membership, hsim, smul_smul, hs2, one_smul]
  let α : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X :=
    fun t τ => ⟨(Bu τ)⁻¹ * (t τ : GL (Fin r) ℂ) * Bu τ, hαmem (t τ) τ⟩
  let u : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X := fun τ => ⟨Bu τ * Bu τ, humem τ⟩
  obtain ⟨e, he, hecoe⟩ := exists_transport_haarU_pi (r := r) X.Ψ X'.Ψ X.p0 X'.p0 hΨ hp
  refine ⟨e, α, u, he, ?_, ?_, ?_⟩
  · have hcont : Continuous α := by
      refine continuous_pi fun τ => Continuous.subtype_mk ?_ _
      exact (continuous_const.mul ((continuous_apply τ).subtype_val)).mul continuous_const
    exact hcont.measurable
  · intro t
    funext τ
    apply Subtype.ext
    show (Bu τ)⁻¹ * ((Bu τ)⁻¹ * (t τ : GL (Fin r) ℂ) * Bu τ) * Bu τ =
      (Bu τ * Bu τ)⁻¹ * (t τ : GL (Fin r) ℂ) * (Bu τ * Bu τ)
    group
  · intro t τ σ hτσ
    obtain rfl : σ = τ' τ := Subtype.ext hτσ.symm
    rw [hecoe (α t) τ (τ' τ) rfl]
    show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) * (((Bu τ)⁻¹ * (t τ : GL (Fin r) ℂ) * Bu τ : GL (Fin r) ℂ) :
      Matrix (Fin r) (Fin r) ℂ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))⁻¹ = _
    rw [Units.val_mul, Units.val_mul, hBuinv, hBu]
    set c : ℂ := ((Real.sqrt |tf τ| : ℝ) : ℂ) with hc
    have hc0 : c ≠ 0 := by
      simp only [hc]
      exact_mod_cast (Real.sqrt_pos.mpr (abs_pos.mpr (htf τ))).ne'
    have hMB : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ * B τ = c • _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) := by
      simp only [hBdef]
      rw [Matrix.mul_smul, mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (hMdet τ))]
    have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) * (B τ)⁻¹ = c⁻¹ • _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ := by
      have : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) = c⁻¹ • (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ * B τ) := by
        rw [hMB, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this, Matrix.smul_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hBdet τ)), Matrix.mul_one]
    have h2 : B τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))⁻¹ = c • (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ)⁻¹ := by
      simp only [hBdef]
      rw [Matrix.smul_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hM'det τ)), Matrix.mul_one]
    calc _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) * ((B τ)⁻¹ * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * B τ) *
          (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))⁻¹
        = (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) * (B τ)⁻¹) * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
          (B τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [h1, h2]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc0, inv_mul_cancel₀ hc0,
          one_smul]

end GlobalTheory.PeterssonFrameChange
