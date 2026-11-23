import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPolyRadialCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSectionStab
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAtGq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoFrameLoc

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

namespace DC

open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.P.TheSecStab

section block

variable {k : ℕ}

def sR (T T' : ℝ) (ζ : ℂ) : ℝ := Real.sqrt (Complex.normSq ζ / (T * T') - 1)

theorem sZ_eq (T T' : ℝ) (ζ : ℂ) : sZ T T' ζ = ((sR T T' ζ : ℝ) : ℂ) := rfl

theorem sR_pos {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) : 0 < sR T T' ζ := by
  unfold sR
  apply Real.sqrt_pos.2
  rw [sub_pos, one_lt_div (mul_pos hT hT')]
  exact hζ

theorem sw_rel (hk : 1 ≤ k) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) :
    sZ T T' ζ * sZ T T' ζ = wZ T T' ζ * star (wZ T T' ζ) - 1 := by
  have hTT : 0 < T * T' := mul_pos hT hT'
  have harg : 0 ≤ Complex.normSq ζ / (T * T') - 1 := by
    rw [sub_nonneg, le_div_iff₀ hTT]
    linarith
  have hcpos : 0 < Real.sqrt T * Real.sqrt T' := mul_pos (Real.sqrt_pos.2 hT) (Real.sqrt_pos.2 hT')
  have hc2 : (Real.sqrt T * Real.sqrt T') ^ 2 = T * T' := by
    rw [mul_pow, Real.sq_sqrt hT.le, Real.sq_sqrt hT'.le]
  unfold sZ wZ
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt harg]
  rw [star_mul', star_neg, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [show (-(((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ))⁻¹ * ζ) * (-(((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ))⁻¹ * (starRingEnd ℂ) ζ)
      = ((((Real.sqrt T * Real.sqrt T') ^ 2 : ℝ) : ℂ))⁻¹ * (ζ * (starRingEnd ℂ) ζ) by push_cast; ring,
    Complex.mul_conj, hc2]
  push_cast
  ring

theorem gA_last {a : Fin (k + 1) → ℂ} {T : ℝ} (hT : 0 < T) (ha : herm (Hb k) a a = -(T : ℂ)) :
    gA k a T *ᵥ Pi.single (Fin.last k) 1 = (((Real.sqrt T : ℝ) : ℂ))⁻¹ • a := by
  have h := (gA_spec k hT ha).2
  have hne : ((Real.sqrt T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT).ne'
  rw [Matrix.mulVec_smul] at h
  calc gA k a T *ᵥ Pi.single (Fin.last k) 1
      = (((Real.sqrt T : ℝ) : ℂ))⁻¹ • (((Real.sqrt T : ℝ) : ℂ) • (gA k a T *ᵥ Pi.single (Fin.last k) 1)) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = _ := by rw [h]

theorem gB_unit {b : Fin (k + 1) → ℂ} {T' : ℝ} (hT' : 0 < T') (hb : herm (Hb k) b b = -(T' : ℂ)) :
    IsUnit (gB k b T').det := (UHb_inv (show gB k b T' ∈ UH (Hb k) from (gB_spec k hT' hb).1)).1

theorem secB_mem (hk : 1 ≤ k) {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (ha : herm (Hb k) a a = -(T : ℂ)) (hb : herm (Hb k) b b = -(T' : ℂ)) {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) :
    theSecB k a b T T' ζ ∈ UH (Hb k) := ((theSecB_core k hk a b T T' hT hT' ha hb).2 ζ hζ).1

theorem secB_b (hk : 1 ≤ k) {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (ha : herm (Hb k) a a = -(T : ℂ)) (hb : herm (Hb k) b b = -(T' : ℂ)) (ζ : ℂ) :
    theSecB k a b T T' ζ *ᵥ b = (((Real.sqrt T' * sR T T' ζ : ℝ) : ℂ)) • (gA k a T *ᵥ Pi.single 0 1) +
      (((Real.sqrt T' : ℝ) : ℂ) * wZ T T' ζ * (((Real.sqrt T : ℝ) : ℂ))⁻¹) • a := by
  unfold theSecB
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (gB_spec k hT' hb).2, Matrix.mulVec_smul, nu_last_vec hk,
    Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, gA_last hT ha, sZ_eq, smul_add,
    smul_smul, smul_smul, smul_smul]
  push_cast
  rw [mul_assoc]

theorem nu_back (hk : 1 ≤ k) (w s : ℂ) (hw : s * s = w * star w - 1) :
    nu k w s *ᵥ ((-s) • Pi.single 0 1 + star w • Pi.single (Fin.last k) 1) = Pi.single (Fin.last k) 1 := by
  have h0 := zero_ne_last hk
  rw [nu_mulVec]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, h0, h0.symm, if_true, if_false]
  by_cases hi0 : i = 0
  · subst hi0
    simp only [h0, if_true, if_false]
    ring
  · by_cases hil : i = Fin.last k
    · subst hil
      simp only [h0.symm, if_true, if_false]
      linear_combination -hw
    · simp only [hi0, hil, if_false]
      ring

theorem secB_inv_a (hk : 1 ≤ k) {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (ha : herm (Hb k) a a = -(T : ℂ)) (hb : herm (Hb k) b b = -(T' : ℂ)) {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) :
    (theSecB k a b T T' ζ)⁻¹ *ᵥ a = (((-(Real.sqrt T * sR T T' ζ) : ℝ) : ℂ)) • ((gB k b T')⁻¹ *ᵥ Pi.single 0 1) +
      (((Real.sqrt T : ℝ) : ℂ) * star (wZ T T' ζ) * (((Real.sqrt T' : ℝ) : ℂ))⁻¹) • b := by
  have hU := (UHb_inv (secB_mem hk hT hT' ha hb hζ)).1
  have hne : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT').ne'
  have key : theSecB k a b T T' ζ *ᵥ ((((-(Real.sqrt T * sR T T' ζ) : ℝ) : ℂ)) • ((gB k b T')⁻¹ *ᵥ Pi.single 0 1) +
      (((Real.sqrt T : ℝ) : ℂ) * star (wZ T T' ζ) * (((Real.sqrt T' : ℝ) : ℂ))⁻¹) • b) = a := by
    unfold theSecB
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec _ (gB k b T') _, Matrix.mul_nonsing_inv _ (gB_unit hT' hb), Matrix.one_mulVec,
      (gB_spec k hT' hb).2, smul_smul]
    have e : (((-(Real.sqrt T * sR T T' ζ) : ℝ) : ℂ)) • (Pi.single 0 1 : Fin (k + 1) → ℂ) +
        (((Real.sqrt T : ℝ) : ℂ) * star (wZ T T' ζ) * (((Real.sqrt T' : ℝ) : ℂ))⁻¹ * ((Real.sqrt T' : ℝ) : ℂ)) •
          (Pi.single (Fin.last k) 1 : Fin (k + 1) → ℂ) =
        ((Real.sqrt T : ℝ) : ℂ) • ((-(sZ T T' ζ)) • (Pi.single 0 1 : Fin (k + 1) → ℂ) +
          star (wZ T T' ζ) • (Pi.single (Fin.last k) 1 : Fin (k + 1) → ℂ)) := by
      rw [smul_add, smul_smul, smul_smul, sZ_eq, mul_assoc _ _ ((Real.sqrt T' : ℝ) : ℂ), inv_mul_cancel₀ hne, mul_one]
      push_cast
      rw [mul_neg]
    rw [e, Matrix.mulVec_smul, nu_back hk _ _ (sw_rel hk hT hT' hζ)]
    exact (gA_spec k hT ha).2
  have h2 := congrArg (fun v => (theSecB k a b T T' ζ)⁻¹ *ᵥ v) key
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec] at h2
  exact h2.symm

theorem boost_first_orthogonal (hk : 1 ≤ k) {a : Fin (k + 1) → ℂ} {T : ℝ} (hT : 0 < T) (ha : herm (Hb k) a a = -(T : ℂ)) :
    herm (Hb k) (gA k a T *ᵥ Pi.single 0 1) a = 0 := by
  have h0 := zero_ne_last hk
  have h := form_of_unitary (Hb k) (gA_spec k hT ha).1 (Pi.single 0 1) (((Real.sqrt T : ℝ) : ℂ) • Pi.single (Fin.last k) 1)
  rw [(gA_spec k hT ha).2] at h
  rw [h, herm_smul_right, herm_Hb_right]
  simp [h0.symm]

theorem boost_first_unit_norm (hk : 1 ≤ k) {a : Fin (k + 1) → ℂ} {T : ℝ} (hT : 0 < T) (ha : herm (Hb k) a a = -(T : ℂ)) :
    herm (Hb k) (gA k a T *ᵥ Pi.single 0 1) (gA k a T *ᵥ Pi.single 0 1) = 1 := by
  have h0 := zero_ne_last hk
  rw [form_of_unitary (Hb k) (gA_spec k hT ha).1, herm_Hb_right]
  simp [h0]

theorem gB_adj {b : Fin (k + 1) → ℂ} {T' : ℝ} (hT' : 0 < T') (hb : herm (Hb k) b b = -(T' : ℂ)) (x y : Fin (k + 1) → ℂ) :
    herm (Hb k) x ((gB k b T')⁻¹ *ᵥ y) = herm (Hb k) (gB k b T' *ᵥ x) y := by
  rw [← form_of_unitary (Hb k) (gB_spec k hT' hb).1 x, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (gB_unit hT' hb),
    Matrix.one_mulVec]

theorem inverse_boost_first_orthogonal (hk : 1 ≤ k) {b : Fin (k + 1) → ℂ} {T' : ℝ} (hT' : 0 < T') (hb : herm (Hb k) b b = -(T' : ℂ)) :
    herm (Hb k) ((gB k b T')⁻¹ *ᵥ Pi.single 0 1) b = 0 := by
  have h0 := zero_ne_last hk
  rw [← SettingConstruction.herm_symm (Hb k) (SettingConstruction.Hb_herm k), gB_adj hT' hb, (gB_spec k hT' hb).2, herm_smul_left, herm_Hb_right]
  simp [h0]

theorem inverse_boost_first_unit_norm (hk : 1 ≤ k) {b : Fin (k + 1) → ℂ} {T' : ℝ} (hT' : 0 < T') (hb : herm (Hb k) b b = -(T' : ℂ)) :
    herm (Hb k) ((gB k b T')⁻¹ *ᵥ Pi.single 0 1) ((gB k b T')⁻¹ *ᵥ Pi.single 0 1) = 1 := by
  have h0 := zero_ne_last hk
  rw [gB_adj hT' hb, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (gB_unit hT' hb), Matrix.one_mulVec, herm_Hb_right]
  simp [h0]

theorem secB_perp {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT' : 0 < T') (hb : herm (Hb k) b b = -(T' : ℂ)) (ζ : ℂ)
    {x : Fin (k + 1) → ℂ} (hxb : herm (Hb k) x b = 0) (hx0 : herm (Hb k) x ((gB k b T')⁻¹ *ᵥ Pi.single 0 1) = 0) :
    theSecB k a b T T' ζ *ᵥ x = gA k a T *ᵥ (gB k b T' *ᵥ x) := by
  have hne : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT').ne'
  have c0 : (gB k b T' *ᵥ x) 0 = 0 := by
    rw [gB_adj hT' hb, herm_Hb_right] at hx0
    have hs : (if (0 : Fin (k + 1)) = Fin.last k then (-1 : ℂ) else 1) ≠ 0 := by split_ifs <;> norm_num
    exact (mul_eq_zero.1 hx0).resolve_left hs
  have cl : (gB k b T' *ᵥ x) (Fin.last k) = 0 := by
    rw [← form_of_unitary (Hb k) (gB_spec k hT' hb).1, (gB_spec k hT' hb).2, herm_smul_right, herm_Hb_right, if_pos rfl] at hxb
    have h1 : star ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by rw [show star ((Real.sqrt T' : ℝ) : ℂ) = _ from Complex.conj_ofReal _]; exact hne
    have h2 := (mul_eq_zero.1 hxb).resolve_left h1
    exact (mul_eq_zero.1 h2).resolve_left (by norm_num)
  unfold theSecB
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, nu_mulVec, c0, cl, zero_smul, zero_smul, add_zero, add_zero]

end block

section big

variable {k r : ℕ}

theorem jV_add (u v : Fin (k + 1) → ℂ) : jV k r (u + v) = jV k r u + jV k r v := by
  ext i
  simp only [jV, Pi.add_apply]
  split_ifs <;> simp

theorem jV_smul (c : ℂ) (u : Fin (k + 1) → ℂ) : jV k r (c • u) = c • jV k r u := by
  ext i
  simp only [jV, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem emb_mulVec_of (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    embWb k r μ *ᵥ v = jV k r (μ *ᵥ wbPart k r v) := by
  have h := emb_mulVec_jV (r := r) μ (wbPart k r v)
  rwa [jV_wbPart hv] at h

theorem herm_of {u v : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (hv : inWb k r v) :
    herm (Hpk k r) u v = herm (Hb k) (wbPart k r u) (wbPart k r v) := by
  have h := herm_jV (r := r) (wbPart k r u) (wbPart k r v)
  rwa [jV_wbPart hu, jV_wbPart hv] at h

def EE (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  jV k r (gA k (wbPart k r z) (Tz k r z) *ᵥ Pi.single 0 1)

def EE' (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  jV k r ((gB k (wbPart k r z') (Tz k r z'))⁻¹ *ᵥ Pi.single 0 1)

theorem prWv_fix {z x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (h0 : herm (Hpk k r) x z = 0) :
    SSn.prWv k r z x = x := by
  have hw : SSn.wbP k r x = x := by
    funext i
    unfold SSn.wbP
    split_ifs with h
    · rfl
    · exact (hx i (by omega)).symm
  unfold SSn.prWv
  rw [hw, h0, zero_div, zero_smul, add_zero]

theorem prWv_self {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) : SSn.prWv k r z z = 0 := by
  have hw : SSn.wbP k r z = z := by
    funext i
    unfold SSn.wbP
    split_ifs with h
    · rfl
    · exact (hz i (by omega)).symm
  have hT0 : ((Tz k r z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold SSn.prWv
  rw [hw, PRhoCut.FL.herm_alt]
  push_cast
  rw [neg_div, div_self hT0, neg_smul, one_smul, add_neg_cancel]

theorem unitH_one {x : Fin (2 * r + k + 1) → ℂ} (h : herm (Hpk k r) x x = 1) : SSn.unitH k r x = x := by
  unfold SSn.unitH
  rw [h]
  simp

theorem unitH_pos {c : ℝ} (hc : 0 < c) {x : Fin (2 * r + k + 1) → ℂ} (h : herm (Hpk k r) x x = 1) :
    SSn.unitH k r (((c : ℝ) : ℂ) • x) = x := by
  have e : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (((c : ℝ) : ℂ) • x) (((c : ℝ) : ℂ) • x) = ((c ^ 2 : ℝ) : ℂ) := by
    unfold Formalism.QuantumDeterminants.herm at h ⊢
    rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, h]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  unfold SSn.unitH
  rw [e, Complex.ofReal_re, Real.sqrt_sq hc.le, smul_smul]
  rw [show (((c⁻¹ : ℝ) : ℂ)) * ((c : ℝ) : ℂ) = 1 by
    push_cast
    exact inv_mul_cancel₀ (by exact_mod_cast hc.ne'), one_smul]

theorem unitH_neg {c : ℝ} (hc : 0 < c) {x : Fin (2 * r + k + 1) → ℂ} (h : herm (Hpk k r) x x = 1) :
    SSn.unitH k r (((-c : ℝ) : ℂ) • x) = -x := by
  have e : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (((-c : ℝ) : ℂ) • x) (((-c : ℝ) : ℂ) • x) = ((c ^ 2 : ℝ) : ℂ) := by
    unfold Formalism.QuantumDeterminants.herm at h ⊢
    rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, h]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  unfold SSn.unitH
  rw [e, Complex.ofReal_re, Real.sqrt_sq hc.le, smul_smul]
  rw [show (((c⁻¹ : ℝ) : ℂ)) * ((-c : ℝ) : ℂ) = -1 by
    push_cast
    rw [mul_neg, inv_mul_cancel₀ (by exact_mod_cast hc.ne')], neg_one_smul]

variable {z z' : Fin (2 * r + k + 1) → ℂ}

theorem muZ_eq (ζ : ℂ) : NF.muZ k r (theSection k r z z') ζ =
    embWb k r (theSecB k (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z') ζ) := rfl

theorem section_first_vector_eq (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {ζ : ℂ}
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) : SSn.nu0 k r z z' (theSection k r z z') ζ = EE k r z := by
  have ha := SettingConstruction.herm_self k r z hz
  have hb := SettingConstruction.herm_self k r z' hz'
  have hE : inWb k r (EE k r z) := inWb_jV _
  have hEz : herm (Hpk k r) (EE k r z) z = 0 := by
    rw [herm_of hE hz, EE, wbPart_jV]
    exact boost_first_orthogonal hk hT ha
  have hEE : herm (Hpk k r) (EE k r z) (EE k r z) = 1 := by
    rw [EE, herm_jV]
    exact boost_first_unit_norm hk hT ha
  unfold SSn.nu0
  rw [muZ_eq, emb_mulVec_of _ hz', secB_b hk hT hT' ha hb, jV_add, jV_smul, jV_smul, jV_wbPart hz, PRhoCut.FL.prWv_add,
    PRhoCut.FL.prWv_smul, PRhoCut.FL.prWv_smul, prWv_self hz hT, smul_zero, add_zero]
  show SSn.unitH k r (_ • SSn.prWv k r z (EE k r z)) = _
  rw [prWv_fix hE hEz]
  exact unitH_pos (mul_pos (Real.sqrt_pos.2 hT') (sR_pos hT hT' hζ)) hEE

theorem EE'_facts (hk : 1 ≤ k) (hz' : inWb k r z') (hT' : 0 < Tz k r z') :
    inWb k r (EE' k r z') ∧ herm (Hpk k r) (EE' k r z') z' = 0 ∧ herm (Hpk k r) (EE' k r z') (EE' k r z') = 1 := by
  have hb := SettingConstruction.herm_self k r z' hz'
  refine ⟨inWb_jV _, ?_, ?_⟩
  · rw [EE', herm_of (inWb_jV _) hz', wbPart_jV]
    exact inverse_boost_first_orthogonal hk hT' hb
  · rw [EE', herm_jV]
    exact inverse_boost_first_unit_norm hk hT' hb

theorem nu0'_eq (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {ζ : ℂ}
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) : SSn.nu0' k r z z' (theSection k r z z') ζ = -EE' k r z' := by
  have ha := SettingConstruction.herm_self k r z hz
  have hb := SettingConstruction.herm_self k r z' hz'
  obtain ⟨hE, hEz, hEE⟩ := EE'_facts (r := r) hk hz' hT'
  unfold SSn.nu0'
  rw [muZ_eq, emb_inv (secB_mem hk hT hT' ha hb hζ), emb_mulVec_of _ hz, secB_inv_a hk hT hT' ha hb hζ, jV_add, jV_smul, jV_smul, jV_wbPart hz', PRhoCut.FL.prWv_add,
    PRhoCut.FL.prWv_smul, PRhoCut.FL.prWv_smul, prWv_self hz' hT', smul_zero, add_zero]
  show SSn.unitH k r (_ • SSn.prWv k r z' (EE' k r z')) = _
  rw [prWv_fix hE hEz]
  exact unitH_neg (mul_pos (Real.sqrt_pos.2 hT) (sR_pos hT hT' hζ)) hEE

theorem muZ_perp (hz' : inWb k r z') (hT' : 0 < Tz k r z') (ζ : ℂ) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u)
    (huz : herm (Hpk k r) u z' = 0) (huE : herm (Hpk k r) u (EE' k r z') = 0) :
    NF.muZ k r (theSection k r z z') ζ *ᵥ u =
      jV k r (gA k (wbPart k r z) (Tz k r z) *ᵥ (gB k (wbPart k r z') (Tz k r z') *ᵥ wbPart k r u)) := by
  have hb := SettingConstruction.herm_self k r z' hz'
  have h1 : herm (Hb k) (wbPart k r u) (wbPart k r z') = 0 := by
    rw [← herm_of hu hz']; exact huz
  have h2 : herm (Hb k) (wbPart k r u) ((gB k (wbPart k r z') (Tz k r z'))⁻¹ *ᵥ Pi.single 0 1) = 0 := by
    rw [EE', herm_of hu (inWb_jV _), wbPart_jV] at huE; exact huE
  rw [muZ_eq, emb_mulVec_of _ hu, secB_perp hT' hb ζ h1 h2]

def uu (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  SSn.prWv k r z' (Pi.single j 1) - herm (Hpk k r) (SSn.prWv k r z' (Pi.single j 1)) (-EE' k r z') • (-EE' k r z')

theorem uu_facts (hk : 1 ≤ k) (hz' : inWb k r z') (hT' : 0 < Tz k r z') (j : Fin (2 * r + k + 1)) :
    inWb k r (uu k r z' j) ∧ herm (Hpk k r) (uu k r z' j) z' = 0 ∧ herm (Hpk k r) (uu k r z' j) (EE' k r z') = 0 := by
  obtain ⟨hE, hEz, hEE⟩ := EE'_facts (r := r) hk hz' hT'
  obtain ⟨hp, hpz⟩ := PRhoCut.FL.prWv_inW hz' hT' (Pi.single j 1)
  have hneg : (-EE' k r z') = (-1 : ℂ) • EE' k r z' := by rw [neg_smul, one_smul]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp only [uu, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    rw [hp i hi, hE i hi]
    simp
  · unfold uu
    rw [herm_sub_left, herm_smul_left, hneg, herm_smul_left, hpz, hEz]
    simp
  · unfold uu
    rw [herm_sub_left, herm_smul_left, hneg, herm_smul_left, herm_smul_right, hEE]
    simp

theorem section_embedding_eq_matrix (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {ζ : ℂ}
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) : SSn.io0 k r z z' (theSection k r z z') ζ =
      Matrix.of fun i j => jV k r (gA k (wbPart k r z) (Tz k r z) *ᵥ
        (gB k (wbPart k r z') (Tz k r z') *ᵥ wbPart k r (uu k r z' j))) i := by
  ext i j
  obtain ⟨h1, h2, h3⟩ := uu_facts (r := r) hk hz' hT' j
  unfold SSn.io0
  rw [Matrix.of_apply, Matrix.of_apply, nu0'_eq hk hz hz' hT hT' hζ]
  exact congrFun (muZ_perp hz' hT' ζ h1 h2 h3) i

end big

end DC

theorem datum_constancy_holds : DatumConst := by
  intro k r z z' hk hz hz' hT hT' ζ ζ₁ hζ hζ₁
  refine ⟨?_, ?_, ?_⟩
  · rw [DC.section_first_vector_eq hk hz hz' hT hT' hζ, DC.section_first_vector_eq hk hz hz' hT hT' hζ₁]
  · rw [DC.nu0'_eq hk hz hz' hT hT' hζ, DC.nu0'_eq hk hz hz' hT hT' hζ₁]
  · rw [DC.section_embedding_eq_matrix hk hz hz' hT hT' hζ, DC.section_embedding_eq_matrix hk hz hz' hT hT' hζ₁]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
