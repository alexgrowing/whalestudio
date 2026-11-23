import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompDefs

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

variable {k r : ℕ}

lemma single_apply_mul (a b i j : Fin (k + 1)) :
    (Matrix.single a b (1 : ℂ)) i j = (Pi.single a 1 : Fin (k + 1) → ℂ) i * (Pi.single b 1 : Fin (k + 1) → ℂ) j := by
  rw [Matrix.single_apply, Pi.single_apply, Pi.single_apply]
  by_cases hi : i = a
  · by_cases hj : j = b
    · subst hi
      subst hj
      simp
    · simp [hj, Ne.symm hj]
  · simp [hi, Ne.symm hi]

lemma nu_lin (w s : ℂ) :
    nu k w s = (1 - Matrix.single 0 0 1 - Matrix.single (Fin.last k) (Fin.last k) 1) + star w • Matrix.single 0 0 1 +
      s • (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) +
      w • Matrix.single (Fin.last k) (Fin.last k) 1 := by
  ext i j
  rw [nu_apply]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, single_apply_mul]
  ring

def aa (r : ℕ) (G G' X : Mb k) : Q.Mx k r := e0 k r (G * X * G')

lemma aa_add (G G' X Y : Mb k) : aa r G G' (X + Y) = aa r G G' X + aa r G G' Y := by
  simp only [aa, e0, Matrix.mul_add, Matrix.add_mul]

lemma aa_smul (G G' X : Mb k) (c : ℂ) : aa r G G' (c • X) = c • aa r G G' X := by
  simp only [aa, e0, Matrix.mul_smul, Matrix.smul_mul]

lemma mu0_eq_corner_entry_expansion (z z' : Fin (2 * r + k + 1) → ℂ) (w : ℂ) :
    mu0 k r z z' w =
      (aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
          (1 - Matrix.single 0 0 1 - Matrix.single (Fin.last k) (Fin.last k) 1) + (1 - Em k r * (Em k r)ᵀ)) +
        star (wZ (Tz k r z) (Tz k r z') w) •
          aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z')) (Matrix.single 0 0 1) +
        sZ (Tz k r z) (Tz k r z') w •
          aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
            (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) +
        wZ (Tz k r z) (Tz k r z') w •
          aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
            (Matrix.single (Fin.last k) (Fin.last k) 1) := by
  have h : mu0 k r z z' w = embWb k r (gA k (wbPart k r z) (Tz k r z) *
      nu k (wZ (Tz k r z) (Tz k r z') w) (sZ (Tz k r z) (Tz k r z') w) * gB k (wbPart k r z') (Tz k r z')) := rfl
  rw [h, emb_eq, nu_lin]
  have h2 : ∀ X : Mb k, Em k r * (gA k (wbPart k r z) (Tz k r z) * X * gB k (wbPart k r z') (Tz k r z')) * (Em k r)ᵀ =
      aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z')) X := fun X => rfl
  rw [h2, aa_add, aa_add, aa_add, aa_smul, aa_smul, aa_smul]
  abel

lemma dZ_lin (f1 f2 f3 : ℂ → ℂ) (a0 a1 a2 a3 ζ : ℂ) (h1 : DifferentiableAt ℝ f1 ζ) (h2 : DifferentiableAt ℝ f2 ζ)
    (h3 : DifferentiableAt ℝ f3 ζ) :
    NF.dZ (fun w => a0 + f1 w * a1 + f2 w * a2 + f3 w * a3) ζ =
        NF.dZ f1 ζ * a1 + NF.dZ f2 ζ * a2 + NF.dZ f3 ζ * a3 ∧
      NF.dZb (fun w => a0 + f1 w * a1 + f2 w * a2 + f3 w * a3) ζ =
        NF.dZb f1 ζ * a1 + NF.dZb f2 ζ * a2 + NF.dZb f3 ζ * a3 := by
  have h : HasFDerivAt (fun w => a0 + f1 w * a1 + f2 w * a2 + f3 w * a3)
      (0 + a1 • fderiv ℝ f1 ζ + a2 • fderiv ℝ f2 ζ + a3 • fderiv ℝ f3 ζ) ζ :=
    (((hasFDerivAt_const a0 ζ).add (h1.hasFDerivAt.mul_const a1)).add (h2.hasFDerivAt.mul_const a2)).add
      (h3.hasFDerivAt.mul_const a3)
  unfold NF.dZ NF.dZb
  rw [h.fderiv]
  simp only [add_apply, zero_apply, smul_apply, smul_eq_mul]
  constructor <;> ring

lemma wZ_has (T T' : ℝ) (ζ : ℂ) :
    HasFDerivAt (wZ T T') ((-(kap T T')⁻¹) • (ContinuousLinearMap.id ℝ ℂ)) ζ :=
  (hasFDerivAt_id ζ).const_mul (-(kap T T')⁻¹)

lemma wZ_d (T T' : ℝ) (ζ : ℂ) : NF.dZ (wZ T T') ζ = -(kap T T')⁻¹ ∧ NF.dZb (wZ T T') ζ = 0 := by
  unfold NF.dZ NF.dZb
  rw [(wZ_has T T' ζ).fderiv]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  constructor
  · linear_combination ((1 / 2 : ℂ) * (kap T T')⁻¹) * Complex.I_mul_I
  · linear_combination (-(1 / 2 : ℂ) * (kap T T')⁻¹) * Complex.I_mul_I

lemma kap_star (T T' : ℝ) : star (kap T T') = kap T T' := Complex.conj_ofReal _

lemma wZs_has (T T' : ℝ) (ζ : ℂ) :
    HasFDerivAt (fun w => star (wZ T T' w))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((-(kap T T')⁻¹) • (ContinuousLinearMap.id ℝ ℂ))) ζ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp ζ (wZ_has T T' ζ)

lemma wZs_d (T T' : ℝ) (ζ : ℂ) :
    NF.dZ (fun w => star (wZ T T' w)) ζ = 0 ∧ NF.dZb (fun w => star (wZ T T' w)) ζ = -(kap T T')⁻¹ := by
  unfold NF.dZ NF.dZb
  rw [(wZs_has T T' ζ).fderiv]
  have hk : conj (kap T T') = kap T T' := kap_star T T'
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul, map_neg, map_inv₀, hk, map_one, Complex.conj_I]
  constructor
  · linear_combination (-(1 / 2 : ℂ) * (kap T T')⁻¹) * Complex.I_mul_I
  · linear_combination ((1 / 2 : ℂ) * (kap T T')⁻¹) * Complex.I_mul_I

lemma normSq_has (ζ : ℂ) :
    HasFDerivAt (fun w : ℂ => Complex.normSq w)
      ((ζ.re • Complex.reCLM + ζ.re • Complex.reCLM) + (ζ.im • Complex.imCLM + ζ.im • Complex.imCLM)) ζ := by
  have h := (Complex.reCLM.hasFDerivAt (x := ζ)).mul (Complex.reCLM.hasFDerivAt (x := ζ))
  have h' := (Complex.imCLM.hasFDerivAt (x := ζ)).mul (Complex.imCLM.hasFDerivAt (x := ζ))
  have h2 := h.add h'
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  simp [Complex.normSq_apply]

lemma sr_facts (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (ζ : ℂ) (hζ : T * T' < Complex.normSq ζ) :
    0 < Complex.normSq ζ / (T * T') - 1 ∧
      Real.sqrt (Complex.normSq ζ / (T * T') - 1) * (Real.sqrt T * Real.sqrt T') = Real.sqrt (Complex.normSq ζ - T * T') ∧
      0 < Real.sqrt (Complex.normSq ζ - T * T') ∧ 0 < Real.sqrt T * Real.sqrt T' ∧
      (Real.sqrt T * Real.sqrt T') * (Real.sqrt T * Real.sqrt T') = T * T' := by
  have hTT : 0 < T * T' := mul_pos hT hT'
  have hne : T * T' ≠ 0 := hTT.ne'
  have hs : Real.sqrt T * Real.sqrt T' = Real.sqrt (T * T') := (Real.sqrt_mul hT.le T').symm
  have h1 : 0 < Complex.normSq ζ / (T * T') - 1 := sub_pos.mpr ((one_lt_div hTT).mpr hζ)
  refine ⟨h1, ?_, Real.sqrt_pos.mpr (sub_pos.mpr hζ),
    mul_pos (Real.sqrt_pos.mpr hT) (Real.sqrt_pos.mpr hT'), ?_⟩
  · rw [hs, ← Real.sqrt_mul h1.le]
    congr 1
    rw [sub_mul, div_mul_cancel₀ _ hne, one_mul]
  · rw [hs, Real.mul_self_sqrt hTT.le]

lemma sZ_has (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (ζ : ℂ) (hζ : T * T' < Complex.normSq ζ) :
    HasFDerivAt (sZ T T')
      ((Complex.ofRealCLM).comp ((1 / (2 * Real.sqrt (Complex.normSq ζ / (T * T') - 1))) •
        ((T * T')⁻¹ • ((ζ.re • Complex.reCLM + ζ.re • Complex.reCLM) + (ζ.im • Complex.imCLM + ζ.im • Complex.imCLM))))) ζ := by
  have h0 := (sr_facts T T' hT hT' ζ hζ).1
  have h1 : HasFDerivAt (fun w : ℂ => Complex.normSq w / (T * T') - 1)
      ((T * T')⁻¹ • ((ζ.re • Complex.reCLM + ζ.re • Complex.reCLM) + (ζ.im • Complex.imCLM + ζ.im • Complex.imCLM))) ζ := by
    have := ((normSq_has ζ).const_mul (T * T')⁻¹).sub_const 1
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    show Complex.normSq w / (T * T') - 1 = (T * T')⁻¹ * Complex.normSq w - 1
    rw [div_eq_inv_mul]
  exact (Complex.ofRealCLM.hasFDerivAt).comp ζ (h1.sqrt h0.ne')

lemma sZ_d (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (ζ : ℂ) (hζ : T * T' < Complex.normSq ζ) :
    NF.dZ (sZ T T') ζ = (2 * kap T T')⁻¹ * conj ζ * (sig (T * T') ζ)⁻¹ ∧
      NF.dZb (sZ T T') ζ = (2 * kap T T')⁻¹ * ζ * (sig (T * T') ζ)⁻¹ := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := sr_facts T T' hT hT' ζ hζ
  unfold NF.dZ NF.dZb
  rw [(sZ_has T T' hT hT' ζ hζ).fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, add_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.ofRealCLM_apply, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, smul_eq_mul, mul_one, mul_zero,
    add_zero, zero_add]
  unfold kap sig
  rw [← h1]
  set sr := Real.sqrt (Complex.normSq ζ / (T * T') - 1) with hsr
  set κ := Real.sqrt T * Real.sqrt T' with hκ
  have hs0 : (sr : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 h0).ne'
  have hk0 : (κ : ℂ) ≠ 0 := by exact_mod_cast h3.ne'
  have hc : conj ζ = (ζ.re : ℂ) - (ζ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hz : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
  rw [← h4, hc]
  constructor
  · push_cast
    field_simp
    ring
  · conv_rhs => rw [hz]
    push_cast
    field_simp
    ring

theorem dmu_both (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (ζ : ℂ)
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    (Matrix.of fun i j => NF.dZ (fun w => mu0 k r z z' w i j) ζ) =
        e0 k r (gA k (wbPart k r z) (Tz k r z) *
          dnu k 0 ((2 * kap (Tz k r z) (Tz k r z'))⁻¹ * conj ζ * (sig (Tz k r z * Tz k r z') ζ)⁻¹)
            (-(kap (Tz k r z) (Tz k r z'))⁻¹) * gB k (wbPart k r z') (Tz k r z')) ∧
      (Matrix.of fun i j => NF.dZb (fun w => mu0 k r z z' w i j) ζ) =
        e0 k r (gA k (wbPart k r z) (Tz k r z) *
          dnu k (-(kap (Tz k r z) (Tz k r z'))⁻¹) ((2 * kap (Tz k r z) (Tz k r z'))⁻¹ * ζ * (sig (Tz k r z * Tz k r z') ζ)⁻¹)
            0 * gB k (wbPart k r z') (Tz k r z')) := by
  have hR : ∀ a b c : ℂ, e0 k r (gA k (wbPart k r z) (Tz k r z) * dnu k a b c * gB k (wbPart k r z') (Tz k r z')) =
      a • aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z')) (Matrix.single 0 0 1) +
        b • aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
            (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) +
        c • aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
            (Matrix.single (Fin.last k) (Fin.last k) 1) := by
    intro a b c
    show aa r _ _ (dnu k a b c) = _
    unfold dnu
    rw [aa_add, aa_add, aa_smul, aa_smul, aa_smul]
  have hL : ∀ i j, (fun w => mu0 k r z z' w i j) = fun w =>
      (aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
          (1 - Matrix.single 0 0 1 - Matrix.single (Fin.last k) (Fin.last k) 1) + (1 - Em k r * (Em k r)ᵀ) : Q.Mx k r) i j +
        star (wZ (Tz k r z) (Tz k r z') w) *
          aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z')) (Matrix.single 0 0 1) i j +
        sZ (Tz k r z) (Tz k r z') w *
          aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
            (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) i j +
        wZ (Tz k r z) (Tz k r z') w *
          aa r (gA k (wbPart k r z) (Tz k r z)) (gB k (wbPart k r z') (Tz k r z'))
            (Matrix.single (Fin.last k) (Fin.last k) 1) i j := by
    intro i j
    funext w
    rw [mu0_eq_corner_entry_expansion]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hd := fun a0 a1 a2 a3 => dZ_lin (fun w => star (wZ (Tz k r z) (Tz k r z') w)) (sZ (Tz k r z) (Tz k r z'))
    (wZ (Tz k r z) (Tz k r z')) a0 a1 a2 a3 ζ (wZs_has _ _ ζ).differentiableAt
    (sZ_has _ _ hT hT' ζ hζ).differentiableAt (wZ_has _ _ ζ).differentiableAt
  constructor
  · ext i j
    rw [Matrix.of_apply, hL, (hd _ _ _ _).1, hR, (wZs_d _ _ ζ).1, (sZ_d _ _ hT hT' ζ hζ).1, (wZ_d _ _ ζ).1]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  · ext i j
    rw [Matrix.of_apply, hL, (hd _ _ _ _).2, hR, (wZs_d _ _ ζ).2, (sZ_d _ _ hT hT' ζ hζ).2, (wZ_d _ _ ζ).2]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem dmu_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (ζ : ℂ)
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    (Matrix.of fun i j => NF.dZ (fun w => mu0 k r z z' w i j) ζ) =
        e0 k r (gA k (wbPart k r z) (Tz k r z) *
          dnu k 0 ((2 * kap (Tz k r z) (Tz k r z'))⁻¹ * conj ζ * (sig (Tz k r z * Tz k r z') ζ)⁻¹)
            (-(kap (Tz k r z) (Tz k r z'))⁻¹) * gB k (wbPart k r z') (Tz k r z')) :=
  (dmu_both k r z z' hT hT' ζ hζ).1

theorem dmub_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (ζ : ℂ)
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    (Matrix.of fun i j => NF.dZb (fun w => mu0 k r z z' w i j) ζ) =
        e0 k r (gA k (wbPart k r z) (Tz k r z) *
          dnu k (-(kap (Tz k r z) (Tz k r z'))⁻¹) ((2 * kap (Tz k r z) (Tz k r z'))⁻¹ * ζ * (sig (Tz k r z * Tz k r z') ζ)⁻¹)
            0 * gB k (wbPart k r z') (Tz k r z')) :=
  (dmu_both k r z z' hT hT' ζ hζ).2

theorem sZ_eq (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (ζ : ℂ) (hζ : T * T' < Complex.normSq ζ) :
    sZ T T' ζ = (kap T T')⁻¹ * sig (T * T') ζ := by
  obtain ⟨_, h1, _, h3, _⟩ := sr_facts T T' hT hT' ζ hζ
  unfold sZ kap sig
  rw [← h1]
  have key : ∀ sr κ : ℝ, 0 < κ → ((sr : ℝ) : ℂ) = ((κ : ℝ) : ℂ)⁻¹ * ((sr * κ : ℝ) : ℂ) := by
    intro sr κ h
    have h0 : (κ : ℂ) ≠ 0 := by exact_mod_cast h.ne'
    push_cast
    field_simp
  exact key _ _ h3

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
