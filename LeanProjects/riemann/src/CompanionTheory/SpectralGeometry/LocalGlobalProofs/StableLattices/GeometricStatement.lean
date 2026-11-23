import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaParabolicCompactFactorizationStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryMaximalCompactIsCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HilbertSchmidtProjectionBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsGradedMatrixEigenBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InverseGramEigenvaluesSumHsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EigenvalueGapExistsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteNetOfGradedProjectionsStatement

noncomputable section

open Matrix
open scoped Pointwise
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag

namespace GlobalTheory.CompanionTheory.UGeo

variable {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}

local notation "hs" => Formalism.REAL.hs

theorem continuous_hs : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => hs M) := by
  unfold Formalism.REAL.hs
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((continuous_id.matrix_elem i j).norm).pow 2

theorem hs_Pm_pos (hA : IsGrad ε A) (x : S7.UJ ε) : 0 < hs (S7.toM x * Pm A) :=
  hs_pos (toM_mul_ne_zero x (Pm_ne_zero hA))

theorem prod_pos (hA : IsGrad ε A) (x : S7.UJ ε) :
    0 < hs (S7.toM x * Pm A) * (1 + hs (S7.toM x * Pz A)) :=
  mul_pos (hs_Pm_pos hA x) (by linarith [hs_nonneg (S7.toM x * Pz A)])

theorem tau_continuous (hA : IsGrad ε A) : Continuous fun x : S7.UJ ε => tauG A (S7.toM x) := by
  unfold tauG
  have c1 : ∀ P : Matrix (Fin n) (Fin n) ℂ, Continuous fun x : S7.UJ ε => hs (S7.toM x * P) := fun P =>
    continuous_hs.comp ((S7.continuous_toM ε).matrix_mul continuous_const)
  exact continuous_const.mul (Continuous.log ((c1 _).mul (continuous_const.add (c1 _))) fun x => (prod_pos hA x).ne')

theorem exp_tau (hA : IsGrad ε A) (x : S7.UJ ε) :
    Real.exp (-2 * tauG A (S7.toM x)) = hs (S7.toM x * Pm A) * (1 + hs (S7.toM x * Pz A)) := by
  unfold tauG
  rw [show -2 * (-(1 / 2) * Real.log (hs (S7.toM x * Pm A) * (1 + hs (S7.toM x * Pz A)))) =
    Real.log (hs (S7.toM x * Pm A) * (1 + hs (S7.toM x * Pz A))) by ring, Real.exp_log (prod_pos hA x)]

theorem hs_line_Pm (hA : IsGrad ε A) (M : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    hs (M * aT A t * Pm A) = Real.exp (-t) ^ 2 * hs (M * Pm A) := by
  rw [Matrix.mul_assoc, aT_Pm hA, Matrix.mul_smul, hs_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem hs_line_Pp (hA : IsGrad ε A) (M : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    hs (M * aT A t * Pp A) = Real.exp t ^ 2 * hs (M * Pp A) := by
  rw [Matrix.mul_assoc, aT_Pp hA, Matrix.mul_smul, hs_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem hs_line_Pz (hA : IsGrad ε A) (M : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    hs (M * aT A t * Pz A) = hs (M * Pz A) := by
  rw [Matrix.mul_assoc, aT_Pz hA]

theorem tau_add (hA : IsGrad ε A) (x : S7.UJ ε) (t : ℝ) :
    tauG A (S7.toM x * aT A t) = tauG A (S7.toM x) + t := by
  unfold tauG
  rw [hs_line_Pm hA, hs_line_Pz hA, mul_assoc, Real.log_mul (by positivity) (prod_pos hA x).ne', Real.log_pow,
    Real.log_exp]
  push_cast
  ring

theorem hs_mul_unitary (M k : Matrix (Fin n) (Fin n) ℂ) (hk : k * kᴴ = 1) : hs (M * k) = hs M := by
  rw [hs_eq_trace, hs_eq_trace, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k, hk, Matrix.one_mul]

theorem toMK_unitary (k : S7.KG ε) : S7.toMK k * (S7.toMK k)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 k.2.1

theorem toMK_unitary' (k : S7.KG ε) : (S7.toMK k)ᴴ * S7.toMK k = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 k.2.1

theorem comm_of_mem (hA : IsGrad ε A) (k : S7.KG ε) (hk : (k : S7.UJ ε) ∈ PSub ε A) :
    S7.toMK k * Pm A = Pm A * S7.toMK k ∧ S7.toMK k * Pz A = Pz A * S7.toMK k := by
  have hki : ((k : S7.UJ ε))⁻¹ ∈ PSub ε A := (PSub ε A).inv_mem hk
  have hinv : S7.toM ((k : S7.UJ ε))⁻¹ = (S7.toMK k)ᴴ := by
    rw [← toM_inv_eq]
    exact Matrix.inv_eq_left_inv (toMK_unitary' k)
  have s1 : ∀ y ∈ Vm A, S7.toMK k *ᵥ y ∈ Vm A := stable_of_keeps hk.1
  have s2 : ∀ y ∈ Vm A, (S7.toMK k)ᴴ *ᵥ y ∈ Vm A := by
    rw [← hinv]; exact stable_of_keeps hki.1
  have s3 : ∀ y ∈ Wm A, S7.toMK k *ᵥ y ∈ Wm A := stable_of_keeps hk.2
  have s4 : ∀ y ∈ Wm A, (S7.toMK k)ᴴ *ᵥ y ∈ Wm A := by
    rw [← hinv]; exact stable_of_keeps hki.2
  have c1 : Pm A * S7.toMK k = S7.toMK k * Pm A :=
    GlobalTheory.RealIwasawa.proj_comm (W := Vm A) (Pm_conj hA) (fun y => mem_Vm.2 ⟨y, rfl⟩) (fun y hy => by
      obtain ⟨z, rfl⟩ := mem_Vm.1 hy
      rw [Matrix.mulVec_mulVec, Pm_idem hA]) s1 s2
  have c2 : (1 - Pp A) * S7.toMK k = S7.toMK k * (1 - Pp A) :=
    GlobalTheory.RealIwasawa.proj_comm (W := Wm A)
      (by rw [conjTranspose_sub, conjTranspose_one, Pp_conj hA])
      (fun y => mem_Wm.2 (by
        rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, Pp_idem hA, sub_self, Matrix.zero_mulVec]))
      (fun y hy => by rw [Matrix.sub_mulVec, Matrix.one_mulVec, mem_Wm.1 hy, sub_zero]) s3 s4
  refine ⟨c1.symm, ?_⟩
  have c3 : Pp A * S7.toMK k = S7.toMK k * Pp A := by
    have := c2
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one] at this
    exact (sub_right_injective this)
  rw [Pz_eq]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, c1, c3]

theorem tau_right_inv (hA : IsGrad ε A) (x y : PSub ε A) (k : S7.KG ε)
    (h : S7.toM (y : S7.UJ ε) = S7.toM (x : S7.UJ ε) * S7.toMK k) :
    tauG A (S7.toM (y : S7.UJ ε)) = tauG A (S7.toM (x : S7.UJ ε)) := by
  have e : (y : S7.UJ ε) = (x : S7.UJ ε) * (k : S7.UJ ε) := Subtype.ext (Units.ext h)
  have hk : (k : S7.UJ ε) ∈ PSub ε A := by
    have : (k : S7.UJ ε) = (x : S7.UJ ε)⁻¹ * (y : S7.UJ ε) := by rw [e]; group
    rw [this]
    exact (PSub ε A).mul_mem ((PSub ε A).inv_mem x.2) y.2
  obtain ⟨c1, c2⟩ := comm_of_mem hA k hk
  unfold tauG
  rw [h, Matrix.mul_assoc, Matrix.mul_assoc, c1, c2, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hs_mul_unitary _ _ (toMK_unitary k), hs_mul_unitary _ _ (toMK_unitary k)]

theorem line_mem (hA : IsGrad ε A) (x : PSub ε A) (t : ℝ) :
    ∃ y : PSub ε A, S7.toM (y : S7.UJ ε) = S7.toM (x : S7.UJ ε) * aT A t := by
  have h1N : (1 : Formalism.REAL.UJ ε) ∈ GlobalTheory.FlagMeas.flagN ε (CompanionTheory.RgExh.Dec.N.S.W A) := by
    refine ⟨fun i y _ => ?_, fun y _ => ?_⟩ <;>
      · rw [GlobalTheory.FlagLeviGroup.uMat_one, Matrix.one_mulVec, sub_self]
        exact Submodule.zero_mem _
  let a : Formalism.REAL.UJ ε := GlobalTheory.CompanionTheory.GradLine.aLine hA t
  have ha0 : a ∈ PSub ε A := (psubEq n ε A hA a).2 ⟨1, h1N, a, GlobalTheory.CompanionTheory.GradLine.aLine_mem hA t, (one_mul _).symm⟩
  let a' : S7.UJ ε := a
  have ha : a' ∈ PSub ε A := ha0
  have hm : S7.toM a' = aT A t := rfl
  refine ⟨⟨(x : S7.UJ ε) * a', (PSub ε A).mul_mem x.2 ha⟩, ?_⟩
  show S7.toM (x : S7.UJ ε) * S7.toM a' = _
  rw [hm]

theorem hs_lines (hA : IsGrad ε A) (x : S7.UJ ε) (t : ℝ) (h0 : 0 ≤ tauG A (S7.toM x)) (ht : 0 ≤ t) :
    (3 : ℝ)⁻¹ * Real.exp (2 * t) * hs (S7.toM x) ≤ hs (S7.toM x * aT A t) ∧
      hs (S7.toM x * aT A t) ≤ Real.exp (2 * t) * hs (S7.toM x) := by
  have e1 := hs_three hA (S7.toM x * aT A t)
  rw [hs_line_Pm hA, hs_line_Pz hA, hs_line_Pp hA] at e1
  have e2 := hs_three hA (S7.toM x)
  have hprod : hs (S7.toM x * Pm A) * (1 + hs (S7.toM x * Pz A)) ≤ 1 := by
    rw [← exp_tau hA x]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hac : 1 ≤ hs (S7.toM x * Pm A) * hs (S7.toM x * Pp A) := by
    have h1 := one_le_hs (Pp_idem hA) (Pp_ne_zero hA)
    have h2 := hs_mul_le (Pp A * S7.toM x⁻¹) (S7.toM x * Pp A)
    have h3 : S7.toM x⁻¹ * S7.toM x = 1 := by
      show ((x⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val * ((x : (Matrix (Fin n) (Fin n) ℂ)ˣ)).val = 1
      simp
    have h4 : Pp A * S7.toM x⁻¹ * (S7.toM x * Pp A) = Pp A := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (S7.toM x⁻¹), h3, Matrix.one_mul, Pp_idem hA]
    rw [h4, hs_Pp_inv hA] at h2
    linarith
  set a := hs (S7.toM x * Pm A)
  set b := hs (S7.toM x * Pz A)
  set c := hs (S7.toM x * Pp A)
  have ha : 0 ≤ a := hs_nonneg _
  have hb : 0 ≤ b := hs_nonneg _
  have hc : 0 ≤ c := hs_nonneg _
  have ha1 : a ≤ 1 := by nlinarith
  have hab : a * b ≤ 1 := by nlinarith
  have hc1 : 1 ≤ c := by nlinarith
  have hbc : b ≤ c := by nlinarith [mul_le_mul_of_nonneg_right hab hc, mul_le_mul_of_nonneg_left hac hb]
  have hE : Real.exp t ^ 2 = Real.exp (2 * t) := by rw [← Real.exp_nat_mul]; norm_num
  have hE' : Real.exp (-t) ^ 2 ≤ Real.exp (2 * t) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by push_cast; linarith)
  have hE1 : 1 ≤ Real.exp (2 * t) := Real.one_le_exp (by linarith)
  have hE0 : 0 ≤ Real.exp (-t) ^ 2 := by positivity
  rw [e1, e2, hE]
  constructor
  · nlinarith [mul_nonneg hE0 ha]
  · nlinarith [mul_le_mul_of_nonneg_right hE' ha]

theorem Pm_A (hA : IsGrad ε A) : Pm A * A = -Pm A := by
  have := congrArg conjTranspose (A_Pm hA)
  rwa [conjTranspose_mul, hA.2.1, Pm_conj hA, conjTranspose_neg, Pm_conj hA] at this

theorem Pp_A (hA : IsGrad ε A) : Pp A * A = Pp A := by
  have := congrArg conjTranspose (A_Pp hA)
  rwa [conjTranspose_mul, hA.2.1, Pp_conj hA] at this

theorem Pz_A (hA : IsGrad ε A) : Pz A * A = 0 := by
  have := congrArg conjTranspose (A_Pz hA)
  rwa [conjTranspose_mul, hA.2.1, Pz_conj hA, conjTranspose_zero] at this

theorem block_zero {P Q Z : Matrix (Fin n) (Fin n) ℂ} {a b c : ℂ} (hP : P * A = a • P) (hQ : A * Q = b • Q)
    (hZ : A * Z - Z * A = c • Z) (hne : a - b - c ≠ 0) : P * Z * Q = 0 := by
  have h := congrArg (fun M => P * M * Q) hZ
  simp only [Matrix.mul_sub, Matrix.sub_mul] at h
  have e1 : P * (A * Z) * Q = a • (P * Z * Q) := by
    rw [← Matrix.mul_assoc, hP, Matrix.smul_mul, Matrix.smul_mul]
  have e2 : P * (Z * A) * Q = b • (P * Z * Q) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hQ, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_assoc]
  have e3 : P * c • Z * Q = c • (P * Z * Q) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, e2, e3, ← sub_smul] at h
  have h' : (a - b - c) • (P * Z * Q) = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.1 h').resolve_left hne

theorem nil_blocks (hA : IsGrad ε A) {Z : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hc : c = -1 ∨ c = -2)
    (hZ : A * Z - Z * A = c • Z) :
    Pm A * Z * Pm A = 0 ∧ Pz A * Z * Pz A = 0 ∧ Pp A * Z * Pp A = 0 ∧ Pz A * Z * Pm A = 0 ∧ Pp A * Z * Pz A = 0 ∧
      Pp A * Z * Pm A = 0 := by
  have m1 : Pm A * A = (-1 : ℂ) • Pm A := by rw [Pm_A hA]; simp
  have m2 : A * Pm A = (-1 : ℂ) • Pm A := by rw [A_Pm hA]; simp
  have z1 : Pz A * A = (0 : ℂ) • Pz A := by rw [Pz_A hA]; simp
  have z2 : A * Pz A = (0 : ℂ) • Pz A := by rw [A_Pz hA]; simp
  have p1 : Pp A * A = (1 : ℂ) • Pp A := by rw [Pp_A hA]; simp
  have p2 : A * Pp A = (1 : ℂ) • Pp A := by rw [A_Pp hA]; simp
  rcases hc with rfl | rfl
  · exact ⟨block_zero m1 m2 hZ (by norm_num), block_zero z1 z2 hZ (by norm_num), block_zero p1 p2 hZ (by norm_num),
      block_zero z1 m2 hZ (by norm_num), block_zero p1 z2 hZ (by norm_num), block_zero p1 m2 hZ (by norm_num)⟩
  · exact ⟨block_zero m1 m2 hZ (by norm_num), block_zero z1 z2 hZ (by norm_num), block_zero p1 p2 hZ (by norm_num),
      block_zero z1 m2 hZ (by norm_num), block_zero p1 z2 hZ (by norm_num), block_zero p1 m2 hZ (by norm_num)⟩

theorem nilp_decomp (hA : IsGrad ε A) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ nilpC A) :
    Y = Pm A * Y * Pp A + Pz A * Y * Pp A + Pm A * Y * Pz A := by
  obtain ⟨Y₁, Y₂, rfl, h1, h2⟩ := hY
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := nil_blocks hA (c := -1) (Or.inl rfl) (Z := Y₁) (by rw [h1]; simp)
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := nil_blocks hA (c := -2) (Or.inr rfl) (Z := Y₂) (by rw [h2]; simp)
  set Y := Y₁ + Y₂ with hYd
  have c1 : Pm A * Y * Pm A = 0 := by simp only [hYd, Matrix.mul_add, Matrix.add_mul, a1, b1, add_zero]
  have c2 : Pz A * Y * Pz A = 0 := by simp only [hYd, Matrix.mul_add, Matrix.add_mul, a2, b2, add_zero]
  have c3 : Pp A * Y * Pp A = 0 := by simp only [hYd, Matrix.mul_add, Matrix.add_mul, a3, b3, add_zero]
  have c4 : Pz A * Y * Pm A = 0 := by simp only [hYd, Matrix.mul_add, Matrix.add_mul, a4, b4, add_zero]
  have c5 : Pp A * Y * Pz A = 0 := by simp only [hYd, Matrix.mul_add, Matrix.add_mul, a5, b5, add_zero]
  have c6 : Pp A * Y * Pm A = 0 := by simp only [hYd, Matrix.mul_add, Matrix.add_mul, a6, b6, add_zero]
  calc Y = (Pm A + Pz A + Pp A) * Y * (Pm A + Pz A + Pp A) := by rw [sum_proj, Matrix.one_mul, Matrix.mul_one]
    _ = Pm A * Y * Pp A + Pz A * Y * Pp A + Pm A * Y * Pz A := by
      simp only [Matrix.mul_add, Matrix.add_mul, c1, c2, c3, c4, c5, c6, add_zero, zero_add]
      abel

theorem hilbert_schmidt_triple_mul_le (U V W : Matrix (Fin n) (Fin n) ℂ) : hs (U * V * W) ≤ hs U * hs V * hs W :=
  (hs_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hs_mul_le _ _) (hs_nonneg _))

theorem contraction (hA : IsGrad ε A) (x : S7.UJ ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ nilpC A)
    (h0 : 0 ≤ tauG A (S7.toM x)) :
    hs (S7.toM x * Y * (S7.toM x)⁻¹) ≤ 6 * Real.exp (-2 * tauG A (S7.toM x)) * hs Y := by
  have hprod : hs (S7.toM x * Pm A) * (1 + hs (S7.toM x * Pz A)) ≤ 1 := by
    rw [← exp_tau hA x]
    exact Real.exp_le_one_iff.2 (by linarith)
  rw [exp_tau hA x, toM_inv_eq]
  have e : S7.toM x * Y * S7.toM x⁻¹ = (S7.toM x * Pm A) * Y * (Pp A * S7.toM x⁻¹) +
      (S7.toM x * Pz A) * Y * (Pp A * S7.toM x⁻¹) + (S7.toM x * Pm A) * Y * (Pz A * S7.toM x⁻¹) := by
    conv_lhs => rw [nilp_decomp hA hY]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have u1 := hilbert_schmidt_triple_mul_le (S7.toM x * Pm A) Y (Pp A * S7.toM x⁻¹)
  have u2 := hilbert_schmidt_triple_mul_le (S7.toM x * Pz A) Y (Pp A * S7.toM x⁻¹)
  have u3 := hilbert_schmidt_triple_mul_le (S7.toM x * Pm A) Y (Pz A * S7.toM x⁻¹)
  rw [hs_Pp_inv hA] at u1 u2
  rw [hs_Pz_inv hA] at u3
  have v1 := hs_add_le ((S7.toM x * Pm A) * Y * (Pp A * S7.toM x⁻¹) + (S7.toM x * Pz A) * Y * (Pp A * S7.toM x⁻¹))
    ((S7.toM x * Pm A) * Y * (Pz A * S7.toM x⁻¹))
  have v2 := hs_add_le ((S7.toM x * Pm A) * Y * (Pp A * S7.toM x⁻¹)) ((S7.toM x * Pz A) * Y * (Pp A * S7.toM x⁻¹))
  rw [e]
  set a := hs (S7.toM x * Pm A)
  set b := hs (S7.toM x * Pz A)
  have ha : 0 ≤ a := hs_nonneg _
  have hb : 0 ≤ b := hs_nonneg _
  have hy : 0 ≤ hs Y := hs_nonneg _
  have ha1 : a ≤ 1 := by nlinarith
  have k1 : a * a ≤ a * (1 + b) := by nlinarith
  have k2 : 4 * (a * a) + 6 * (a * b) ≤ 6 * (a * (1 + b)) := by nlinarith
  have k3 := mul_le_mul_of_nonneg_right k2 hy
  nlinarith

theorem gap (g : S7.UJ ε) (hn : (n : ℝ) < hs (S7.toM g)) :
    ∃ (A' : Matrix (Fin n) (Fin n) ℂ) (α β : ℝ), IsGrad ε A' ∧ 1 ≤ β ∧ β ≤ α ∧
      Real.log (hs (S7.toM g) / n) / (n + 1) ≤ Real.log α - Real.log β ∧
      ∀ y : Fin n → ℂ, α * nsq (Pm A' *ᵥ y) + β⁻¹ * nsq (Pz A' *ᵥ y) ≤ nsq (S7.toM g⁻¹ *ᵥ y) := by
  have hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self _
  obtain ⟨hpos, hsum⟩ := GlobalTheory.T.inverse_gram_eigenvalues_sum_hs n ε g hT
  set lam := hT.eigenvalues with hlam
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp [Formalism.REAL.hs] at hn
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  haveI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  set h := hs (S7.toM g) with hh
  have hq : 1 < h / n := (one_lt_div hnR).2 hn
  obtain ⟨i₁, hi₁⟩ : ∃ i, h / n ≤ lam i := by
    by_contra hc
    push_neg at hc
    have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i (_ : i ∈ Finset.univ) => hc i
    rw [hsum] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    rw [mul_div_cancel₀ _ hnR.ne'] at this
    exact lt_irrefl _ this
  let l : Fin n → ℝ := fun i => |Real.log (lam i)|
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ l Finset.univ_nonempty
  set L := l i₀ with hL
  have hLlog : Real.log (h / n) ≤ L := by
    calc Real.log (h / n) ≤ Real.log (lam i₁) := Real.log_le_log (by linarith) hi₁
      _ ≤ l i₁ := le_abs_self _
      _ ≤ L := hmax _ (Finset.mem_univ _)
  have hLpos : 0 < L := lt_of_lt_of_le (Real.log_pos hq) hLlog
  obtain ⟨r, hr, hgap⟩ := GlobalTheory.T.exists_gap_interval_avoiding_finite_family n l L hLpos (fun i => ⟨abs_nonneg _, hmax i (Finset.mem_univ _)⟩) ⟨i₀, rfl⟩
  set w := L / ((n : ℝ) + 1) with hw
  have hwpos : 0 < w := div_pos hLpos (by positivity)
  have hLw : L = ((n : ℝ) + 1) * w := by rw [hw]; field_simp
  set α := Real.exp (((r : ℝ) + 1) * w) with hα
  set β := Real.exp ((r : ℝ) * w) with hβ
  have hα1 : 1 < α := Real.one_lt_exp_iff.2 (by positivity)
  have hβ1 : 1 ≤ β := Real.one_le_exp (by positivity)
  have hβα : β ≤ α := Real.exp_le_exp.2 (by nlinarith)
  have hαi : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα1
  let f : ℝ → ℝ := fun s => if α ≤ s then -1 else if s ≤ α⁻¹ then 1 else 0
  have hf : ∀ s : ℝ, 0 < s → (f s = -1 ∨ f s = 0 ∨ f s = 1) ∧ f s⁻¹ = - f s := by
    intro s hsp
    have hsi : 0 < s⁻¹ := inv_pos.2 hsp
    have hαp : 0 < α := by linarith
    by_cases h1 : α ≤ s
    · have h2 : s⁻¹ ≤ α⁻¹ := inv_anti₀ hαp h1
      have h3 : ¬ α ≤ s⁻¹ := by intro h; linarith
      simp [f, h1, h2, h3]
    · by_cases h2 : s ≤ α⁻¹
      · have h3 : α ≤ s⁻¹ := by
          have := inv_anti₀ hsp h2
          rwa [inv_inv] at this
        simp [f, h1, h2, h3]
      · push_neg at h1 h2
        have h3 : ¬ α ≤ s⁻¹ := by
          intro h
          have := inv_anti₀ hαp h
          rw [inv_inv] at this
          linarith
        have h4 : ¬ s⁻¹ ≤ α⁻¹ := by
          intro h
          have := inv_anti₀ hsi h
          rw [inv_inv, inv_inv] at this
          linarith
        simp [f, not_le.2 h1, not_le.2 h2, h3, h4]
  have hzero : ∀ i, f (lam i) = 0 → l i < ((r : ℝ) + 1) * w := by
    intro i hi
    have h1 : ¬ α ≤ lam i := by
      intro h
      simp [f, h] at hi
    have h2 : ¬ lam i ≤ α⁻¹ := by
      intro h
      simp [f, h1, h] at hi
    push_neg at h1 h2
    have e1 : Real.log (lam i) < ((r : ℝ) + 1) * w := by
      have := (Real.log_lt_log_iff (hpos i) (by linarith)).2 h1
      rwa [hα, Real.log_exp] at this
    have e2 : -(((r : ℝ) + 1) * w) < Real.log (lam i) := by
      have := (Real.log_lt_log_iff (by positivity) (hpos i)).2 h2
      rwa [hα, Real.log_inv, Real.log_exp] at this
    exact abs_lt.2 ⟨e2, e1⟩
  have hneg : ∀ s, f s = -1 → α ≤ s := by
    intro s hi
    by_contra hc
    by_cases h2 : s ≤ α⁻¹
    · simp only [f, if_neg hc, if_pos h2] at hi
      norm_num at hi
    · simp only [f, if_neg hc, if_neg h2] at hi
      norm_num at hi
  obtain ⟨A', hA', hy⟩ := GlobalTheory.T.exists_graded_matrix_eigen_bound n ε g hT f α β hf
    (fun i hi => hneg _ hi)
    (fun i hi => by
      have h1 := hzero i hi
      have h2 : l i < (r : ℝ) * w := by
        rcases hgap i with h | h
        · exact h
        · linarith
      have h3 : -((r : ℝ) * w) < Real.log (lam i) := (abs_lt.1 h2).1
      have h4 : β⁻¹ = Real.exp (-((r : ℝ) * w)) := by rw [hβ, Real.exp_neg]
      rw [h4]
      calc Real.exp (-((r : ℝ) * w)) ≤ Real.exp (Real.log (lam i)) := Real.exp_le_exp.2 h3.le
        _ = lam i := Real.exp_log (hpos i))
    ⟨i₀, fun hi => by
      have h1 := hzero i₀ hi
      have h2 : ((r : ℝ) + 1) ≤ n := by exact_mod_cast hr
      have h3 : L < ((r : ℝ) + 1) * w := h1
      nlinarith⟩
  refine ⟨A', α, β, hA', hβ1, hβα, ?_, hy⟩
  rw [hα, hβ, Real.log_exp, Real.log_exp]
  have : Real.log (h / n) / ((n : ℝ) + 1) ≤ w := div_le_div_of_nonneg_right hLlog (by positivity)
  linarith

theorem cover (n : ℕ) (ε : Fin n → Bool) :
    ∃ (m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (c₁ R₀ : ℝ), 0 < c₁ ∧ (∀ j, IsGrad ε (A j)) ∧
      ∀ g : S7.UJ ε, R₀ < hs (S7.toM g) → ∃ (j : Fin m) (x : PSub ε (A j)) (k : S7.KG ε),
        g = (x : S7.UJ ε) * (k : S7.UJ ε) ∧
        c₁ * Real.log (hs (S7.toM (x : S7.UJ ε))) ≤ tauG (A j) (S7.toM (x : S7.UJ ε)) := by
  obtain ⟨m, A, hA, hnet⟩ := GlobalTheory.T.finite_net_of_graded_projections n ε
  set large₂ := Real.log (20 * (n : ℝ) ^ 2) with hLg
  set E := 2 * ((n : ℝ) + 1) * large₂ + 2 * Real.log n with hE
  refine ⟨m, A, 1 / (4 * ((n : ℝ) + 1)), n + Real.exp E, by positivity, hA, fun g hg => ?_⟩
  have hexp := Real.exp_pos E
  have hn1 : (n : ℝ) < hs (S7.toM g) := by linarith
  obtain ⟨A', α, β, hA', hβ1, hβα, hlog, hy⟩ := gap g hn1
  obtain ⟨j, h1, h2⟩ := hnet A' hA'
  obtain ⟨x, k, hxk⟩ := GlobalTheory.T.iwasawa_parabolic_compact_factorization n ε (A j) (hA j) g
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp [Formalism.REAL.hs] at hn1
    · exact h
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  subst hxk
  obtain ⟨ea, eb⟩ := GlobalTheory.T.hilbert_schmidt_projection_bound n ε (A j) A' α β x k (hA j) hA' h1 h2 hβ1 hβα hy
  have hs_eq : hs (S7.toM ((x : S7.UJ ε) * (k : S7.UJ ε))) = hs (S7.toM (x : S7.UJ ε)) :=
    hs_mul_unitary _ _ (toMK_unitary k)
  rw [hs_eq] at hlog hg hn1
  refine ⟨j, x, k, rfl, ?_⟩
  set h := hs (S7.toM (x : S7.UJ ε)) with hh
  set a := hs (S7.toM (x : S7.UJ ε) * Pm (A j)) with ha
  set b := hs (S7.toM (x : S7.UJ ε) * Pz (A j)) with hb
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have hapos : 0 < a := hs_Pm_pos (hA j) _
  have hb0 : 0 ≤ b := hs_nonneg _
  have hP : a * (1 + b) ≤ 20 * (n : ℝ) ^ 2 * (β / α) := by
    have t1 : 1 + b ≤ 5 * n * β := by nlinarith [mul_le_mul hnR hβ1 zero_le_one (by linarith : (0 : ℝ) ≤ n)]
    calc a * (1 + b) ≤ (4 * n / α) * (5 * n * β) :=
          mul_le_mul ea t1 (by linarith) (by positivity)
      _ = 20 * (n : ℝ) ^ 2 * (β / α) := by field_simp; ring
  have hlogP : Real.log (a * (1 + b)) ≤ large₂ + Real.log β - Real.log α := by
    have hpos : 0 < a * (1 + b) := by positivity
    have := Real.log_le_log hpos hP
    have hn2 : (0 : ℝ) < n := by linarith
    have e : Real.log (20 * (n : ℝ) ^ 2 * (β / α)) = large₂ + Real.log β - Real.log α := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_div hβ0.ne' hα0.ne', hLg]
      ring
    rw [e] at this
    exact this
  have hhpos : 0 < h := by linarith
  have hlogh : E < Real.log h := by
    have : Real.exp E < h := by linarith
    exact (Real.lt_log_iff_exp_lt hhpos).2 this
  have hdiv : Real.log (h / n) = Real.log h - Real.log n := Real.log_div hhpos.ne' (by linarith)
  rw [hdiv] at hlog
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have s1 : (Real.log h - Real.log n) / ((n : ℝ) + 1) ≤ large₂ - Real.log (a * (1 + b)) := by linarith
  have s2 : Real.log h - Real.log n ≤ (large₂ - Real.log (a * (1 + b))) * ((n : ℝ) + 1) := (div_le_iff₀ hN).1 s1
  rw [hE] at hlogh
  have s3 : Real.log h ≤ -2 * ((n : ℝ) + 1) * Real.log (a * (1 + b)) := by nlinarith
  show 1 / (4 * ((n : ℝ) + 1)) * Real.log h ≤ -(1 / 2) * Real.log (a * (1 + b))
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

theorem geo : Geo := by
  intro n ε
  obtain ⟨m, A, c₁, R₀, hc, hA, hcov⟩ := cover n ε
  refine ⟨m, A, fun j x => tauG (A j) (S7.toM x), c₁, R₀, 6, hc, hA, fun j => tau_continuous (hA j),
    fun j x y k h => tau_right_inv (hA j) x y k h, fun j x t => line_mem (hA j) x t, ?_, ?_, ?_, ?_⟩
  · intro j x t y h
    show tauG (A j) (S7.toM (y : S7.UJ ε)) = tauG (A j) (S7.toM (x : S7.UJ ε)) + t
    rw [h, tau_add (hA j)]
  · let E : Fin m → Set (S7.UJ ε) := fun j => {x | x ∈ PSub ε (A j) ∧
      c₁ * Real.log (hs (S7.toM x)) ≤ tauG (A j) (S7.toM x)}
    refine ⟨fun j => E j * ((S7.KG ε : Subgroup (S7.UJ ε)) : Set (S7.UJ ε)), fun j => ?_, ?_, ?_, ?_⟩
    · have hcl : IsClosed (E j) := by
        refine (GlobalTheory.CompanionTheory.ParabolicHaar.isClosed_pSub ε (A j)).inter (isClosed_le ?_ (tau_continuous (hA j)))
        refine continuous_const.mul (Continuous.log (continuous_hs.comp (S7.continuous_toM ε)) fun x => ?_)
        have hx : S7.toM x * Pm (A j) ≠ 0 := toM_mul_ne_zero x (Pm_ne_zero (hA j))
        intro h0
        exact hx (by rw [hs_eq_zero h0, Matrix.zero_mul])
      exact (hcl.mul_right_of_isCompact (GlobalTheory.T.unitary_maximal_compact_is_compact n ε)).measurableSet
    · rintro j g k ⟨x, hx, k', hk', rfl⟩
      exact ⟨x, hx, k' * k, (S7.KG ε).mul_mem hk' k.2, by simp [mul_assoc]⟩
    · intro g hg
      obtain ⟨j, x, k, rfl, hx⟩ := hcov g hg
      exact ⟨j, x, ⟨x.2, hx⟩, k, k.2, rfl⟩
    · rintro j x ⟨x', ⟨hx'P, hx'⟩, k, hk, e⟩
      let k' : S7.KG ε := ⟨k, hk⟩
      have h1 : S7.toM (x : S7.UJ ε) = S7.toM x' * S7.toMK k' := by rw [← e]; rfl
      have h2 := tau_right_inv (hA j) ⟨x', hx'P⟩ x k' h1
      have h3 : hs (S7.toM (x : S7.UJ ε)) = hs (S7.toM x') := by
        rw [h1]; exact hs_mul_unitary _ _ (toMK_unitary k')
      show c₁ * Real.log (hs (S7.toM (x : S7.UJ ε))) ≤ tauG (A j) (S7.toM (x : S7.UJ ε))
      rw [h2, h3]
      exact hx'
  · intro j x t h0 ht
    obtain ⟨u1, u2⟩ := hs_lines (hA j) (x : S7.UJ ε) t h0 ht
    have hx0 := hs_nonneg (S7.toM (x : S7.UJ ε))
    have hexp := (Real.exp_pos (2 * t)).le
    constructor
    · refine le_trans ?_ u1
      have : (6 : ℝ)⁻¹ * Real.exp (2 * t) ≤ (3 : ℝ)⁻¹ * Real.exp (2 * t) := by nlinarith
      exact mul_le_mul_of_nonneg_right this hx0
    · refine u2.trans ?_
      exact mul_le_mul_of_nonneg_right (by nlinarith) hx0
  · intro j x Y hY h0
    exact contraction (hA j) (x : S7.UJ ε) hY h0

end GlobalTheory.CompanionTheory.UGeo
