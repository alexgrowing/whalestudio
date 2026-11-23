import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorActionHermitianExpFixedOfMinNorm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixKroneckerPowerTensorActionAlgebra
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorPowerSumRightActionNormAndContinuity
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma posDef_det_one_eq_unitary_conj_exp_diagonal {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (hP : P.PosDef) (hdet : P.det = 1) :
    ∃ (U : Matrix ι ι ℂ) (δ : ι → ℝ), U * Uᴴ = 1 ∧ ∑ i, δ i = 0 ∧
      P = (U * diagonal fun i => ((Real.exp (2 * δ i) : ℝ) : ℂ)) * Uᴴ := by
  refine ⟨(hP.1.eigenvectorUnitary : Matrix ι ι ℂ), fun i => Real.log (hP.1.eigenvalues i) / 2,
    ?_, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem hP.1.eigenvectorUnitary.2
  · have h := hP.1.det_eq_prod_eigenvalues
    rw [hdet] at h
    have hprod' : ((∏ i, hP.1.eigenvalues i : ℝ) : ℂ) = 1 := by push_cast; exact h.symm
    have hprod : ∏ i, hP.1.eigenvalues i = 1 := by exact_mod_cast hprod'
    rw [← Finset.sum_div, ← Real.log_prod (fun i _ => (hP.eigenvalues_pos i).ne'), hprod,
      Real.log_one, zero_div]
  · conv_lhs => rw [hP.1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    congr 3
    funext i
    simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id]
    rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log (hP.eigenvalues_pos i)]
    rfl

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma unitary_conj_exp_diagonal_conjTranspose {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (δ : ι → ℝ) (s : ℝ) :
    ((U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ)ᴴ =
      (U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ := by
  simp [conjTranspose_mul, Matrix.mul_assoc, diagonal_conjTranspose, -Complex.ofReal_exp, Pi.star_def]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma unitary_conj_exp_diagonal_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) (δ : ι → ℝ) (s t : ℝ) :
    ((U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ) *
        ((U * diagonal fun i => ((Real.exp (t * δ i) : ℝ) : ℂ)) * Uᴴ) =
      (U * diagonal fun i => ((Real.exp ((s + t) * δ i) : ℝ) : ℂ)) * Uᴴ := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _),
    diagonal_mul_diagonal]
  simp only [← Complex.ofReal_mul, ← Real.exp_add, ← add_mul]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma exists_unitary_exp_diagonal_fixing_of_nsq_eq {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (d : Fin m → ℕ) (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (hv : _root_.GlobalTheory.ClassFin.IsMinVec d v)
    (g : Matrix ι ι ℂ) (hg : g.det = 1)
    (hn : _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v g) = _root_.GlobalTheory.ClassFin.nsq v) :
    ∃ (U : Matrix ι ι ℂ) (δ : ι → ℝ), U * Uᴴ = 1 ∧ ∑ i, δ i = 0 ∧
      g * gᴴ = (U * diagonal fun i => ((Real.exp (2 * δ i) : ℝ) : ℂ)) * Uᴴ ∧
      ∀ s : ℝ, _root_.GlobalTheory.ClassFin.act d v
        ((U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ) = v := by
  have hdetP : (g * gᴴ).det = 1 := by simp [hg]
  have hP : (g * gᴴ).PosDef :=
    (posSemidef_self_mul_conjTranspose g).posDef_iff_isUnit.mpr
      ((isUnit_iff_isUnit_det _).mpr (by rw [hdetP]; exact isUnit_one))
  obtain ⟨U, δ, hU, hδ, hgP⟩ := posDef_det_one_eq_unitary_conj_exp_diagonal _ hP hdetP
  refine ⟨U, δ, hU, hδ, hgP, ?_⟩
  obtain ⟨-, hactmul, -⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v
  have hgu : IsUnit g.det := by rw [hg]; exact isUnit_one
  have hhh : ((U * diagonal fun i => ((Real.exp (1 * δ i) : ℝ) : ℂ)) * Uᴴ) *
      ((U * diagonal fun i => ((Real.exp (1 * δ i) : ℝ) : ℂ)) * Uᴴ)ᴴ = g * gᴴ := by
    rw [unitary_conj_exp_diagonal_conjTranspose, unitary_conj_exp_diagonal_mul hU, hgP]
    norm_num
  set h : Matrix ι ι ℂ := (U * diagonal fun i => ((Real.exp (1 * δ i) : ℝ) : ℂ)) * Uᴴ with hh
  have hk : (g⁻¹ * h) * (g⁻¹ * h)ᴴ = 1 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h, hhh, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hgu, Matrix.one_mul, conjTranspose_nonsing_inv,
      mul_nonsing_inv _ (by simp [hg])]
  have hgk : h = g * (g⁻¹ * h) := by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hgu, Matrix.one_mul]
  have hnh : _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v h) = _root_.GlobalTheory.ClassFin.nsq v := by
    rw [hgk, hactmul, (_root_.GlobalTheory.ClassFin.ActNorm.act_norm_continuity ι m d).1 _ _ hk, hn]
  rw [hh] at hnh
  exact _root_.GlobalTheory.ClassFin.act_exp_eq_of_isMinVec ι m d v U δ hv hU hδ (by simpa only [one_mul] using hnh)

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma map_conj_mul_conjTranspose_eq_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) : U.map (starRingEnd ℂ) * (U.map (starRingEnd ℂ))ᴴ = 1 := by
  have := congrArg (fun M : Matrix ι ι ℂ => M.map (starRingEnd ℂ)) hU
  simp only [Matrix.map_mul] at this
  convert this using 2
  · ext i j; simp
  · ext i j; by_cases h : i = j <;> simp [one_apply, h]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma unitary_conj_exp_diagonal_map_conj {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (δ : ι → ℝ) (s : ℝ) :
    ((U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ).map (starRingEnd ℂ) =
      (U.map (starRingEnd ℂ) * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) *
        (U.map (starRingEnd ℂ))ᴴ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  by_cases h : i = j <;> simp [diagonal, h, -Complex.ofReal_exp]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma unitary_conj_exp_zero_diagonal_eq_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) (δ : ι → ℝ) :
    (U * diagonal fun i => ((Real.exp (0 * δ i) : ℝ) : ℂ)) * Uᴴ = 1 := by
  simp [hU]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma posSemidef_eq_of_mul_self_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef) (h : X * X = Y * Y) : X = Y := by
  have hX2 : (0 : Matrix ι ι ℂ) ≤ X * X := by
    rw [Matrix.nonneg_iff_posSemidef]
    have := Matrix.posSemidef_conjTranspose_mul_self X
    rwa [hX.1.eq] at this
  have hY2 : (0 : Matrix ι ι ℂ) ≤ Y * Y := h ▸ hX2
  have h1 := (CFC.sqrt_eq_iff (X * X) X hX2 hX.nonneg).mpr rfl
  have h2 := (CFC.sqrt_eq_iff (Y * Y) Y hY2 hY.nonneg).mpr rfl
  rw [← h1, ← h2, h]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma nsq_act_eq_of_gram_eq {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (d : Fin m → ℕ) (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (a b : Matrix ι ι ℂ) (ha : IsUnit a.det)
    (hab : b * bᴴ = a * aᴴ) :
    _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v b) =
      _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v a) := by
  obtain ⟨-, hactmul, -⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v
  have hk : (a⁻¹ * b) * (a⁻¹ * b)ᴴ = 1 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc b, hab, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, nonsing_inv_mul _ ha, Matrix.one_mul, conjTranspose_nonsing_inv,
      mul_nonsing_inv _ (by simpa [det_conjTranspose] using ha.star)]
  have hb : b = a * (a⁻¹ * b) := by rw [← Matrix.mul_assoc, mul_nonsing_inv _ ha, Matrix.one_mul]
  rw [hb, hactmul, (_root_.GlobalTheory.ClassFin.ActNorm.act_norm_continuity ι m d).1 _ _ hk]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in

theorem _root_.GlobalTheory.ClassFin.exists_real_translate_isMinVec : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (t : _root_.GlobalTheory.ClassFin.TIdx ι d → ℝ), (∃ w ∈ _root_.GlobalTheory.ClassFin.orb d (fun k => (t k : ℂ)), _root_.GlobalTheory.ClassFin.IsMinVec d w) → ∃ g : Matrix ι ι ℝ, g.det = 1 ∧ _root_.GlobalTheory.ClassFin.IsMinVec d (_root_.GlobalTheory.ClassFin.act d (fun k => (t k : ℂ)) (g.map (fun r : ℝ => (r : ℂ)))) := by
  intro ι _ _ m d t ⟨w, hwo, hw⟩
  obtain ⟨g₀, hg₀, rfl⟩ := hwo
  set tc : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ := fun k => (t k : ℂ) with htc
  obtain ⟨-, hactmul, -, -, -, hactmap⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d tc
  set w := _root_.GlobalTheory.ClassFin.act d tc g₀ with hwdef
  have hg₀u : IsUnit g₀.det := by rw [hg₀]; exact isUnit_one
  have hmapH : ∀ M : Matrix ι ι ℂ, Mᴴ.map (starRingEnd ℂ) = (M.map (starRingEnd ℂ))ᴴ :=
    fun M => by ext i j; simp
  have hmapmap : ∀ M : Matrix ι ι ℂ, (M.map (starRingEnd ℂ)).map (starRingEnd ℂ) = M :=
    fun M => by ext i j; simp
  obtain ⟨gb, hgb⟩ : ∃ x : Matrix ι ι ℂ, x = g₀.map (starRingEnd ℂ) := ⟨_, rfl⟩
  have hgbdet : gb.det = 1 := by
    have := RingHom.map_det (starRingEnd ℂ) g₀
    rw [hg₀, map_one] at this
    rw [hgb]
    exact this.symm
  have hact_gb : _root_.GlobalTheory.ClassFin.act d tc gb = fun k => starRingEnd ℂ (w k) := by
    have := hactmap ℂ (starRingEnd ℂ) g₀
    have htc' : (fun k => starRingEnd ℂ (tc k)) = tc := by funext k; simp [htc]
    rw [htc'] at this
    rw [hgb]
    exact this
  obtain ⟨c, hc⟩ : ∃ x : Matrix ι ι ℂ, x = g₀⁻¹ * gb := ⟨_, rfl⟩
  have hcdet : c.det = 1 := by simp [hc, hgbdet, hg₀]
  have hg₀c : g₀ * c = gb := by rw [hc, ← Matrix.mul_assoc, mul_nonsing_inv _ hg₀u, Matrix.one_mul]
  have hn : _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d w c) = _root_.GlobalTheory.ClassFin.nsq w := by
    rw [hwdef, ← hactmul, hg₀c, hact_gb]
    unfold _root_.GlobalTheory.ClassFin.nsq
    simp [hwdef]
  obtain ⟨U, δ, hU, hδ, hcQ, hfix⟩ := exists_unitary_exp_diagonal_fixing_of_nsq_eq d w hw c hcdet hn
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → Matrix ι ι ℂ,
      ∀ s, Q s = (U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ := ⟨_, fun _ => rfl⟩
  have hQmul : ∀ s s', Q s * Q s' = Q (s + s') := fun s s' => by
    rw [hQ, hQ, hQ]; exact unitary_conj_exp_diagonal_mul hU δ s s'
  have hQH : ∀ s, (Q s)ᴴ = Q s := fun s => by
    rw [hQ]; exact unitary_conj_exp_diagonal_conjTranspose U δ s
  have hcQ' : c * cᴴ = Q 2 := by rw [hQ]; exact hcQ
  have hfix' : ∀ s, _root_.GlobalTheory.ClassFin.act d w (Q s) = w := fun s => by rw [hQ]; exact hfix s
  have hUb1 : U.map (starRingEnd ℂ) * (U.map (starRingEnd ℂ))ᴴ = 1 := map_conj_mul_conjTranspose_eq_one hU
  obtain ⟨Qb, hQb⟩ : ∃ Qb : ℝ → Matrix ι ι ℂ, ∀ s, Qb s =
      (U.map (starRingEnd ℂ) * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) *
        (U.map (starRingEnd ℂ))ᴴ := ⟨_, fun _ => rfl⟩
  have hQbmap : ∀ s, (Q s).map (starRingEnd ℂ) = Qb s := fun s => by
    rw [hQ, hQb]; exact unitary_conj_exp_diagonal_map_conj U δ s
  have hQbmul : ∀ s s', Qb s * Qb s' = Qb (s + s') := fun s s' => by
    rw [hQb, hQb, hQb]; exact unitary_conj_exp_diagonal_mul hUb1 δ s s'
  have hQb0 : Qb 0 = 1 := by rw [hQb]; exact unitary_conj_exp_zero_diagonal_eq_one hUb1 δ
  have hQbH : ∀ s, (Qb s)ᴴ = Qb s := fun s => by
    rw [hQb]; exact unitary_conj_exp_diagonal_conjTranspose _ δ s
  have hgcb : gb * c.map (starRingEnd ℂ) = g₀ := by
    have := congrArg (fun M : Matrix ι ι ℂ => M.map (starRingEnd ℂ)) hg₀c
    simp only [Matrix.map_mul] at this
    rw [hgb, this, hgb, hmapmap]
  have hccb : c * c.map (starRingEnd ℂ) = 1 := by
    have h1 : g₀ * (c * c.map (starRingEnd ℂ)) = g₀ := by rw [← Matrix.mul_assoc, hg₀c, hgcb]
    have h2 : c * c.map (starRingEnd ℂ) = g₀⁻¹ * (g₀ * (c * c.map (starRingEnd ℂ))) := by
      rw [← Matrix.mul_assoc, nonsing_inv_mul _ hg₀u, Matrix.one_mul]
    rw [h2, h1, nonsing_inv_mul _ hg₀u]
  have hcbc : c.map (starRingEnd ℂ) * c = 1 := mul_eq_one_comm.mp hccb
  have hQb2 : c.map (starRingEnd ℂ) * (c.map (starRingEnd ℂ))ᴴ = Qb 2 := by
    rw [← hQbmap, ← hcQ', Matrix.map_mul, hmapH]
  have e : cᴴ * c * Qb 2 = 1 := by
    rw [← hQb2, Matrix.mul_assoc, ← Matrix.mul_assoc c, hccb, Matrix.one_mul, ← conjTranspose_mul,
      hcbc, conjTranspose_one]
  have hcHc : cᴴ * c = Qb (-2) := by
    calc cᴴ * c = cᴴ * c * (Qb 2 * Qb (-2)) := by
          rw [hQbmul, show (2 : ℝ) + -2 = 0 by norm_num, hQb0, Matrix.mul_one]
      _ = Qb (-2) := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]
  have hZZ : (c * Qb 1 * cᴴ) * (c * Qb 1 * cᴴ) = Q 1 * Q 1 := by
    calc (c * Qb 1 * cᴴ) * (c * Qb 1 * cᴴ) = c * (Qb 1 * (cᴴ * c) * Qb 1) * cᴴ := by
          simp only [Matrix.mul_assoc]
      _ = Q 1 * Q 1 := by
          rw [hcHc, hQbmul, hQbmul, show (1 : ℝ) + -2 + 1 = 0 by norm_num, hQb0, Matrix.mul_one,
            hQmul, hcQ']
          norm_num
  have hZpsd : (c * Qb 1 * cᴴ).PosSemidef := by
    have : c * Qb 1 * cᴴ = (c * Qb (1 / 2)) * (c * Qb (1 / 2))ᴴ := by
      rw [conjTranspose_mul, hQbH]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Qb (1 / 2)) (Qb (1 / 2)), hQbmul]
      norm_num
    rw [this]
    exact posSemidef_self_mul_conjTranspose _
  have hQ1psd : (Q 1).PosSemidef := by
    have : Q 1 = Q (1 / 2) * (Q (1 / 2))ᴴ := by rw [hQH, hQmul]; norm_num
    rw [this]
    exact posSemidef_self_mul_conjTranspose _
  have hZQ : c * Qb 1 * cᴴ = Q 1 := posSemidef_eq_of_mul_self_eq _ _ hZpsd hQ1psd hZZ
  have hPreal : (g₀ * Q 1 * g₀ᴴ).map (starRingEnd ℂ) = g₀ * Q 1 * g₀ᴴ := by
    calc (g₀ * Q 1 * g₀ᴴ).map (starRingEnd ℂ) = gb * Qb 1 * gbᴴ := by
          rw [Matrix.map_mul, Matrix.map_mul, hQbmap, hmapH, hgb]
      _ = g₀ * (c * Qb 1 * cᴴ) * g₀ᴴ := by
          rw [← hg₀c, conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = g₀ * Q 1 * g₀ᴴ := by rw [hZQ]
  have hdetQ : ∀ s, (Q s).det = 1 := fun s => by
    rw [hQ, det_mul, det_mul, det_diagonal]
    have hUd : U.det * Uᴴ.det = 1 := by rw [← det_mul, hU, det_one]
    have hD : ∏ i, ((Real.exp (s * δ i) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum, hδ, mul_zero, Real.exp_zero,
        Complex.ofReal_one]
    rw [hD]
    linear_combination hUd
  obtain ⟨h, hh⟩ : ∃ x : Matrix ι ι ℂ, x = g₀ * Q (1 / 2) := ⟨_, rfl⟩
  have hP_h : h * hᴴ = g₀ * Q 1 * g₀ᴴ := by
    rw [hh, conjTranspose_mul, hQH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Q (1 / 2)) (Q (1 / 2)), hQmul]
    norm_num
  have hhdet : h.det = 1 := by rw [hh, det_mul, hg₀, hdetQ, one_mul]
  have hPdet : (g₀ * Q 1 * g₀ᴴ).det = 1 := by
    rw [← hP_h, det_mul, det_conjTranspose, hhdet]
    simp
  have hacth : _root_.GlobalTheory.ClassFin.act d tc h = w := by rw [hh, hactmul, hfix']
  obtain ⟨R, hR⟩ : ∃ x : Matrix ι ι ℝ, x = (g₀ * Q 1 * g₀ᴴ).map Complex.re := ⟨_, rfl⟩
  have hRc : R.map (fun x : ℝ => (x : ℂ)) = g₀ * Q 1 * g₀ᴴ := by
    ext i j
    have := congrFun (congrFun hPreal i) j
    simp only [Matrix.map_apply] at this
    simpa [hR] using Complex.conj_eq_iff_re.mp this
  have hRAB : R = h.map Complex.re * (h.map Complex.re)ᴴ + h.map Complex.im * (h.map Complex.im)ᴴ := by
    rw [hR, ← hP_h]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply,
      star_trivial, Complex.re_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.mul_re] <;> ring
  have hRpsd : R.PosSemidef := by
    rw [hRAB]
    exact (posSemidef_self_mul_conjTranspose _).add (posSemidef_self_mul_conjTranspose _)
  have hr0 : (0 : Matrix ι ι ℝ) ≤ CFC.sqrt R := CFC.sqrt_nonneg R
  have hrr : CFC.sqrt R * CFC.sqrt R = R := CFC.sqrt_mul_sqrt_self R hRpsd.nonneg
  have hrpsd : (CFC.sqrt R).PosSemidef := Matrix.nonneg_iff_posSemidef.mp hr0
  have hRdet : R.det = 1 := by
    have e : (R.map (fun x : ℝ => (x : ℂ))).det = ((R.det : ℝ) : ℂ) :=
      (RingHom.map_det Complex.ofRealHom R).symm
    rw [hRc, hPdet] at e
    exact_mod_cast e.symm
  have hrdet : (CFC.sqrt R).det = 1 := by
    have h2 : (CFC.sqrt R).det * (CFC.sqrt R).det = 1 := by rw [← det_mul, hrr, hRdet]
    have h3 : 0 ≤ (CFC.sqrt R).det := hrpsd.det_nonneg
    nlinarith
  refine ⟨CFC.sqrt R, hrdet, ?_⟩
  set r := CFC.sqrt R with hrdef
  have hrcH : (r.map (fun x : ℝ => (x : ℂ)))ᴴ = r.map (fun x : ℝ => (x : ℂ)) := by
    ext i j
    have := hrpsd.1.apply i j
    simp only [star_trivial] at this
    simp [this]
  have hrcsq : (r * r).map (fun x : ℝ => (x : ℂ)) =
      r.map (fun x : ℝ => (x : ℂ)) * r.map (fun x : ℝ => (x : ℂ)) := by
    ext i j
    simp [Matrix.mul_apply]
  have hrcrc : r.map (fun x : ℝ => (x : ℂ)) * (r.map (fun x : ℝ => (x : ℂ)))ᴴ = h * hᴴ := by
    rw [hrcH, ← hrcsq, hrr, hRc, hP_h]
  have hrcdet : (r.map (fun x : ℝ => (x : ℂ))).det = 1 := by
    have e : (r.map (fun x : ℝ => (x : ℂ))).det = ((r.det : ℝ) : ℂ) :=
      (RingHom.map_det Complex.ofRealHom r).symm
    rw [e, hrdet, Complex.ofReal_one]
  have hnorm : _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d tc (r.map (fun x : ℝ => (x : ℂ)))) =
      _root_.GlobalTheory.ClassFin.nsq w := by
    rw [nsq_act_eq_of_gram_eq d tc h _ (by rw [hhdet]; exact isUnit_one) hrcrc, hacth]
  unfold _root_.GlobalTheory.ClassFin.IsMinVec at hw ⊢
  unfold _root_.GlobalTheory.ClassFin.orb at hw
  intro u hu
  obtain ⟨y, hy, rfl⟩ := hu
  rw [hnorm, ← hactmul]
  refine hw _ ⟨g₀⁻¹ * (r.map (fun x : ℝ => (x : ℂ)) * y), by simp [hg₀, hrcdet, hy], ?_⟩
  rw [hwdef, ← hactmul, ← Matrix.mul_assoc, mul_nonsing_inv _ hg₀u, Matrix.one_mul]

end GlobalTheory.ClassFin
