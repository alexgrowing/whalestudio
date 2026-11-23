import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.StatementG
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolutionStatement

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.UnitaryDoubleCoset

section Abstract

variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

theorem cT_pow (c : O →+* O) {B : Matrix n n O} (hB : cT c B = B) (m : ℕ) : cT c (B ^ m) = B ^ m := by
  induction m with
  | zero => simp [cT_one]
  | succ m ih => rw [pow_succ, cT_mul, ih, hB, ← pow_succ', pow_succ]

theorem cT_aeval (c : O →+* O) {B : Matrix n n O} (hB : cT c B = B) (p : Polynomial O) :
    cT c (Polynomial.aeval B p) = Polynomial.aeval B (p.map c) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, map_add, map_add, ← hp, ← hq]
    ext i j; simp [cT]
  | monomial m a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      ← Algebra.smul_def, ← Algebra.smul_def]
    conv_rhs => rw [← cT_pow c hB m]
    ext i j; simp [cT]

theorem aeval_intertwine (ι : O →+* L) {B B' : Matrix n n O} {g : Matrix n n L}
    (h : B.map ι * g = g * B'.map ι) (p : Polynomial O) :
    (Polynomial.aeval B p).map ι * g = g * (Polynomial.aeval B' p).map ι := by
  have hp : ∀ m : ℕ, (B ^ m).map ι * g = g * (B' ^ m).map ι := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_succ, Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih,
        Matrix.mul_assoc]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, Matrix.map_add _ (map_add ι), Matrix.map_add _ (map_add ι), Matrix.add_mul,
      Matrix.mul_add, hp, hq]
  | monomial m a =>
    have e : ∀ M : Matrix n n O, (a • M).map ι = ι a • M.map ι := fun M => by
      ext i j; simp
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, e, e,
      Matrix.smul_mul, Matrix.mul_smul, hp]

open IsDedekindDomain NumberField in
open scoped TensorProduct Matrix in
variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n] in
omit [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.UnitaryDoubleCoset.cT_map (ι : O →+* L) {c : O →+* O} {σ : L →+* L}
    (hι : ∀ x, σ (ι x) = ι (c x)) (M : Matrix n n O) :
    _root_.Formalism.UG.cT σ (M.map ι) = (_root_.Formalism.UG.cT c M).map ι := by
  ext i j
  simp [_root_.Formalism.UG.cT, hι]

open IsDedekindDomain NumberField in
open scoped TensorProduct Matrix in
variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n] in
omit [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.UnitaryDoubleCoset.cT_cT {c : O →+* O} (hc : ∀ x, c (c x) = x)
    (M : Matrix n n O) : _root_.Formalism.UG.cT c (_root_.Formalism.UG.cT c M) = M := by
  ext i j
  simp [_root_.Formalism.UG.cT, hc]

open IsDedekindDomain NumberField in
open scoped TensorProduct Matrix in
variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n] in
private theorem cT_aeval_eq_aeval_cT_map (c : O →+* O) (B : Matrix n n O) (q : Polynomial O) :
    _root_.Formalism.UG.cT c (Polynomial.aeval B q) = Polynomial.aeval (_root_.Formalism.UG.cT c B) (q.map c) := by
  induction q using Polynomial.induction_on with
  | C a =>
    ext i j
    by_cases hij : i = j
    · subst hij; simp [_root_.Formalism.UG.cT, Polynomial.aeval_C, Matrix.algebraMap_matrix_apply]
    · simp [_root_.Formalism.UG.cT, Polynomial.aeval_C, Matrix.algebraMap_matrix_apply, hij, Ne.symm hij]
  | add p q hp hq =>
    simp only [map_add, Polynomial.map_add, ← hp, ← hq]
    simp [_root_.Formalism.UG.cT, Matrix.map_add, Matrix.transpose_add]
  | monomial m a hm =>
    rw [pow_succ, ← mul_assoc, mul_comm _ Polynomial.X, Polynomial.map_mul,
      map_mul (Polynomial.aeval B) Polynomial.X, map_mul (Polynomial.aeval (_root_.Formalism.UG.cT c B)), ← hm,
      Polynomial.map_X, Polynomial.aeval_X, Polynomial.aeval_X]
    have hcomm : Polynomial.aeval B (Polynomial.C a * Polynomial.X ^ m) * B =
        B * Polynomial.aeval B (Polynomial.C a * Polynomial.X ^ m) := by
      have := congrArg (Polynomial.aeval B) (mul_comm (Polynomial.C a * Polynomial.X ^ m) Polynomial.X)
      simpa only [map_mul, Polynomial.aeval_X] using this
    simp only [_root_.Formalism.UG.cT, ← Matrix.transpose_mul, ← Matrix.map_mul, hcomm]

open IsDedekindDomain NumberField in
open scoped TensorProduct Matrix in
variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n] in

theorem _root_.GlobalTheory.UnitaryDoubleCoset.exists_poly_norm {c : O →+* O} (hc : ∀ x, c (c x) = x)
    (hN : ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) →
      ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X)
    {B : Matrix n n O} (hB : _root_.Formalism.UG.cT c B = B) (hu : IsUnit B) :
    ∃ p : Polynomial O, _root_.Formalism.UG.cT c (Polynomial.aeval B p) * Polynomial.aeval B p = B := by
  have hmap : B.charpoly.map c = B.charpoly := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_transpose]
    conv_rhs => rw [← hB]
    rfl
  have hunit : IsUnit (B.charpoly.coeff 0) := by
    have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hu
    rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  obtain ⟨p, q, hpq⟩ := hN B.charpoly (Matrix.charpoly_monic B) hmap hunit
  refine ⟨p, ?_⟩
  have h1 := congrArg (Polynomial.aeval B) hpq
  rw [map_mul, Matrix.aeval_self_charpoly, zero_mul, map_sub, Polynomial.aeval_X, sub_eq_zero] at h1
  rw [cT_aeval_eq_aeval_cT_map, hB, ← map_mul, mul_comm, h1]

open IsDedekindDomain NumberField in
open scoped TensorProduct Matrix in
variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.UnitaryDoubleCoset.exists_unitary_factors (ι : O →+* L) {c : O →+* O} {σ : L →+* L}
    (hι : ∀ x, σ (ι x) = ι (c x))
    (hc : ∀ x, c (c x) = x)
    (hN : ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) →
      ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X)
    {g g' : GL n L} (hg : g ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L)) (hg' : g' ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L))
    (h k : GL n O) (e : g' = _root_.Formalism.UG.bc ι h * g * _root_.Formalism.UG.bc ι k) :
    ∃ k₁ ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L) ⊓ (_root_.Formalism.UG.bc ι).range, ∃ k₂ ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L),
      (∃ M : Matrix n n O, (k₂ : Matrix n n L) = M.map ι) ∧ g' = k₁ * g * k₂ := by
  have hmul : ∀ {R : Type} [CommRing R] (τ : R →+* R) (A B : Matrix n n R),
      _root_.Formalism.UG.cT τ (A * B) = _root_.Formalism.UG.cT τ B * _root_.Formalism.UG.cT τ A := by
    intro R _ τ A B
    simp [_root_.Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hone : ∀ {R : Type} [CommRing R] (τ : R →+* R), _root_.Formalism.UG.cT τ (1 : Matrix n n R) = 1 := by
    intro R _ τ
    simp [_root_.Formalism.UG.cT]

  have hinv : ∀ u : GL n L, _root_.Formalism.UG.cT σ (u : Matrix n n L) * u = 1 →
      _root_.Formalism.UG.cT σ (u : Matrix n n L) = ((u⁻¹ : GL n L) : Matrix n n L) ∧
        _root_.Formalism.UG.cT σ ((u⁻¹ : GL n L) : Matrix n n L) = u := by
    intro u hu
    have h1 : _root_.Formalism.UG.cT σ (u : Matrix n n L) = ((u⁻¹ : GL n L) : Matrix n n L) := by
      calc _root_.Formalism.UG.cT σ (u : Matrix n n L) = _root_.Formalism.UG.cT σ (u : Matrix n n L) * (u * ↑u⁻¹) := by
            rw [Units.mul_inv, mul_one]
        _ = ((u⁻¹ : GL n L) : Matrix n n L) := by rw [← mul_assoc, hu, one_mul]
    refine ⟨h1, ?_⟩
    have h2 : _root_.Formalism.UG.cT σ ((u⁻¹ : GL n L) : Matrix n n L) * ((u⁻¹ : GL n L) : Matrix n n L) = 1 := by
      have h3 := hmul σ (u : Matrix n n L) ((u⁻¹ : GL n L) : Matrix n n L)
      rw [Units.mul_inv, hone, h1] at h3
      exact h3.symm
    calc _root_.Formalism.UG.cT σ ((u⁻¹ : GL n L) : Matrix n n L)
        = _root_.Formalism.UG.cT σ ((u⁻¹ : GL n L) : Matrix n n L) * (((u⁻¹ : GL n L) : Matrix n n L) * u) := by
          rw [Units.inv_mul, mul_one]
      _ = u := by rw [← mul_assoc, h2, one_mul]
  have hg1 : _root_.Formalism.UG.cT σ (g : Matrix n n L) * g = 1 := by simpa [_root_.Formalism.UG.UJ] using hg
  have hg'1 : _root_.Formalism.UG.cT σ (g' : Matrix n n L) * g' = 1 := by simpa [_root_.Formalism.UG.UJ] using hg'
  have hbc : ∀ u : GL n O, ((_root_.Formalism.UG.bc ι u : GL n L) : Matrix n n L) = (u : Matrix n n O).map ι := by
    intro u
    simp [_root_.Formalism.UG.bc]

  set H := _root_.Formalism.UG.cT c (h : Matrix n n O) * h with hHdef
  have hH : _root_.Formalism.UG.cT c H = H := by
    rw [hHdef, hmul, _root_.GlobalTheory.UnitaryDoubleCoset.cT_cT hc]
  have hHu : IsUnit H := by
    refine IsUnit.mul (IsUnit.of_mul_eq_one (_root_.Formalism.UG.cT c ((h⁻¹ : GL n O) : Matrix n n O)) ?_) h.isUnit
    rw [← hmul, Units.inv_mul, hone]
  obtain ⟨p, hp⟩ := _root_.GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc hN hH hHu
  set P := Polynomial.aeval H p with hPdef
  have hPu : IsUnit P := isUnit_of_mul_isUnit_right (hp.symm ▸ hHu)
  set k₁ : GL n L := _root_.Formalism.UG.bc ι (h * hPu.unit⁻¹) with hk₁def
  have hk₁ : k₁ ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L) := by
    have hO : _root_.Formalism.UG.cT c ((h * hPu.unit⁻¹ : GL n O) : Matrix n n O) *
        ((h * hPu.unit⁻¹ : GL n O) : Matrix n n O) = 1 := by
      rw [Units.val_mul, hmul]
      calc _root_.Formalism.UG.cT c ((hPu.unit⁻¹ : GL n O) : Matrix n n O) * _root_.Formalism.UG.cT c (h : Matrix n n O) *
            ((h : Matrix n n O) * ((hPu.unit⁻¹ : GL n O) : Matrix n n O))
          = _root_.Formalism.UG.cT c ((hPu.unit⁻¹ : GL n O) : Matrix n n O) * (_root_.Formalism.UG.cT c P * P) *
            ((hPu.unit⁻¹ : GL n O) : Matrix n n O) := by
            rw [hp, hHdef]; simp only [mul_assoc]
        _ = _root_.Formalism.UG.cT c (P * ((hPu.unit⁻¹ : GL n O) : Matrix n n O)) *
            (P * ((hPu.unit⁻¹ : GL n O) : Matrix n n O)) := by
            rw [hmul]; simp only [mul_assoc]
        _ = 1 := by rw [hPu.mul_val_inv, hone, one_mul]
    show _root_.Formalism.UG.cT σ (k₁ : Matrix n n L) * 1 * k₁ = 1
    rw [mul_one, hk₁def, hbc, _root_.GlobalTheory.UnitaryDoubleCoset.cT_map ι hι, ← Matrix.map_mul, hO,
      Matrix.map_one _ (map_zero ι) (map_one ι)]
  refine ⟨k₁, ⟨hk₁, ⟨_, rfl⟩⟩, g⁻¹ * k₁⁻¹ * g',
    mul_mem (mul_mem (inv_mem hg) (inv_mem hk₁)) hg', ?_, by group⟩

  obtain ⟨hGc, hGic⟩ := hinv g hg1
  obtain ⟨hG'c, -⟩ := hinv g' hg'1
  have eM : (g' : Matrix n n L) = (h : Matrix n n O).map ι * g * (k : Matrix n n O).map ι := by
    rw [e, Units.val_mul, Units.val_mul, hbc, hbc]
  have hkk : (k : Matrix n n O).map ι * (↑k⁻¹ : Matrix n n O).map ι = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hhh : (↑h⁻¹ : Matrix n n O).map ι * (h : Matrix n n O).map ι = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero ι) (map_one ι)]

  have hHg : (h : Matrix n n O).map ι * g = g' * (↑k⁻¹ : Matrix n n O).map ι := by
    rw [eM, mul_assoc _ _ ((↑k⁻¹ : Matrix n n O).map ι), hkk, mul_one]
  have hhm : (h : Matrix n n O).map ι =
      g' * (↑k⁻¹ : Matrix n n O).map ι * ((g⁻¹ : GL n L) : Matrix n n L) := by
    rw [← hHg, mul_assoc, Units.mul_inv, mul_one]
  set Hk := _root_.Formalism.UG.cT c ((k⁻¹ : GL n O) : Matrix n n O) * ((k⁻¹ : GL n O) : Matrix n n O)
    with hHkdef
  have hconj : H.map ι * g = g * Hk.map ι := by
    rw [hHdef, hHkdef, Matrix.map_mul, Matrix.map_mul, ← _root_.GlobalTheory.UnitaryDoubleCoset.cT_map ι hι,
      ← _root_.GlobalTheory.UnitaryDoubleCoset.cT_map ι hι, mul_assoc, hHg, ← mul_assoc]
    conv_lhs => rw [hhm, hmul, hmul, hG'c, hGic]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  clear_value Hk P H
  have hsemi : ∀ q : Polynomial O, (Polynomial.aeval H q).map ι * g =
      g * (Polynomial.aeval Hk q).map ι := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      simp only [Polynomial.aeval_C, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero ι)]
      ext i j
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
    | add p q hp hq =>
      rw [map_add, map_add, Matrix.map_add _ (map_add ι), Matrix.map_add _ (map_add ι), add_mul,
        mul_add, hp, hq]
    | monomial m a hm =>
      rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval H) _ Polynomial.X,
        map_mul (Polynomial.aeval Hk) _ Polynomial.X, Polynomial.aeval_X, Polynomial.aeval_X,
        Matrix.map_mul, Matrix.map_mul, mul_assoc, hconj, ← mul_assoc, hm, mul_assoc]
  refine ⟨Polynomial.aeval Hk p * k, ?_⟩
  rw [Units.val_mul, Units.val_mul, hk₁def, ← map_inv, hbc, mul_inv_rev, inv_inv, Units.val_mul,
    hPu.unit_spec, Matrix.map_mul, eM, Matrix.map_mul]
  have hcancel : ((g⁻¹ : GL n L) : Matrix n n L) * (P.map ι * (↑h⁻¹ : Matrix n n O).map ι) *
      ((h : Matrix n n O).map ι * g * (k : Matrix n n O).map ι) =
      ((g⁻¹ : GL n L) : Matrix n n L) * (P.map ι * g) * (k : Matrix n n O).map ι := by
    simp only [mul_assoc]
    rw [← mul_assoc ((↑h⁻¹ : Matrix n n O).map ι), hhh, one_mul]
  rw [hcancel, hPdef, hsemi p, ← mul_assoc, Units.inv_mul, one_mul]

end Abstract

theorem doubleCoset_unitary_of_GL (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (σ : v.adicCompletion K →+* v.adicCompletion K) (n : ℕ) (hσσ : ∀ x, σ (σ x) = x)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hx : ∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) :
    ∀ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)),
    ∀ g' ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)),
    ∀ h ∈ GLint (Fin n) (Ov K v), ∀ k ∈ GLint (Fin n) (Ov K v), g' = h * g * k →
      ∃ k₁ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v),
      ∃ k₂ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v),
        g' = k₁ * g * k₂ := by
  rintro g hg g' hg' _ ⟨h, rfl⟩ _ ⟨k, rfl⟩ e
  have := isAdicComplete_adicCompletionIntegers v
  have : Finite (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
    finite_residueField_adicCompletionIntegers v
  let c : v.adicCompletionIntegers K →+* v.adicCompletionIntegers K :=
    (σ.comp (v.adicCompletionIntegers K).subtype).codRestrict (v.adicCompletionIntegers K) fun x => by
      show Valued.v (σ x) ≤ 1
      rw [hσ]; exact x.2
  have hcv : ∀ x, ((c x : v.adicCompletionIntegers K) : v.adicCompletion K) = σ x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hσσ x)
  have hI : ∀ x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K),
      c x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    intro x hx hu
    exact hx (by simpa [hc] using hu.map c)
  have hω : ∃ ω, IsUnit (ω - c ω) := by
    obtain ⟨x, hx1, hx2⟩ := hx
    refine ⟨⟨x, hx1⟩, ?_⟩
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    show Valued.v (x - σ x) = 1
    rw [Valuation.map_sub_swap, hx2]
  obtain ⟨k₁, hk₁, k₂, hk₂, ⟨M, hM⟩, e'⟩ :=
    exists_unitary_factors (O := Ov K v) (Ov K v).subtype (c := c) (σ := σ) (fun _ => rfl) hc
      (GlobalTheory.T.exists_norm_eq_X_mod_monic_of_adicComplete_involution (v.adicCompletionIntegers K) _ c hc hI hω) hg hg' h k e
  refine ⟨k₁, hk₁, k₂, ⟨hk₂, ?_⟩, e'⟩
  refine GlobalTheory.UnitarySwap.mem_GLint_of_unitary (J := 1) hσ (one_mem _) hk₂ fun i j => ?_
  rw [hM]
  exact (M i j).2

end GlobalTheory.UnitaryDoubleCoset
