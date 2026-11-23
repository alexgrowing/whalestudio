import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec

noncomputable section

open MvPolynomial Matrix

namespace PositivityTheory.SiegelWeilFormula.KSplit

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def actU (u : Matrix (Fin m) (Fin m) ℂ) : PX m n →ₐ[ℂ] PX m n :=
  aeval fun k =>
    if k.2.2 then ∑ c, C (star (u k.1 c)) * X (c, k.2.1, true) else ∑ c, C (u k.1 c) * X (c, k.2.1, false)

def lf (b : Bool) (M : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) : PX m n := ∑ c, C (M a c) * X (c, i, b)

def am (b : Bool) (u : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ := if b then u.map star else u

theorem actU_X (u : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) (b : Bool) :
    actU u (X (a, i, b)) = lf b (am b u) a i := by
  cases b <;> simp [actU, lf, am]

theorem lin_lf (φ : PX m n →ₗ[ℂ] PX m n) (b : Bool) (N M : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n)
    (h : ∀ c, φ (X (c, i, b)) = lf b N c i) : φ (lf b M a i) = lf b (M * N) a i := by
  simp only [lf, C_mul', map_sum, map_smul, h, Finset.smul_sum, smul_smul, mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => C_mul'.symm

theorem mstar_mul (A B : Matrix (Fin m) (Fin m) ℂ) : (A * B).map star = A.map star * B.map star := by
  ext i j; simp [mul_apply, star_sum]

theorem am_mul (b : Bool) (A B : Matrix (Fin m) (Fin m) ℂ) : am b (A * B) = am b A * am b B := by
  cases b <;> simp [am, mstar_mul]

theorem actU_lf (u M : Matrix (Fin m) (Fin m) ℂ) (b : Bool) (a : Fin m) (i : Fin n) :
    actU u (lf b M a i) = lf b (M * am b u) a i :=
  lin_lf (actU u).toLinearMap b _ M a i fun c => actU_X u c i b

theorem actU_comp (A B : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : actU A (actU B P) = actU (B * A) P := by
  have h : (actU (n := n) A).comp (actU B) = actU (B * A) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, i, b⟩
    rw [AlgHom.comp_apply, actU_X, actU_X, actU_lf, am_mul]
  exact congrArg (fun f : PX m n →ₐ[ℂ] PX m n => f P) h

theorem actU_one (P : PX m n) : actU 1 P = P := by
  have h : actU (n := n) (1 : Matrix (Fin m) (Fin m) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, i, b⟩
    cases b <;> simp [actU, one_apply]
  rw [h]; rfl

theorem evX_actU (u : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) (v : Matrix (Fin m) (Fin n) ℂ) :
    evX (actU u P) v = evX P (u * v) := by
  have h : (aeval (R := ℂ) fun k : Fin m × Fin n × Bool =>
      if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1).comp (actU u) =
      aeval fun k : Fin m × Fin n × Bool => if k.2.2 then star ((u * v) k.1 k.2.1) else (u * v) k.1 k.2.1 := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, i, b⟩
    cases b
    · simp [actU, mul_apply]
    · simp [actU, mul_apply, star_sum]
  have e := congrArg (fun f : PX m n →ₐ[ℂ] ℂ => f P) h
  simp only [AlgHom.comp_apply, coe_aeval_eq_eval] at e
  exact e

def dm (b : Bool) (Y : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ := if b then -Yᵀ else Y

def dY (Y : Matrix (Fin m) (Fin m) ℂ) : Derivation ℂ (PX m n) (PX m n) :=
  MvPolynomial.mkDerivation ℂ fun k => lf k.2.2 (dm k.2.2 Y) k.1 k.2.1

theorem dY_X (Y : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) (b : Bool) :
    dY Y (X (a, i, b)) = lf b (dm b Y) a i := by
  simp [dY, mkDerivation_X]

theorem dY_lf (Y M : Matrix (Fin m) (Fin m) ℂ) (b : Bool) (a : Fin m) (i : Fin n) :
    dY Y (lf b M a i) = lf b (M * dm b Y) a i :=
  lin_lf (dY Y : Derivation ℂ (PX m n) (PX m n)).toLinearMap b _ M a i fun c => dY_X Y c i b

theorem lf_add (b : Bool) (M N : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) :
    lf b (M + N) a i = lf b M a i + lf b N a i := by
  simp [lf, add_mul, Finset.sum_add_distrib]

theorem lf_smul (b : Bool) (z : ℂ) (M : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) :
    lf b (z • M) a i = z • lf b M a i := by
  simp [lf, C_mul', smul_smul, Finset.smul_sum]

theorem dY_add (Y Y' : Matrix (Fin m) (Fin m) ℂ) : (dY (Y + Y') : Derivation ℂ (PX m n) (PX m n)) = dY Y + dY Y' := by
  apply MvPolynomial.derivation_ext
  rintro ⟨a, i, b⟩
  rw [Derivation.add_apply, dY_X, dY_X, dY_X, ← lf_add]
  congr 1
  cases b <;> simp [dm, add_comm]

theorem dY_smul (z : ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) : (dY (z • Y) : Derivation ℂ (PX m n) (PX m n)) = z • dY Y := by
  apply MvPolynomial.derivation_ext
  rintro ⟨a, i, b⟩
  rw [Derivation.smul_apply, dY_X, dY_X, ← lf_smul]
  congr 1
  cases b <;> simp [dm]

theorem actU_dY_actU (V : Matrix (Fin m) (Fin m) ℂ) (hV : V ∈ unitaryGroup (Fin m) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ)
    (P : PX m n) : actU V (dY Y (actU (star V) P)) = dY (star V * Y * V) P := by
  have hid : ∀ Q : PX m n, actU V (actU (star V) Q) = Q := fun Q => by
    rw [actU_comp, (mem_unitaryGroup_iff'.1 hV), actU_one]
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : actU (n := n) (star V) (C a) = C a := by simp [actU]
    rw [this, derivation_C, map_zero, derivation_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    have key : actU V (dY Y (actU (star V) (X k))) = dY (star V * Y * V) (X k) := by
      obtain ⟨a, i, b⟩ := k
      rw [actU_X, dY_lf, actU_lf, dY_X]
      congr 1
      cases b
      · simp [am, dm, Matrix.mul_assoc]
      · have h1 : (star V).map star = Vᵀ := by ext c e; simp [star_eq_conjTranspose]
        have h2 : V.map star = (star V)ᵀ := by ext c e; simp [star_eq_conjTranspose]
        simp only [am, dm, if_true, h1, h2, transpose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hid, hid, hp, key,
      Derivation.leibniz, smul_eq_mul, smul_eq_mul]

theorem der_monomial (D : Derivation ℂ (PX m n) (PX m n)) (w : Fin m × Fin n × Bool → ℂ)
    (hD : ∀ k, D (X k) = C (w k) * X k) (s : Fin m × Fin n × Bool →₀ ℕ) :
    D (monomial s 1) = C (s.sum fun k e => (e : ℂ) * w k) * monomial s 1 := by
  induction s using Finsupp.induction with
  | zero => simp
  | single_add k e s _ _ ih =>
    have e1 : (monomial (Finsupp.single k e + s) (1 : ℂ) : PX m n) = X k ^ e * monomial s 1 := by
      rw [X_pow_eq_monomial (R := ℂ), monomial_mul, one_mul]
    rw [e1, Derivation.leibniz, Derivation.leibniz_pow, hD, ih, Finsupp.sum_add_index' (fun _ => by simp)
      (fun _ _ _ => by push_cast; ring), Finsupp.sum_single_index (by simp)]
    simp only [smul_eq_mul, nsmul_eq_mul, map_add, map_mul, map_natCast]
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · subst h0; simp
    · have : (X k : PX m n) ^ e = X k ^ (e - 1) * X k := by
        rw [← pow_succ, Nat.sub_add_cancel hpos]
      rw [this]; ring

theorem actU_diag_monomial (ζ : Fin m → ℂ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    actU (diagonal ζ) (monomial s 1) =
      C (s.prod fun k e => (if k.2.2 then star (ζ k.1) else ζ k.1) ^ e) * monomial s (1 : ℂ) := by
  have hX : ∀ k : Fin m × Fin n × Bool, actU (n := n) (diagonal ζ) (X k) =
      C (if k.2.2 then star (ζ k.1) else ζ k.1) * X k := by
    rintro ⟨a, i, b⟩
    rw [actU_X]
    cases b
    · simp only [lf, am, Bool.false_eq_true, if_false]
      rw [Finset.sum_eq_single a (fun c _ hc => by rw [diagonal_apply_ne _ (Ne.symm hc)]; simp) (by simp)]
      simp
    · simp only [lf, am, if_true]
      rw [Finset.sum_eq_single a (fun c _ hc => by rw [map_apply, diagonal_apply_ne _ (Ne.symm hc)]; simp) (by simp)]
      simp
  simp only [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod, map_pow, hX, mul_pow, ← Finset.prod_mul_distrib]

def chg (a : Fin m) (s : Fin m × Fin n × Bool →₀ ℕ) : ℤ :=
  s.sum fun k e => if k.1 = a then (if k.2.2 then -(e : ℤ) else e) else 0

theorem chg_add (a : Fin m) (k : Fin m × Fin n × Bool) (e : ℕ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    chg a (Finsupp.single k e + s) = (if k.1 = a then (if k.2.2 then -(e : ℤ) else e) else 0) + chg a s := by
  unfold chg
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by split_ifs <;> push_cast <;> ring),
    Finsupp.sum_single_index (by simp)]

theorem prod_phase (a : Fin m) (z : ℂ) (hz : star z * z = 1) (s : Fin m × Fin n × Bool →₀ ℕ) :
    (s.prod fun k e => (if k.2.2 then star (if k.1 = a then z else 1) else (if k.1 = a then z else 1)) ^ e) =
      z ^ chg a s := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hs : star z = z⁻¹ := eq_inv_of_mul_eq_one_left hz
  induction s using Finsupp.induction with
  | zero => simp [chg]
  | single_add k e s _ _ ih =>
    rw [Finsupp.prod_add_index' (fun _ => by simp) (fun _ _ _ => by rw [pow_add]), Finsupp.prod_single_index (by simp), ih,
      chg_add, zpow_add₀ hz0]
    congr 1
    split_ifs with h1 h2 h2 <;> simp [hs, _root_.zpow_neg, zpow_natCast]

theorem star_exp_mul_I (t : ℝ) : star (Complex.exp (t * Complex.I)) * Complex.exp (t * Complex.I) = 1 := by
  rw [show star (Complex.exp (t * Complex.I)) = Complex.exp (-(t * Complex.I)) by
    rw [Complex.star_def, ← Complex.exp_conj]; simp [Complex.conj_ofReal], ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero]

theorem kill_charged (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ u ∈ unitaryGroup (Fin m) ℂ, ∀ P, Λ (actU u P) = Λ P)
    (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (h : chg a s ≠ 0) : Λ (monomial s 1) = 0 := by
  set q := chg a s
  set z : ℂ := Complex.exp ((Real.pi / q : ℝ) * Complex.I)
  have hz : star z * z = 1 := star_exp_mul_I _
  have hq : z ^ q = -1 := by
    rw [← Complex.exp_int_mul]
    rw [show (q : ℂ) * (((Real.pi / q : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I by
      push_cast; field_simp]
    exact Complex.exp_pi_mul_I
  set ζ : Fin m → ℂ := fun c => if c = a then z else 1
  have hu : diagonal ζ ∈ unitaryGroup (Fin m) ℂ := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; ext c; simp only [ζ, Pi.star_apply, Pi.mul_apply, Pi.one_apply]; split_ifs
    · exact hz
    · simp
  have e := hΛ _ hu (monomial s 1)
  rw [actU_diag_monomial, C_mul', map_smul, smul_eq_mul] at e
  have e2 : (s.prod fun k e => (if k.2.2 then star (ζ k.1) else ζ k.1) ^ e) = -1 := by
    rw [← hq]; exact prod_phase a z hz s
  rw [e2] at e
  linear_combination -e / 2

theorem sum_weight (d : Fin m → ℂ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    (s.sum fun k e => (e : ℂ) * if k.2.2 then -d k.1 else d k.1) = ∑ a, d a * chg a s := by
  simp only [chg, Finsupp.sum, Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k.1 (fun b _ hb => by
    have : k.1 ≠ b := Ne.symm hb
    simp [this]) (by simp)]
  rcases k with ⟨a, i, b⟩
  cases b <;> simp [mul_comm]

theorem kill_diag (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ u ∈ unitaryGroup (Fin m) ℂ, ∀ P, Λ (actU u P) = Λ P)
    (d : Fin m → ℂ) (P : PX m n) : Λ (dY (diagonal d) P) = 0 := by
  have hD : ∀ k : Fin m × Fin n × Bool, dY (diagonal d) (X k) = C (if k.2.2 then -d k.1 else d k.1) * X k := by
    rintro ⟨a, i, b⟩
    rw [dY_X]
    cases b
    · simp only [lf, dm, Bool.false_eq_true, if_false]
      rw [Finset.sum_eq_single a (fun c _ hc => by rw [diagonal_apply_ne _ (Ne.symm hc)]; simp) (by simp)]
      simp
    · simp only [lf, dm, if_true]
      rw [Finset.sum_eq_single a (fun c _ hc => by
        rw [Matrix.neg_apply, transpose_apply, diagonal_apply_ne _ hc]; simp) (by simp)]
      simp
  have hmon : ∀ s, Λ (dY (diagonal d) (monomial s 1)) = 0 := fun s => by
    rw [der_monomial _ _ hD, C_mul', map_smul, smul_eq_mul, sum_weight]
    by_cases h : ∀ a, chg a s = 0
    · rw [Finset.sum_eq_zero fun a _ => by rw [h a]; simp, zero_mul]
    · push Not at h
      obtain ⟨a, ha⟩ := h
      rw [kill_charged Λ hΛ s a ha, mul_zero]
  rw [P.as_sum, map_sum, map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [show (monomial s (coeff s P) : PX m n) = coeff s P • monomial s 1 by rw [smul_monomial, smul_eq_mul, mul_one],
    (dY (diagonal d)).map_smul, map_smul, hmon, smul_zero]

theorem kill_herm (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ u ∈ unitaryGroup (Fin m) ℂ, ∀ P, Λ (actU u P) = Λ P)
    (H : Matrix (Fin m) (Fin m) ℂ) (hH : H.IsHermitian) (P : PX m n) : Λ (dY H P) = 0 := by
  set U := hH.eigenvectorUnitary
  have e := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at e
  have hs : star (U : Matrix (Fin m) (Fin m) ℂ) ∈ unitaryGroup (Fin m) ℂ := Unitary.star_mem U.2
  have e2 : H = star (star (U : Matrix (Fin m) (Fin m) ℂ)) * diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
      star (U : Matrix (Fin m) (Fin m) ℂ) := by rw [star_star]; exact e
  rw [e2, ← actU_dY_actU _ hs, hΛ _ hs]
  exact kill_diag Λ hΛ _ _

theorem kill_dY (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ u ∈ unitaryGroup (Fin m) ℂ, ∀ P, Λ (actU u P) = Λ P)
    (Y : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : Λ (dY Y P) = 0 := by
  obtain ⟨H₁, h1, H₂, h2, eY⟩ : ∃ H₁ : Matrix (Fin m) (Fin m) ℂ, H₁.IsHermitian ∧ ∃ H₂ : Matrix (Fin m) (Fin m) ℂ,
      H₂.IsHermitian ∧ Y = H₁ + Complex.I • H₂ := by
    refine ⟨(1 / 2 : ℂ) • (Y + Yᴴ), ?_, (1 / (2 * Complex.I) : ℂ) • (Y - Yᴴ), ?_, ?_⟩
    · ext i j
      simp only [IsHermitian, conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, star_mul',
        star_add, star_star]
      rw [show star (1 / 2 : ℂ) = 1 / 2 by simp [Complex.ext_iff]]
      ring
    · ext i j
      simp only [IsHermitian, conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, star_mul',
        star_sub, star_star]
      rw [show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by
        simp [Complex.ext_iff, Complex.div_re, Complex.div_im]]
      ring
    · ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      field_simp
      ring
  rw [eY, dY_add, dY_smul, Derivation.add_apply, Derivation.smul_apply, map_add, map_smul, kill_herm Λ hΛ _ h1,
    kill_herm Λ hΛ _ h2, smul_zero, add_zero]

theorem dsum_apply {ι : Type} (s : Finset ι) (D : ι → Derivation ℂ (PX m n) (PX m n)) (P : PX m n) :
    (∑ i ∈ s, D i) P = ∑ i ∈ s, D i P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]

theorem hOp_eq (c : ℝ) (a b : Fin m) (P : PX m n) : hOp (fun _ => true) c a b P = dY (single a b 1) P := by
  set D' : Derivation ℂ (PX m n) (PX m n) := ∑ i, ((X (b, i, false) : PX m n) • pderiv (a, i, false) -
    (X (a, i, true) : PX m n) • pderiv (b, i, true))
  have h1 : hOp (fun _ => true) c a b P = D' P := by
    simp only [D', dsum_apply, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, hOp, sgn, if_true, mul_one,
      sub_self, mul_zero, map_zero, zero_mul, sub_zero, C_1, one_mul]
  have h2 : D' = dY (single a b 1) := by
    apply MvPolynomial.derivation_ext
    rintro ⟨a', i', b'⟩
    rw [dY_X]
    simp only [D', dsum_apply, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, pderiv_X, Pi.single_apply,
      Prod.mk.injEq]
    cases b'
    · simp only [lf, dm, Bool.false_eq_true, if_false, and_false, mul_zero, sub_zero, single_apply]
      by_cases ha : a' = a
      · subst ha
        rw [Finset.sum_eq_single b (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
        rw [Finset.sum_eq_single i' (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
        simp
      · simp [Ne.symm ha, ha]
    · simp only [lf, dm, if_true, and_false, and_true, mul_zero, zero_sub, single_apply, Matrix.neg_apply,
        transpose_apply]
      by_cases hb : a' = b
      · subst hb
        rw [Finset.sum_eq_single a (fun c _ hc => by simp [hc, Ne.symm hc]) (by simp)]
        rw [Finset.sum_eq_single i' (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
        simp
      · simp [Ne.symm hb, hb]
  rw [h1, h2]

theorem hOp_kill (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ u ∈ unitaryGroup (Fin m) ℂ, ∀ P, Λ (actU u P) = Λ P) (c : ℝ)
    (a b : Fin m) (P : PX m n) : Λ (hOp (fun _ => true) c a b P) = 0 := by
  rw [hOp_eq]; exact kill_dY Λ hΛ _ P

end PositivityTheory.SiegelWeilFormula.KSplit

end
