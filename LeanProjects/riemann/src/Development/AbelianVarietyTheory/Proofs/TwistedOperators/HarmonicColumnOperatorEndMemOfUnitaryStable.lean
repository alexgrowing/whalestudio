import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumSmulMemOfSumZpowSmulMem
open scoped ComplexConjugate
open MvPolynomial Matrix

namespace GlobalTheory.Harm

section ColDerM
variable {R : Type*} [CommRing R] {T : Type*} [DecidableEq T] {p q : ℕ} {κ : Type*} [Fintype κ]

noncomputable def colDerM (t : T) (X : Matrix κ κ R) : Derivation R (Poly R T p q κ) (Poly R T p q κ) :=
  mkDerivation R fun v => match v with
    | (t', Sum.inl a, j) => if t' = t then xForm t a (X j) else 0
    | (t', Sum.inr b, j) => if t' = t then -yForm t b (fun r => X r j) else 0

theorem colDerM_X_xVar (t t' : T) (X : Matrix κ κ R) (a : Fin p) (j : κ) :
    colDerM (q := q) t X (MvPolynomial.X (xVar t' a j)) = if t' = t then xForm t a (X j) else 0 := by
  simp [colDerM, mkDerivation_X]

theorem colDerM_X_yVar (t t' : T) (X : Matrix κ κ R) (b : Fin q) (j : κ) :
    colDerM (p := p) t X (MvPolynomial.X (yVar t' b j)) =
      if t' = t then -yForm t b (fun r => X r j) else 0 := by
  simp [colDerM, mkDerivation_X]

omit [DecidableEq T] in
theorem xForm_eq_sum (t : T) (a : Fin p) (ε : κ → R) :
    (xForm t a ε : Poly R T p q κ) = ∑ k, ε k • MvPolynomial.X (xVar t a k) := by
  simp [xForm_apply, smul_eq_C_mul]

omit [DecidableEq T] in
theorem yForm_eq_sum (t : T) (b : Fin q) (φ : κ → R) :
    (yForm t b φ : Poly R T p q κ) = ∑ k, φ k • MvPolynomial.X (yVar t b k) := by
  simp [yForm_apply, smul_eq_C_mul]

theorem colDerM_xForm (t t' : T) (X : Matrix κ κ R) (a : Fin p) (ε : κ → R) :
    colDerM (q := q) t X (xForm t' a ε) = if t' = t then xForm t a (ε ᵥ* X) else 0 := by
  have hv : ε ᵥ* X = ∑ k, ε k • X k := by ext l; simp [vecMul, dotProduct]
  rw [xForm_eq_sum, map_sum]
  simp only [Derivation.map_smul, colDerM_X_xVar]
  split_ifs with h
  · rw [hv, map_sum]; simp [map_smul]
  · simp

theorem colDerM_yForm (t t' : T) (X : Matrix κ κ R) (b : Fin q) (φ : κ → R) :
    colDerM (p := p) t X (yForm t' b φ) = if t' = t then -yForm t b (X *ᵥ φ) else 0 := by
  have hv : X *ᵥ φ = ∑ k, φ k • fun r => X r k := by ext l; simp [mulVec, dotProduct, mul_comm]
  rw [yForm_eq_sum, map_sum]
  simp only [Derivation.map_smul, colDerM_X_yVar]
  split_ifs with h
  · rw [hv, map_sum]; simp [map_smul, Finset.sum_neg_distrib]
  · simp

variable [DecidableEq κ] in

theorem colActHom_colDerM (g : T → GL κ R) (t : T) (X : Matrix κ κ R) (P : Poly R T p q κ) :
    colActHom g (colDerM t X P) =
      colDerM t ((g t : Matrix κ κ R) * X * (((g t)⁻¹ : GL κ R) : Matrix κ κ R)) (colActHom g P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [colActHom, algHom_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    have hgen : colActHom g (colDerM t X (MvPolynomial.X v)) =
        colDerM t ((g t : Matrix κ κ R) * X * (((g t)⁻¹ : GL κ R) : Matrix κ κ R))
          (colActHom g (MvPolynomial.X v)) := by
      obtain ⟨t', a | b, j⟩ := v
      · rw [colDerM_X_xVar]
        simp only [colActHom, colSubst_X_xVar, colDerM_xForm]
        split_ifs with h
        · subst h
          rw [colSubst_xForm]
          congr 1
          have key : ∀ (M N : Matrix κ κ R) (j : κ), M j ᵥ* N = (M * N) j := fun M N j => by
            ext i; simp [vecMul, dotProduct, mul_apply]
          rw [key, key, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        · simp
      · rw [colDerM_X_yVar]
        simp only [colActHom, colSubst_X_yVar, colDerM_yForm]
        split_ifs with h
        · subst h
          rw [map_neg, colSubst_yForm]
          congr 2
          have key : ∀ (M N : Matrix κ κ R) (j : κ), (M *ᵥ fun r => N r j) = fun r => (M * N) r j :=
            fun M N j => by ext i; simp [mulVec, dotProduct, mul_apply]
          rw [key, key, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
        · simp
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, map_mul,
      Derivation.leibniz, smul_eq_mul, smul_eq_mul, hP, hgen]

end ColDerM
end GlobalTheory.Harm

namespace GlobalTheory.Harm

section ColDerLin
variable {R : Type*} [CommRing R] {T : Type*} [DecidableEq T] {p q : ℕ} {κ : Type*} [Fintype κ]
  [DecidableEq κ]

theorem colDerM_add (t : T) (X Y : Matrix κ κ R) :
    colDerM (p := p) (q := q) t (X + Y) = colDerM t X + colDerM t Y := by
  refine MvPolynomial.derivation_ext fun ⟨t', r, j⟩ => ?_
  rcases r with a | b
  · rw [Derivation.add_apply, colDerM_X_xVar, colDerM_X_xVar, colDerM_X_xVar]
    split_ifs
    · rw [show (X + Y) j = X j + Y j from rfl, map_add]
    · simp
  · rw [Derivation.add_apply, colDerM_X_yVar, colDerM_X_yVar, colDerM_X_yVar]
    split_ifs
    · have : (fun r => (X + Y) r j) = (fun r => X r j) + (fun r => Y r j) := rfl
      rw [this, map_add, neg_add]
    · simp

theorem colDerM_smul (t : T) (c : R) (X : Matrix κ κ R) :
    colDerM (p := p) (q := q) t (c • X) = c • colDerM t X := by
  refine MvPolynomial.derivation_ext fun ⟨t', r, j⟩ => ?_
  rcases r with a | b
  · rw [Derivation.smul_apply, colDerM_X_xVar, colDerM_X_xVar]
    split_ifs
    · have : (c • X) j = c • X j := rfl
      rw [this, map_smul]
    · simp
  · rw [Derivation.smul_apply, colDerM_X_yVar, colDerM_X_yVar]
    split_ifs
    · have : (fun r => (c • X) r j) = c • (fun r => X r j) := rfl
      rw [this, map_smul, smul_neg]
    · simp

theorem colDerM_single (t : T) (k l : κ) :
    colDerM (p := p) (q := q) t (single l k (1 : R)) = colDer R p q t k l := by
  refine MvPolynomial.derivation_ext fun ⟨t', r, j⟩ => ?_
  rcases r with a | b
  · rw [colDerM_X_xVar, colDer_X_xVar]
    by_cases ht : t' = t
    · by_cases hj : j = l
      · subst hj; rw [if_pos ht, if_pos ⟨ht, rfl⟩, ← xForm_single]
        congr 1; ext i; simp [single_apply, Pi.single_apply, eq_comm]
      · rw [if_pos ht, if_neg (fun h => hj h.2)]
        have : (single l k (1 : R)) j = 0 := by ext i; simp [single_apply, Ne.symm hj, hj]
        rw [this, map_zero]
    · rw [if_neg ht, if_neg (fun h => ht h.1)]
  · rw [colDerM_X_yVar, colDer_X_yVar]
    by_cases ht : t' = t
    · by_cases hj : j = k
      · subst hj; rw [if_pos ht, if_pos ⟨ht, rfl⟩, ← yForm_single]
        congr 2; ext i; simp [single_apply, Pi.single_apply, eq_comm]
      · rw [if_pos ht, if_neg (fun h => hj h.2)]
        have : (fun r => single l k (1 : R) r j) = 0 := by ext i; simp [single_apply, hj, Ne.symm hj]
        rw [this, map_zero, neg_zero]
    · rw [if_neg ht, if_neg (fun h => ht h.1)]

end ColDerLin

section Rot
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def blockMat (k l : κ) (c s s' : ℂ) : Matrix κ κ ℂ :=
  1 + single k k (c - 1) + single l l (c - 1) + single l k s + single k l s'

set_option maxHeartbeats 2000000 in
theorem blockMat_mul_star_eq {k l : κ} (hkl : k ≠ l) (c s s' : ℂ) :
    blockMat k l c s s' * star (blockMat k l c s s') =
      1 + single k k (c * star c + s' * star s' - 1) + single l l (s * star s + c * star c - 1) +
        single k l (c * star s + s' * star c) + single l k (s * star c + c * star s') := by
  simp only [blockMat, star_eq_conjTranspose, conjTranspose_add, conjTranspose_one,
    conjTranspose_single, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_same, single_mul_single_of_ne _ _ _ _ hkl, single_mul_single_of_ne _ _ _ _ hkl.symm,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  ext i j
  simp only [Matrix.add_apply, single_apply, one_apply]
  by_cases hik : i = k <;> by_cases hil : i = l <;> by_cases hjk : j = k <;> by_cases hjl : j = l <;>
    simp_all [eq_comm] <;> ring

theorem blockMat_mul_star {k l : κ} (hkl : k ≠ l) {c s s' : ℂ} (h1 : c * star c + s' * star s' = 1)
    (h2 : s * star s + c * star c = 1) (h3 : c * star s + s' * star c = 0) :
    blockMat k l c s s' * star (blockMat k l c s s') = 1 := by
  have h3' := congrArg star h3
  simp only [star_add, star_mul', star_star, star_zero] at h3'
  rw [blockMat_mul_star_eq hkl, h1, h2, h3, show s * star c + c * star s' = 0 by
    rw [← h3']; ring]
  simp

theorem blockMat_conj_single {k l : κ} (hkl : k ≠ l) (c s s' : ℂ) :
    blockMat k l c s s' * single k k 1 * star (blockMat k l c s s') =
      (c * star c) • single k k 1 + (c * star s) • single k l 1 + (s * star c) • single l k 1 +
        (s * star s) • single l l 1 := by
  simp only [smul_single, smul_eq_mul, mul_one]
  simp only [blockMat, star_eq_conjTranspose, conjTranspose_add, conjTranspose_one,
    conjTranspose_single, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_same, single_mul_single_of_ne _ _ _ _ hkl, single_mul_single_of_ne _ _ _ _ hkl.symm,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  ext i j
  simp only [Matrix.add_apply, single_apply]
  by_cases hik : i = k <;> by_cases hil : i = l <;> by_cases hjk : j = k <;> by_cases hjl : j = l <;>
    simp_all [eq_comm] <;> ring

end Rot
end GlobalTheory.Harm

namespace GlobalTheory.Harm

section Vandermonde
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem sum_smul_mem_of_sum_pow_smul_mem_on (W : Submodule K V) {U : Set K} (hU : U.Infinite)
    (S : Finset ι) (e : ι → ℕ) (v : ι → V) (h : ∀ u ∈ U, ∑ i ∈ S, u ^ e i • v i ∈ W) (f : ℕ → K) :
    ∑ i ∈ S, f (e i) • v i ∈ W := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  have hP : (∑ i ∈ S, Polynomial.monomial (e i) (φ (v i))) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ hU
    intro u hu
    have := hφ _ (h u hu)
    simp only [map_sum, map_smul, smul_eq_mul] at this
    simpa [Polynomial.eval_finset_sum, mul_comm] using this
  have := congrArg (Polynomial.lsum (R := K) (fun n => f n • (LinearMap.id : K →ₗ[K] K))) hP
  simpa [map_sum, Polynomial.lsum_apply, Polynomial.sum_monomial_index] using this

theorem sum_smul_mem_of_sum_zpow_smul_mem_on (W : Submodule K V) {U : Set K} (hU : U.Infinite)
    (hU0 : ∀ u ∈ U, u ≠ 0) (S : Finset ι) (e : ι → ℤ) (v : ι → V)
    (h : ∀ u ∈ U, ∑ i ∈ S, u ^ e i • v i ∈ W) (f : ℤ → K) :
    ∑ i ∈ S, f (e i) • v i ∈ W := by
  set N : ℕ := ∑ i ∈ S, (e i).natAbs with hN
  have hle : ∀ i ∈ S, (((e i + N).toNat : ℕ) : ℤ) = e i + N := fun i hi => by
    have : (e i).natAbs ≤ N :=
      Finset.single_le_sum (f := fun i => (e i).natAbs) (fun _ _ => Nat.zero_le _) hi
    omega
  have := sum_smul_mem_of_sum_pow_smul_mem_on W hU S (fun i => (e i + N).toNat) v (fun u hu => by
    have := W.smul_mem (u ^ N) (h u hu)
    rw [Finset.smul_sum] at this
    convert this using 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [smul_smul, ← zpow_natCast, hle i hi, zpow_add₀ (hU0 u hu), zpow_natCast, mul_comm])
    (fun n => f (n - N))
  convert this using 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hle i hi, add_sub_cancel_right]

end Vandermonde

theorem infinite_unit_circle : {u : ℂ | u * star u = 1}.Infinite := by
  have hne : ∀ x : ℝ, (1 - (x : ℂ) * Complex.I) ≠ 0 := fun x h => by
    have := congrArg Complex.re h; simp at this
  have hne' : ∀ x : ℝ, (1 + (x : ℂ) * Complex.I) ≠ 0 := fun x h => by
    have := congrArg Complex.re h; simp at this
  refine Set.infinite_of_injective_forall_mem (α := ℕ)
    (f := fun n => (1 + ((n : ℝ) : ℂ) * Complex.I) / (1 - ((n : ℝ) : ℂ) * Complex.I)) ?_ ?_
  · intro a b hab
    simp only at hab
    rw [div_eq_div_iff (hne a) (hne b)] at hab
    have := congrArg Complex.im hab
    simp at this
    exact_mod_cast (by linarith : (a : ℝ) = b)
  · intro n
    rw [Set.mem_setOf_eq, Complex.star_def, map_div₀]
    simp only [map_add, map_sub, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hne n) (by simpa using hne' n))]
    ring

section Torus
variable {R : Type*} [CommRing R] {T : Type*} [DecidableEq T] {p q : ℕ} {κ : Type*} [Fintype κ]
  [DecidableEq κ]

noncomputable def diagInvAt (k : κ) (u : Rˣ) : GL κ R :=
  ⟨diagonal (Function.update 1 k ↑u⁻¹), diagonal (Function.update 1 k ↑u),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i
      by_cases h : i = k <;> simp [h],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i
      by_cases h : i = k <;> simp [h]⟩

theorem colActHom_diagInvAt_monomial (t : T) (k : κ) (u : Rˣ) (m : Var T p q κ →₀ ℕ) (c : R) :
    colActHom (Pi.mulSingle t (diagInvAt k u)) (monomial m c : Poly R T p q κ) =
      ((u ^ colWeight m t k : Rˣ) : R) • monomial m c := by
  change colAct R T p q κ (Pi.mulSingle t (diagInvAt k u)) (monomial m c) = _
  revert m c
  have hX (v : Var T p q κ) : colAct R T p q κ (Pi.mulSingle t (diagInvAt k u)) (X v) =
      ((u ^ colWeight (Finsupp.single v 1) t k : Rˣ) : R) • X v := by
    obtain ⟨t', a | b, j⟩ := v
    · rw [colAct_apply, colSubst_X_xVar, ← xForm_single, ← map_smul, colWeight_single_xVar]
      congr 1; ext i
      by_cases ht : t' = t
      · subst ht
        by_cases hj : j = k <;> by_cases hi : j = i <;>
          simp [diagInvAt, diagonal_apply, Pi.single_apply, hj, hi, eq_comm] <;> simp_all [eq_comm]
      · simp [Pi.mulSingle_eq_of_ne ht, Matrix.one_apply, Pi.single_apply, eq_comm, Ne.symm ht]
    · rw [colAct_apply, colSubst_X_yVar, ← yForm_single, ← map_smul, colWeight_single_yVar]
      congr 1; ext i
      by_cases ht : t' = t
      · subst ht
        by_cases hj : j = k <;> by_cases hi : j = i <;>
          simp [diagInvAt, diagonal_apply, Pi.single_apply, hj, hi, eq_comm] <;> simp_all [eq_comm]
      · simp [Pi.mulSingle_eq_of_ne ht, Matrix.one_apply, Pi.single_apply, eq_comm, Ne.symm ht]
  have hpow (v : Var T p q κ) (e : ℕ) :
      colAct R T p q κ (Pi.mulSingle t (diagInvAt k u)) (monomial (Finsupp.single v e) 1) =
        ((u ^ colWeight (Finsupp.single v e) t k : Rˣ) : R) • monomial (Finsupp.single v e) 1 := by
    induction e with
    | zero => simp [colWeight]
    | succ e ih =>
      rw [Finsupp.single_add, colWeight_add, monomial_add_single, pow_one, map_mul, ih, hX,
        _root_.zpow_add, Units.val_mul, smul_mul_smul_comm]
  have hm (m : Var T p q κ →₀ ℕ) : colAct R T p q κ (Pi.mulSingle t (diagInvAt k u)) (monomial m 1) =
        ((u ^ colWeight m t k : Rˣ) : R) • monomial m 1 := by
    induction m using Finsupp.induction_linear with
    | zero => simp [colWeight]
    | add m m' h h' =>
      have e : (monomial (m + m') 1 : Poly R T p q κ) = monomial m 1 * monomial m' 1 := by
        rw [monomial_mul, mul_one]
      rw [e, map_mul, h, h', colWeight_add, _root_.zpow_add, Units.val_mul, smul_mul_smul_comm]
    | single v e => exact hpow v e
  intro m c
  have e : (monomial m c : Poly R T p q κ) = c • monomial m 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, hm, smul_comm]

end Torus

section Unitary
variable {T : Type*} [DecidableEq T] {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem inv_mem_unitaryGroup (g : GL κ ℂ) (hg : (g : Matrix κ κ ℂ) ∈ unitaryGroup κ ℂ) :
    ((g⁻¹ : GL κ ℂ) : Matrix κ κ ℂ) ∈ unitaryGroup κ ℂ := by
  have : ((g⁻¹ : GL κ ℂ) : Matrix κ κ ℂ) = star (g : Matrix κ κ ℂ) :=
    Units.inv_eq_of_mul_eq_one_right (mem_unitaryGroup_iff.mp hg)
  rw [this]; exact Unitary.star_mem hg

theorem mulSingle_mem_unitaryGroup (t : T) (g : GL κ ℂ) (hg : (g : Matrix κ κ ℂ) ∈ unitaryGroup κ ℂ)
    (t' : T) : (((Pi.mulSingle t g : T → GL κ ℂ) t' : GL κ ℂ) : Matrix κ κ ℂ) ∈ unitaryGroup κ ℂ := by
  by_cases ht : t' = t
  · subst ht; rwa [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne ht, Units.val_one]; exact one_mem _

theorem diagInvAt_mem_unitaryGroup (k : κ) (u : ℂˣ) (hu : (u : ℂ) * star (u : ℂ) = 1) :
    ((diagInvAt k u : GL κ ℂ) : Matrix κ κ ℂ) ∈ unitaryGroup κ ℂ := by
  rw [mem_unitaryGroup_iff]
  change diagonal _ * star (diagonal _) = 1
  rw [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; ext i
  by_cases h : i = k
  · subst h
    simp only [Function.update_self, Pi.star_apply, Units.val_inv_eq_inv_val, star_inv₀, Pi.one_apply]
    rw [← mul_inv, hu, inv_one]
  · simp [h]

def unitaryGL (M : Matrix κ κ ℂ) (h : M * star M = 1) : GL κ ℂ :=
  ⟨M, star M, h, (mul_eq_one_comm_of_card_eq κ κ ℂ rfl).mp h⟩

end Unitary

section Main
variable {T : Type*} [DecidableEq T] {p q : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem colLie_diag_mem_of_unitary (W : Submodule ℂ (Poly ℂ T p q κ))
    (hW : ∀ g : T → GL κ ℂ, (∀ t, (g t : Matrix κ κ ℂ) ∈ unitaryGroup κ ℂ) →
      ∀ w ∈ W, colActHom g w ∈ W) (t : T) (k : κ) {w : Poly ℂ T p q κ} (hw : w ∈ W) :
    colLie ℂ p q t k k w ∈ W := by
  have := sum_smul_mem_of_sum_zpow_smul_mem_on W infinite_unit_circle
    (fun u (hu : u * star u = 1) h0 => by rw [h0, zero_mul] at hu; exact zero_ne_one hu)
    w.support (fun m => colWeight m t k) (fun m => monomial m (coeff m w)) (fun u hu => by
      have hu0 : u ≠ 0 := fun h0 => by
        rw [Set.mem_setOf_eq, h0, zero_mul] at hu; exact zero_ne_one hu
      have := hW (Pi.mulSingle t (diagInvAt k (Units.mk0 u hu0)))
        (mulSingle_mem_unitaryGroup t _ (diagInvAt_mem_unitaryGroup k _ hu)) w hw
      rw [w.as_sum, map_sum] at this
      simpa only [colActHom_diagInvAt_monomial, Units.val_zpow_eq_zpow_val, Units.val_mk0] using this)
    Int.cast
  rw [w.as_sum, map_sum]
  simpa only [colLie_monomial] using this

theorem colDerM_mem_of_conj (W : Submodule ℂ (Poly ℂ T p q κ))
    (hW : ∀ g : T → GL κ ℂ, (∀ t, (g t : Matrix κ κ ℂ) ∈ unitaryGroup κ ℂ) →
      ∀ w ∈ W, colActHom g w ∈ W) (t : T) (g₀ : GL κ ℂ)
    (hg₀ : (g₀ : Matrix κ κ ℂ) ∈ unitaryGroup κ ℂ) (X : Matrix κ κ ℂ)
    (hX : ∀ w ∈ W, colDerM t X w ∈ W) :
    ∀ w ∈ W, colDerM t ((g₀ : Matrix κ κ ℂ) * X * ((g₀⁻¹ : GL κ ℂ) : Matrix κ κ ℂ)) w ∈ W := by
  intro w hw
  have hgu := mulSingle_mem_unitaryGroup t g₀ hg₀
  have hginv : ∀ t', ((((Pi.mulSingle t g₀ : T → GL κ ℂ)⁻¹) t' : GL κ ℂ) : Matrix κ κ ℂ) ∈ unitaryGroup κ ℂ :=
    fun t' => by rw [Pi.inv_apply]; exact inv_mem_unitaryGroup _ (hgu t')
  have h1 := hW _ hginv w hw
  have h2 := hW _ hgu _ (hX _ h1)
  have e : colActHom (p := p) (q := q) (Pi.mulSingle t g₀) (colActHom (Pi.mulSingle t g₀ : T → GL κ ℂ)⁻¹ w) = w := by
    rw [← AlgHom.comp_apply, ← colActHom_mul, mul_inv_cancel, colActHom_one, AlgHom.id_apply]
  rw [colActHom_colDerM, e, Pi.mulSingle_eq_same] at h2
  exact h2

end Main
end GlobalTheory.Harm

namespace GlobalTheory.Harm

theorem colLie_mem_of_unitary_stable : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {p q n : ℕ}
    (W : Submodule ℂ (GlobalTheory.Harm.Poly ℂ ι p q (Fin n))),
    (∀ g : ι → GL (Fin n) ℂ, (∀ t, (g t : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) →
      ∀ w ∈ W, GlobalTheory.Harm.colActHom g w ∈ W) →
    ∀ (t : ι) (k l : Fin n), ∀ w ∈ W, GlobalTheory.Harm.colLie ℂ p q t k l w ∈ W := by
  intro ι _ _ p q n W hW t k l w hw
  let S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    { carrier := {X | ∀ w ∈ W, colDerM (p := p) (q := q) t X w ∈ W}
      add_mem' := fun {X Y} hX hY w hw => by
        rw [Set.mem_setOf_eq] at hX hY
        rw [colDerM_add, Derivation.add_apply]; exact W.add_mem (hX w hw) (hY w hw)
      zero_mem' := fun w _ => by
        have : colDerM (p := p) (q := q) t (0 : Matrix (Fin n) (Fin n) ℂ) =
            (0 : ℂ) • colDerM t 0 := by rw [← colDerM_smul, zero_smul]
        rw [this, zero_smul, Derivation.zero_apply]; exact W.zero_mem
      smul_mem' := fun c X hX w hw => by
        rw [Set.mem_setOf_eq] at hX
        rw [colDerM_smul, Derivation.smul_apply]; exact W.smul_mem c (hX w hw) }
  have hdiag : ∀ m : Fin n, single m m (1 : ℂ) ∈ S := fun m w hw => by
    rw [colDerM_single]; exact colLie_diag_mem_of_unitary W hW t m hw
  have hconj : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (hM : M * star M = 1) (X : Matrix (Fin n) (Fin n) ℂ),
      X ∈ S → M * X * star M ∈ S := fun M hM X hX =>
    colDerM_mem_of_conj W hW t (unitaryGL M hM) (mem_unitaryGroup_iff.mpr hM) X hX
  change colDer ℂ p q t k l w ∈ W
  rw [← colDerM_single]
  revert w
  change single l k (1 : ℂ) ∈ S
  by_cases hkl : k = l
  · subst hkl; exact hdiag k
  have hA := hconj (blockMat k l (3/5) (4/5) (-4/5))
    (blockMat_mul_star hkl (by simp [Complex.ext_iff]; norm_num) (by simp [Complex.ext_iff]; norm_num)
      (by simp [Complex.ext_iff]; norm_num)) _ (hdiag k)
  have hB := hconj (blockMat k l (3/5) (4/5 * Complex.I) (4/5 * Complex.I))
    (blockMat_mul_star hkl (by simp [Complex.ext_iff]; norm_num) (by simp [Complex.ext_iff]; norm_num)
      (by simp [Complex.ext_iff]; norm_num)) _ (hdiag k)
  rw [blockMat_conj_single hkl] at hA hB
  have key : single l k (1 : ℂ) =
      (25 / 24 : ℂ) • ((3 / 5 * star (3 / 5 : ℂ)) • single k k (1 : ℂ) + (3 / 5 * star (4 / 5 : ℂ)) • single k l 1 +
        (4 / 5 * star (3 / 5 : ℂ)) • single l k 1 + (4 / 5 * star (4 / 5 : ℂ)) • single l l 1) -
      (3 / 8 : ℂ) • single k k 1 - (2 / 3 : ℂ) • single l l 1 -
      (25 / 24 * Complex.I) • ((3 / 5 * star (3 / 5 : ℂ)) • single k k (1 : ℂ) +
        (3 / 5 * star (4 / 5 * Complex.I)) • single k l 1 +
        (4 / 5 * Complex.I * star (3 / 5 : ℂ)) • single l k 1 +
        (4 / 5 * Complex.I * star (4 / 5 * Complex.I)) • single l l 1) +
      (3 / 8 * Complex.I) • single k k 1 + (2 / 3 * Complex.I) • single l l 1 := by
    match_scalars <;> simp [Complex.ext_iff] <;> norm_num
  rw [key]
  exact S.add_mem (S.add_mem (S.sub_mem (S.sub_mem (S.sub_mem (S.smul_mem _ hA) (S.smul_mem _ (hdiag k)))
    (S.smul_mem _ (hdiag l))) (S.smul_mem _ hB)) (S.smul_mem _ (hdiag k))) (S.smul_mem _ (hdiag l))

end GlobalTheory.Harm
