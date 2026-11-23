import Formalism.LocalToGlobal.GlobalTheory.GL4.ColAddGenCastSuccRename
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.XiNorm
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility

theorem hw_add_const (R : Type) [CommRing R] {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ) :
    hw R (r := m + 1) (n := m + 1) le_rfl (fun s => ν s + c) =
      hw R (r := m + 1) (n := m + 1) le_rfl ν * lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c := by
  unfold hw
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]
  congr 1
  · apply Finset.prod_congr rfl
    intro s _
    congr 1
    unfold nuNext
    have h : (s.castSucc : Fin (m + 1)).val + 1 < m + 1 := by simp only [Fin.val_castSucc]; omega
    rw [dif_pos h, dif_pos h]
    dsimp only
    omega
  · have h : ¬ ((Fin.last m : Fin (m + 1)).val + 1 < m + 1) := by simp
    unfold nuNext
    rw [dif_neg h, dif_neg h]
    dsimp only
    rw [Nat.sub_zero, Nat.sub_zero, pow_add]
    rfl

theorem rowGen_det (R : Type) [CommRing R] {m : ℕ} (a b : Fin m) (hab : a ≠ b) :
    rowGen R a b (lpMinor R (r := m) (n := m) m le_rfl le_rfl) =
      Polynomial.C (lpMinor R (r := m) (n := m) m le_rfl le_rfl) := by
  unfold lpMinor
  set M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) R) :=
    Matrix.of fun p q : Fin m => X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) with hMdef
  rw [AlgHom.map_det, RingHom.map_det]
  have hM : (rowGen R a b).mapMatrix M =
      Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) b
        (((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) b +
          (Polynomial.X : Polynomial (MvPolynomial (Fin m × Fin m) R)) •
            ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a) := by
    ext p q
    by_cases hp : p = b
    · subst hp
      simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl]
      try ring
    · simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl, hp]
  rw [hM, Matrix.det_updateRow_add_smul_self _ (Ne.symm hab)]

theorem rowDiv_det_mul (R : Type) [CommRing R] {m : ℕ} (a b : Fin m) (hab : a ≠ b) (k c : ℕ)
    (f : MvPolynomial (Fin m × Fin m) R) :
    rowDiv R a b k (lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * f) =
      lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * rowDiv R a b k f := by
  unfold rowDiv
  rw [map_mul, map_pow, rowGen_det R a b hab, ← Polynomial.C_pow, Polynomial.coeff_C_mul]

theorem rowGen_det_self (R : Type) [CommRing R] {m : ℕ} (a : Fin m) :
    rowGen R a a (lpMinor R (r := m) (n := m) m le_rfl le_rfl) =
      (1 + Polynomial.X) * Polynomial.C (lpMinor R (r := m) (n := m) m le_rfl le_rfl) := by
  unfold lpMinor
  set M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) R) :=
    Matrix.of fun p q : Fin m => X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) with hMdef
  rw [AlgHom.map_det, RingHom.map_det]
  have hM : (rowGen R a a).mapMatrix M =
      Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a
        ((1 + Polynomial.X : Polynomial (MvPolynomial (Fin m × Fin m) R)) •
            ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a) := by
    refine Matrix.ext fun p q => ?_
    by_cases hp : p = a
    · subst hp
      simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl]
      try ring
    · simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl, hp]
  rw [hM, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]

theorem rowDiv_det_mul_self (R : Type) [CommRing R] {m : ℕ} (a : Fin m) (k c : ℕ)
    (f : MvPolynomial (Fin m × Fin m) R) :
    rowDiv R a a k (lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * f) =
      lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c *
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, ((c.choose p.1 : ℕ) : MvPolynomial (Fin m × Fin m) R) * rowDiv R a a p.2 f := by
  unfold rowDiv
  rw [map_mul, map_pow, rowGen_det_self, mul_pow, ← Polynomial.C_pow, mul_comm ((1 + Polynomial.X) ^ c) _,
    mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [add_comm (1 : Polynomial (MvPolynomial (Fin m × Fin m) R)), Polynomial.coeff_X_add_one_pow]

theorem rowDiv_add (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  unfold rowDiv
  rw [map_add, Polynomial.coeff_add]

theorem rowDiv_smul (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (t : R) (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (t • f) = t • rowDiv R a b k f := by
  unfold rowDiv
  rw [map_smul, Polynomial.coeff_smul]

theorem rowDiv_zero (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) :
    rowDiv R a b k (0 : MvPolynomial (Fin r × Fin n) R) = 0 := by
  unfold rowDiv
  rw [map_zero, Polynomial.coeff_zero]

theorem rowDiv_mem_weyl (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) : rowDiv R a b k f ∈ weyl R r n hn ν := by
  unfold weyl at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  | zero => rw [rowDiv_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [rowDiv_add]; exact Submodule.add_mem _ hx hy
  | smul t x _ hx => rw [rowDiv_smul]; exact Submodule.smul_mem _ t hx

theorem det_mul_mem_weyl (R : Type) [CommRing R] {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ)
    (g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) (hg : g ∈ weyl R (m + 1) (m + 1) le_rfl ν) :
    lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * g ∈
      weyl R (m + 1) (m + 1) le_rfl (fun s => ν s + c) := by
  set D := lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c with hD
  set W' := weyl R (m + 1) (m + 1) le_rfl (fun s => ν s + c) with hW'
  have key : ∀ w : List (Fin (m + 1) × Fin (m + 1) × ℕ), D * applyWord R w (hw R le_rfl ν) ∈ W' := by
    intro w
    induction w with
    | nil =>
      simp only [applyWord, List.foldr_nil]
      rw [hD, mul_comm, ← hw_add_const]
      exact Submodule.subset_span ⟨[], rfl⟩
    | cons x w ih =>
      obtain ⟨a, b, k⟩ := x
      show D * rowDiv R a b k (applyWord R w (hw R le_rfl ν)) ∈ W'
      set g := applyWord R w (hw R le_rfl ν)
      by_cases hab : a = b
      · subst hab
        induction k using Nat.strong_induction_on with
        | _ k ihk =>
          have h1 := rowDiv_det_mul_self R a k c g
          have hmem : ((0 : ℕ), k) ∈ Finset.HasAntidiagonal.antidiagonal k := by simp
          rw [← Finset.add_sum_erase _ _ hmem] at h1
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at h1
          have h2 : D * rowDiv R a a k g = rowDiv R a a k (D * g) -
              ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).erase (0, k),
                D * (((c.choose p.1 : ℕ) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) * rowDiv R a a p.2 g) := by
            rw [hD, h1, mul_add, Finset.mul_sum]
            ring
          rw [h2]
          refine Submodule.sub_mem _ (rowDiv_mem_weyl R le_rfl _ a a k _ ih) ?_
          refine Submodule.sum_mem _ fun p hp => ?_
          have hp2 : p.2 < k := by
            rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
            have hne : p.1 ≠ 0 := fun h => hp.1 (Prod.ext h (by simp; omega))
            omega
          rw [mul_left_comm, ← nsmul_eq_mul]
          exact Submodule.smul_of_tower_mem _ _ (ihk p.2 hp2)
      · rw [← rowDiv_det_mul R a b hab]
        exact rowDiv_mem_weyl R le_rfl _ a b k _ ih
  unfold weyl at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact key w
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul t x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ t hx

theorem initMinor_id_eq_lpMinor (R : Type) [CommRing R] (m : ℕ) :
    initMinor R (r := m) (n := m) (s := m) id le_rfl = lpMinor R (r := m) (n := m) m le_rfl le_rfl := by
  unfold initMinor lpMinor
  congr 1

theorem xnN_det_mul {m : ℕ} (ν : Fin (m + 1) → ℕ) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℂ)
    (hf : f ∈ dualWeyl ℂ (m + 1) (m + 1) ν) :
    Formalism.BranchingDeterminantCap.xnN (lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl * f) =
      Formalism.BranchingDeterminantCap.xnC (m + 1) (Formalism.BranchingDeterminantCap.xnLam ν) (m + 1) * Formalism.BranchingDeterminantCap.xnN f := by
  rw [← initMinor_id_eq_lpMinor]
  apply Formalism.BranchingDeterminantCap.xn_L id Function.injective_id (Formalism.BranchingDeterminantCap.xnLam ν) f
  · intro t s hts
    exact Formalism.BranchingDeterminantCap.xn_hR hf t s hts
  · intro s
    have h := Formalism.BranchingDeterminantCap.xn_hW hf s
    have hs : Formalism.BranchingDeterminantCap.xnLam ν s.val = ν s := by
      unfold Formalism.BranchingDeterminantCap.xnLam
      rw [dif_pos s.isLt]
    rw [hs]
    exact h

theorem xnC_pos (M : ℕ) (mm : ℕ → ℕ) : 0 < Formalism.BranchingDeterminantCap.xnC M mm M := by
  unfold Formalism.BranchingDeterminantCap.xnC
  apply Finset.prod_pos
  intro q hq
  rw [Finset.mem_range] at hq
  have h1 : (q : ℝ) < M := by exact_mod_cast hq
  have h2 : (0 : ℝ) ≤ (mm q : ℝ) := Nat.cast_nonneg _
  linarith

def detConst {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ) : ℝ :=
  ∏ j ∈ Finset.range c, Formalism.BranchingDeterminantCap.xnC (m + 1) (Formalism.BranchingDeterminantCap.xnLam (fun s => ν s + j)) (m + 1)

theorem detConst_pos {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ) : 0 < detConst ν c :=
  Finset.prod_pos fun _ _ => xnC_pos _ _

theorem xnN_det_pow_mul {m : ℕ} (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (c : ℕ) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℂ)
    (hf : f ∈ weyl ℂ (m + 1) (m + 1) le_rfl ν) :
    Formalism.BranchingDeterminantCap.xnN (lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * f) = detConst ν c * Formalism.BranchingDeterminantCap.xnN f := by
  induction c with
  | zero => simp [detConst]
  | succ c ih =>
    have hmem : lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * f ∈
        dualWeyl ℂ (m + 1) (m + 1) (fun s => ν s + c) :=
      Formalism.GradedWeylDivisibility.weylLeDual ℂ (m + 1) (m + 1) le_rfl _ (fun a b h => Nat.add_le_add_right (hν h) c) (det_mul_mem_weyl ℂ ν c f hf)
    rw [pow_succ', mul_assoc, xnN_det_mul _ _ hmem, ih, detConst, detConst, Finset.prod_range_succ]
    ring

theorem fockF_self_eq {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f = ((Formalism.BranchingDeterminantCap.xnN f : ℝ) : ℂ) := by
  unfold Formalism.BranchingDeterminantCap.xnN
  rw [Formalism.GradedWeylDivisibility.LFockb_fockF_self, Complex.ofReal_re]

theorem fock_ratio_det_pow {m : ℕ} (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (c : ℕ) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℂ)
    (hf : f ∈ weyl ℂ (m + 1) (m + 1) le_rfl ν) :
    Formalism.REAL.fockF (lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * f)
              (lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * f) /
      Formalism.REAL.fockF (hw ℂ le_rfl (fun s => ν s + c)) (hw ℂ le_rfl (fun s => ν s + c)) =
    Formalism.REAL.fockF f f / Formalism.REAL.fockF (hw ℂ le_rfl ν) (hw ℂ le_rfl ν) := by
  have hhw : hw ℂ le_rfl ν ∈ weyl ℂ (m + 1) (m + 1) le_rfl ν := Submodule.subset_span ⟨[], rfl⟩
  rw [hw_add_const, mul_comm (hw ℂ le_rfl ν), fockF_self_eq, fockF_self_eq, fockF_self_eq, fockF_self_eq,
    xnN_det_pow_mul ν hν c f hf, xnN_det_pow_mul ν hν c _ hhw, ← Complex.ofReal_div, ← Complex.ofReal_div,
    mul_div_mul_left _ _ (detConst_pos ν c).ne']

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality
