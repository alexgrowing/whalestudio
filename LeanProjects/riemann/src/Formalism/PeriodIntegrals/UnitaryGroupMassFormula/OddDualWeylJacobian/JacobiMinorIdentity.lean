import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacRev

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl.Jac

theorem block {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A B : Matrix (m ⊕ n) (m ⊕ n) R) (d : R)
    (h : B * A = d • (1 : Matrix (m ⊕ n) (m ⊕ n) R)) :
    B.toBlocks₂₂.det * A.det = d ^ Fintype.card n * A.toBlocks₁₁.det := by
  have hX : (fromBlocks (1 : Matrix m m R) 0 B.toBlocks₂₁ B.toBlocks₂₂) * A =
      fromBlocks A.toBlocks₁₁ A.toBlocks₁₂ 0 (d • (1 : Matrix n n R)) := by
    ext i j
    have hij := congrFun (congrFun h i) j
    rcases i with i | i <;> rcases j with j | j <;>
      first
      | (simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toBlocks₁₁,
          Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]; done)
      | (simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toBlocks₁₁,
          Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂] at hij ⊢; exact hij)
  have hdet := congrArg Matrix.det hX
  simp only [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, det_one, det_smul, one_mul,
    mul_one] at hdet
  linear_combination hdet

theorem det_sub {R : Type*} [CommRing R] {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eI eJ : ι ≃ Fin k) (A : Matrix (Fin k) (Fin k) R) :
    (A.submatrix eI eJ).det = ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det := by
  have h1 : A.submatrix eI eJ = (A.submatrix eI eI).submatrix id (eJ.trans eI.symm) := by
    ext i j
    simp
  rw [h1]
  rw [det_permute', det_submatrix_equiv_self]

theorem sign_sq {R : Type*} [CommRing R] (u : ℤˣ) : ((u : ℤ) : R) * ((u : ℤ) : R) = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

private theorem mapMatrix_eval_generic_eq {R : Type*} [CommRing R] {k : ℕ} (A : Matrix (Fin k) (Fin k) R) :
    (MvPolynomial.eval₂Hom (Int.castRingHom R) fun p : Fin k × Fin k => A p.1 p.2).mapMatrix
      (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin k × Fin k) ℤ)) = A := by
  ext i j
  simp

private theorem det_generic_int_ne_zero (k : ℕ) :
    (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin k × Fin k) ℤ)).det ≠ 0 := by
  intro h
  have h1 := congrArg
    (MvPolynomial.eval₂Hom (Int.castRingHom ℤ)
      fun p : Fin k × Fin k => (1 : Matrix (Fin k) (Fin k) ℤ) p.1 p.2) h
  rw [RingHom.map_det, mapMatrix_eval_generic_eq (1 : Matrix (Fin k) (Fin k) ℤ), det_one, map_zero] at h1
  exact one_ne_zero h1

private theorem det_toBlocks22_adjugate_submatrix_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {k : ℕ} {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Nonempty n]
    (eI eJ : m ⊕ n ≃ Fin k) (A : Matrix (Fin k) (Fin k) R) (hA : A.det ≠ 0) :
    ((adjugate A).submatrix eJ eI).toBlocks₂₂.det =
      ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det ^ (Fintype.card n - 1) *
        (A.submatrix eI eJ).toBlocks₁₁.det := by
  have hBA : (adjugate A).submatrix eJ eI * A.submatrix eI eJ =
      A.det • (1 : Matrix (m ⊕ n) (m ⊕ n) R) := by
    rw [submatrix_mul_equiv, adjugate_mul]
    ext i j
    simp [Matrix.one_apply]
  have key := block (A.submatrix eI eJ) ((adjugate A).submatrix eJ eI) A.det hBA
  rw [det_sub] at key
  have hs2 := sign_sq (R := R) (Equiv.Perm.sign (eJ.trans eI.symm))
  have hpow : A.det ^ Fintype.card n = A.det * A.det ^ (Fintype.card n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Fintype.card_pos (α := n))]
  have h2 : A.det * (((adjugate A).submatrix eJ eI).toBlocks₂₂.det *
      ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R)) =
      A.det * (A.det ^ (Fintype.card n - 1) * (A.submatrix eI eJ).toBlocks₁₁.det) := by
    linear_combination key + (A.submatrix eI eJ).toBlocks₁₁.det * hpow
  have h3 := mul_left_cancel₀ hA h2
  linear_combination ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * h3 -
    ((adjugate A).submatrix eJ eI).toBlocks₂₂.det * hs2

theorem jacobi {R : Type*} [CommRing R] {k : ℕ} {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Nonempty n] (eI eJ : m ⊕ n ≃ Fin k)
    (A : Matrix (Fin k) (Fin k) R) :
    ((adjugate A).submatrix eJ eI).toBlocks₂₂.det =
      ((Equiv.Perm.sign (eJ.trans eI.symm) : ℤ) : R) * A.det ^ (Fintype.card n - 1) *
        (A.submatrix eI eJ).toBlocks₁₁.det := by
  obtain ⟨G, hG0, φ, hφG⟩ : ∃ G : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) ℤ),
      G.det ≠ 0 ∧ ∃ φ : MvPolynomial (Fin k × Fin k) ℤ →+* R, φ.mapMatrix G = A :=
    ⟨_, det_generic_int_ne_zero k, _, mapMatrix_eval_generic_eq A⟩
  have hcore := det_toBlocks22_adjugate_submatrix_of_det_ne_zero eI eJ G hG0
  have hadj : φ.mapMatrix (adjugate G) = adjugate A := by
    rw [RingHom.map_adjugate, hφG]
  have e1 : φ.mapMatrix (((adjugate G).submatrix eJ eI).toBlocks₂₂) =
      ((adjugate A).submatrix eJ eI).toBlocks₂₂ := by
    ext i j
    exact congrFun (congrFun hadj (eJ (Sum.inr i))) (eI (Sum.inr j))
  have e2 : φ.mapMatrix ((G.submatrix eI eJ).toBlocks₁₁) = (A.submatrix eI eJ).toBlocks₁₁ := by
    ext i j
    exact congrFun (congrFun hφG (eI (Sum.inl i))) (eJ (Sum.inl j))
  have h := congrArg φ hcore
  simp only [map_mul, map_pow, map_intCast, RingHom.map_det, hφG, e1, e2] at h
  exact h

end PI.OddDualWeyl.Jac

namespace PI.OddDualWeyl.Jac

def mkE {a b k : ℕ} (f : Fin a → Fin k) (g : Fin b → Fin k) (h : a + b = k)
    (hf : Function.Injective f) (hg : Function.Injective g) (hfg : ∀ x y, f x ≠ g y) :
    Fin a ⊕ Fin b ≃ Fin k :=
  Equiv.ofBijective (Sum.elim f g) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hf.sumElim hg hfg, by simp [h]⟩)

def eR (k s : ℕ) (hs : s + 1 ≤ k) : Fin (k - 1 - s) ⊕ Fin (s + 1) ≃ Fin k :=
  mkE (a := k - 1 - s) (b := s + 1) (fun x => Fin.castLE (Nat.sub_le _ _ |>.trans (Nat.sub_le _ _)) x) (fun y => Fin.rev (Fin.castLE hs y)) (by omega)
    (Fin.castLE_injective _) (Fin.rev_injective.comp (Fin.castLE_injective _))
    (by
      intro x y h
      have h1 := congrArg Fin.val h
      have := x.isLt; have := y.isLt
      simp [Fin.val_rev] at h1; omega)

def eL (k s : ℕ) (hs : s + 1 ≤ k) : Fin (k - 1 - s) ⊕ Fin (s + 1) ≃ Fin k :=
  mkE (a := k - 1 - s) (b := s + 1) (fun x => Fin.rev (Fin.castLE (Nat.sub_le _ _ |>.trans (Nat.sub_le _ _)) x)) (fun y => Fin.castLE hs y) (by omega)
    (Fin.rev_injective.comp (Fin.castLE_injective _)) (Fin.castLE_injective _)
    (by
      intro x y h
      have h1 := congrArg Fin.val h
      have := x.isLt; have := y.isLt
      simp [Fin.val_rev] at h1; omega)

theorem dualSub_pMinor (R : Type*) [CommRing R] {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : ℕ)
    (hs : s ≤ k) :
    dualSub R k (pMinor R σ s hs) =
      (Matrix.of fun p q : Fin s =>
        adjugate (genM R k) (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p))).det := by
  rw [PI.OddDualWeyl.dualSub, PI.OddDualWeyl.pMinor, AlgHom.map_det]
  exact congrArg Matrix.det (Matrix.ext fun p q => by simp [PI.OddDualWeyl.dualM])

theorem sign_pm (R : Type*) [CommRing R] (u : ℤˣ) :
    ((u : ℤ) : R) = 1 ∨ ((u : ℤ) : R) = -1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

end PI.OddDualWeyl.Jac

namespace PI.OddDualWeyl

open Jac in
theorem jacobiMinorReverse : JacRev := by
  unfold JacRev
  intro R _ k s hs
  refine ⟨((Equiv.Perm.sign ((PI.OddDualWeyl.Jac.eR k s hs).trans (PI.OddDualWeyl.Jac.eR k s hs).symm) : ℤ) : R),
    PI.OddDualWeyl.Jac.sign_pm R _, ?_⟩
  calc dualSub R k (pMinor R Fin.revPerm (s + 1) hs)
      = (Matrix.of fun p q : Fin (s + 1) => adjugate (genM R k) (Fin.rev (Fin.castLE hs q))
          ((Fin.revPerm : Equiv.Perm (Fin k)) (Fin.castLE hs p))).det :=
        PI.OddDualWeyl.Jac.dualSub_pMinor R Fin.revPerm (s + 1) hs
    _ = (((adjugate (genM R k)).submatrix (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs)).toBlocks₂₂)ᵀ.det :=
        congrArg Matrix.det (Matrix.ext fun p q => rfl)
    _ = ((adjugate (genM R k)).submatrix (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs)).toBlocks₂₂.det :=
        det_transpose _
    _ = ((Equiv.Perm.sign ((PI.OddDualWeyl.Jac.eR k s hs).trans (PI.OddDualWeyl.Jac.eR k s hs).symm) : ℤ) :
          MvPolynomial (Fin k × Fin k) R) * (genM R k).det ^ (Fintype.card (Fin (s + 1)) - 1) *
          ((genM R k).submatrix (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs)).toBlocks₁₁.det :=
        PI.OddDualWeyl.Jac.jacobi (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs) (genM R k)
    _ = C (((Equiv.Perm.sign ((PI.OddDualWeyl.Jac.eR k s hs).trans (PI.OddDualWeyl.Jac.eR k s hs).symm) : ℤ) : R)) *
          (genM R k).det ^ s * pMinor R 1 (k - 1 - s) (by omega) := by
        rw [map_intCast, Fintype.card_fin, Nat.add_sub_cancel, pMinor]
        all_goals rfl

end PI.OddDualWeyl
