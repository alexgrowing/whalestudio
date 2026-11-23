import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory

theorem isUnit_det_sub_smul_one_of_forall_not_isUnit {C : Type} [CommRing C] [IsLocalRing C]
    {n : Type} [Fintype n] [DecidableEq n] (Q : Matrix n n C) (hQ : ∀ i j, ¬ IsUnit (Q i j))
    (c : C) (hc : IsUnit c) : IsUnit (Q - c • (1 : Matrix n n C)).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hm : (IsLocalRing.residue C).mapMatrix (Q - c • (1 : Matrix n n C)) =
      (-(IsLocalRing.residue C c)) • (1 : Matrix n n _) := by
    ext i j
    have hq : IsLocalRing.residue C (Q i j) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 (hQ i j))
    by_cases h : i = j
    · subst h; simp [hq]
    · simp [hq, h]
  rw [hm, Matrix.det_smul, Matrix.det_one, mul_one]
  refine pow_ne_zero _ (neg_ne_zero.2 ?_)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hc

theorem exists_GL_conj_eq_diagonal_of_charpoly_eq_prod :
    ∀ {C : Type} [CommRing C] [IsLocalRing C] (A : Matrix (Fin 3) (Fin 3) C) (p : Fin 3 → C),
      (∀ a b, a ≠ b → IsUnit (p a - p b)) → A.charpoly = ∏ a, (X - Polynomial.C (p a)) →
      ∃ h : GL (Fin 3) C, (h : Matrix (Fin 3) (Fin 3) C) * A *
        ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) = Matrix.diagonal p := by
  intro C _ _ A p hp hchar
  classical
  set P : Fin 3 → C[X] := fun a => ∏ b ∈ Finset.univ.erase a, (X - Polynomial.C (p b)) with hPdef
  have hfull : ∀ a, (X - Polynomial.C (p a)) * P a = ∏ b, (X - Polynomial.C (p b)) := fun a =>
    Finset.mul_prod_erase _ (fun b => X - Polynomial.C (p b)) (Finset.mem_univ a)
  have hz : aeval A (∏ b, (X - Polynomial.C (p b))) = 0 := by
    rw [← hchar]; exact Matrix.aeval_self_charpoly A
  have hsplit : ∀ (f : C[X]) a, f = Polynomial.C (f.eval (p a)) +
      (X - Polynomial.C (p a)) * (f /ₘ (X - Polynomial.C (p a))) := by
    intro f a
    have h := modByMonic_add_div f (X - Polynomial.C (p a))
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    exact h.symm
  have key : ∀ (f : C[X]) a, aeval A (f * P a) = f.eval (p a) • aeval A (P a) := by
    intro f a
    conv_lhs => rw [hsplit f a]
    rw [add_mul, mul_comm (X - Polynomial.C (p a)), mul_assoc, hfull]
    simp only [map_add, map_mul, hz, mul_zero, add_zero, aeval_C, Algebra.smul_def]
  have hq : ∀ a, IsUnit ((P a).eval (p a)) := by
    intro a
    simp only [hPdef, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
      (fun b hb => hp a b (Finset.ne_of_mem_erase hb).symm)
  have hq0 : ∀ a b, a ≠ b → (P a).eval (p b) = 0 := by
    intro a b hab
    simp only [hPdef, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩) (sub_self _)
  have hBA : ∀ a, aeval A (P a) * A = p a • aeval A (P a) := by
    intro a
    have h := key X a
    rwa [mul_comm, map_mul, aeval_X, eval_X] at h
  have hBB : ∀ a b, aeval A (P a) * aeval A (P b) = (P a).eval (p b) • aeval A (P b) := by
    intro a b
    rw [← map_mul]
    exact key (P a) b
  have hex : ∀ a, ∃ i j, IsUnit (aeval A (P a) i j) := by
    intro a
    by_contra hne
    push_neg at hne
    obtain ⟨u, hu⟩ := hq a
    set E := ((u⁻¹ : Cˣ) : C) • aeval A (P a) with hE
    have hEn : ∀ i j, ¬ IsUnit (E i j) := by
      intro i j h
      apply hne i j
      have h' : aeval A (P a) i j = (u : C) * E i j := by
        rw [hE, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, Units.mul_inv, one_mul]
      rw [h']
      exact (Units.isUnit u).mul h
    have hEE : E * E = E := by
      rw [hE, Matrix.smul_mul, Matrix.mul_smul, hBB, ← hu, smul_smul, smul_smul,
        mul_assoc, Units.inv_mul, mul_one]
    have hdet := isUnit_det_sub_smul_one_of_forall_not_isUnit E hEn 1 isUnit_one
    rw [one_smul] at hdet
    have hE0 : E = 0 := by
      have h1 : (E - 1) * E = 0 := by rw [sub_mul, hEE, one_mul, sub_self]
      obtain ⟨w, hw⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
      calc E = ((w⁻¹ : (Matrix (Fin 3) (Fin 3) C)ˣ) : Matrix (Fin 3) (Fin 3) C) * ((E - 1) * E) := by
            rw [← mul_assoc, ← hw, Units.inv_mul, one_mul]
        _ = 0 := by rw [h1, mul_zero]
    have hB0 : aeval A (P a) = 0 := by
      have h' : aeval A (P a) = (u : C) • E := by rw [hE, smul_smul, Units.mul_inv, one_smul]
      rw [h', hE0, smul_zero]
    have hs := congrArg (aeval A) (hsplit (P a) a)
    rw [hB0, map_add, aeval_C, map_mul, ← hu] at hs
    have hinv : aeval A (X - Polynomial.C (p a)) *
        (-(((u⁻¹ : Cˣ) : C) • aeval A (P a /ₘ (X - Polynomial.C (p a))))) = 1 := by
      have h2 : aeval A (X - Polynomial.C (p a)) * aeval A (P a /ₘ (X - Polynomial.C (p a))) =
          -algebraMap C _ (u : C) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hs.symm
      rw [mul_neg, Matrix.mul_smul, h2, smul_neg, neg_neg, Algebra.smul_def, ← map_mul,
        Units.inv_mul, map_one]
    have hdx : IsUnit (aeval A (X - Polynomial.C (p a))).det :=
      IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, hinv, Matrix.det_one])
    have hev : A.charpoly.eval (p a) = 0 := by
      rw [hchar, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
    rw [Matrix.eval_charpoly] at hev
    have hneg : Matrix.scalar (Fin 3) (p a) - A = -(aeval A (X - Polynomial.C (p a))) := by
      simp [Algebra.algebraMap_eq_smul_one, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hneg, Matrix.det_neg] at hev
    have hu2 : IsUnit ((-1 : C) ^ Fintype.card (Fin 3) * (aeval A (X - Polynomial.C (p a))).det) :=
      ((isUnit_neg_one).pow _).mul hdx
    rw [hev] at hu2
    exact not_isUnit_zero hu2
  choose i j hij using hex
  let H : Matrix (Fin 3) (Fin 3) C := Matrix.of fun a k => aeval A (P a) (i a) k
  let Q : Matrix (Fin 3) (Fin 3) C := Matrix.of fun k b => aeval A (P b) k (j b)
  have hHQ : H * Q = Matrix.diagonal fun a => (P a).eval (p a) * aeval A (P a) (i a) (j a) := by
    ext a b
    have h' : (H * Q) a b = (aeval A (P a) * aeval A (P b)) (i a) (j b) := by
      simp [H, Q, Matrix.mul_apply]
    rw [h', hBB, Matrix.smul_apply, smul_eq_mul]
    by_cases hab : a = b
    · subst hab; simp
    · rw [hq0 a b hab, zero_mul, Matrix.diagonal_apply_ne _ hab]
  have hdetH : IsUnit H.det := by
    have h2 : IsUnit (H * Q).det := by
      rw [hHQ, Matrix.det_diagonal]
      exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
        (fun a _ => (hq a).mul (hij a))
    rw [Matrix.det_mul] at h2
    exact isUnit_of_mul_isUnit_left h2
  have hHA : H * A = Matrix.diagonal p * H := by
    ext a k
    have h' : (H * A) a k = (aeval A (P a) * A) (i a) k := by simp [H, Matrix.mul_apply]
    rw [h', hBA, Matrix.diagonal_mul]
    simp [H]
  have hU := (Matrix.isUnit_iff_isUnit_det H).2 hdetH
  refine ⟨hU.unit, ?_⟩
  rw [IsUnit.unit_spec, hHA, mul_assoc, hU.mul_val_inv, mul_one]

end GlobalTheory
