import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem rowGen_X (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    rowGen R a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  rw [rowGen, aeval_X]

theorem rowGen_lpMinor (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (hab : a < b)
    (m : ℕ) (hr : m ≤ r) (hn : m ≤ n) :
    rowGen R a b (lpMinor R m hr hn) = Polynomial.C (lpMinor R m hr hn) := by
  classical
  unfold lpMinor
  rw [AlgHom.map_det, RingHom.map_det]
  set N : Matrix (Fin m) (Fin m) (MvPolynomial (Fin r × Fin n) R) :=
    Matrix.of fun p q : Fin m => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)
    with hN
  by_cases hb : b.val < m
  · have ha : a.val < m := lt_trans hab hb
    set i : Fin m := ⟨b.val, hb⟩ with hi
    set j : Fin m := ⟨a.val, ha⟩ with hj
    have hij : i ≠ j := by
      intro h
      have := congrArg Fin.val h
      simp [hi, hj] at this
      exact absurd this (Fin.val_ne_of_ne (ne_of_lt hab)).symm
    have hM : (rowGen R a b).toRingHom.mapMatrix N =
        Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N) i
          (((Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N) i +
            (Polynomial.X : Polynomial (MvPolynomial (Fin r × Fin n) R)) • ((Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N) j) := by
      ext p q
      by_cases hp : p = i
      · subst hp
        have h1 : Fin.castLE hr i = b := Fin.ext (by simp [hi])
        have h2 : Fin.castLE hr j = a := Fin.ext (by simp [hj])
        simp [hN, Matrix.updateRow_apply, rowGen_X, h1, h2, smul_eq_mul]
      · have h1 : Fin.castLE hr p ≠ b := by
          intro h
          apply hp
          exact Fin.ext (by have := congrArg Fin.val h; simpa [hi] using this)
        simp [hN, Matrix.updateRow_apply, rowGen_X, h1, hp]
    change ((rowGen R a b).toRingHom.mapMatrix N).det = _
    rw [hM, Matrix.det_updateRow_add_smul_self _ hij]
  · have hM : (rowGen R a b).toRingHom.mapMatrix N =
        (Polynomial.C : MvPolynomial (Fin r × Fin n) R →+* _).mapMatrix N := by
      ext p q
      have h1 : Fin.castLE hr p ≠ b := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [hN, rowGen_X, h1]
    change ((rowGen R a b).toRingHom.mapMatrix N).det = _
    rw [hM]

theorem rowGen_hw (R : Type*) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (a b : Fin r) (hab : a < b) :
    rowGen R a b (hw R hn ν) = Polynomial.C (hw R hn ν) := by
  simp only [hw, map_prod, map_pow, rowGen_lpMinor R a b hab]

theorem highestWeightVectorRaising : HWRaise := by
  intro R _ r n hn ν a b k hab hk
  unfold rowDiv
  rw [rowGen_hw R hn ν a b hab, Polynomial.coeff_C, if_neg (by omega)]

end Formalism.GradedWeylDivisibility
