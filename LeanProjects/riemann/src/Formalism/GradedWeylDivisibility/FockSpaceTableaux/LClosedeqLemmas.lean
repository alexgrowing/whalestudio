import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lclosedeq_rowGen_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowGen S a b (map φ f) = Polynomial.map (map φ) (rowGen R a b f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [map_C, rowGen, aeval_C, Polynomial.algebraMap_apply, algebraMap_eq, Polynomial.map_C]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add]
  | mul_X p v hp =>
    simp only [map_mul, map_X, hp, Polynomial.map_mul]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp [Polynomial.map_add, Polynomial.map_mul, map_X]

theorem lclosedeq_rowDiv_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv S a b k (map φ f) = map φ (rowDiv R a b k f) := by
  simp only [rowDiv, lclosedeq_rowGen_map, Polynomial.coeff_map]

theorem lclosedeq_applyWord_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord S w (map φ f) = map φ (applyWord R w f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    rw [ih, lclosedeq_rowDiv_map]

theorem lclosedeq_lpMinor_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    map φ (lpMinor R (r := r) (n := n) s hr hn) = lpMinor S s hr hn := by
  unfold lpMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply, map_X]

theorem lclosedeq_hw_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (hn : n ≤ r) (ν : Fin n → ℕ) :
    map φ (hw R hn ν) = hw S hn ν := by
  simp only [hw, map_prod, map_pow, lclosedeq_lpMinor_map]

end Formalism.GradedWeylDivisibility
