import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColsComplete
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.LeadDet

theorem lead_det : ∀ (R C : Type) [CommRing R] [Field C] (f : R →+* C) (ξ ν : R) (N : ℕ) (F G : Matrix (Fin N) (Fin N) R) (lam : C), F * G = (ξ * ν) • (1 : Matrix (Fin N) (Fin N) R) → IotaScalar (F.map f) (G.map f) (G.map f).rank lam → Lead f ξ F.det (G.map f).rank (lam * f ν ^ (G.map f).rank) := by
  intro R C _ _ f ξ ν N F G lam hFG hI
  set a := (G.map f).rank with ha
  obtain ⟨haN, k, k', hdet⟩ := GlobalTheory.ColComplete.cols_complete C N (G.map f)
  rw [← ha] at hdet
  let X : Fin N → Fin N → R := fun i => if (i : ℕ) < a then G *ᵥ Pi.single (k i) 1 else Pi.single (k' i) 1
  let Y : Fin N → Fin N → R := fun i => if (i : ℕ) < a then Pi.single (k i) 1 else F *ᵥ Pi.single (k' i) 1
  let c : Fin N → R := fun i => if (i : ℕ) < a then ξ * ν else 1
  have hFGv : ∀ v, F *ᵥ (G *ᵥ v) = (ξ * ν) • v := by
    intro v; rw [mulVec_mulVec, hFG]; ext j; simp [mulVec, dotProduct, Matrix.one_apply, Finset.mul_sum]
  have hrow : Matrix.of X * Fᵀ = diagonal c * Matrix.of Y := by
    ext i j
    rw [diagonal_mul, mul_apply]
    have : (∑ l, Matrix.of X i l * Fᵀ l j) = (F *ᵥ X i) j := by
      simp [mulVec, dotProduct, mul_comm]
    rw [this]
    by_cases hi : (i : ℕ) < a
    · simp only [X, Y, c, hi, if_true, of_apply]; rw [hFGv]; simp
    · simp [X, Y, c, hi]
  have hdetR : (Matrix.of X).det * F.det = (ξ * ν) ^ a * (Matrix.of Y).det := by
    have := congrArg Matrix.det hrow
    rw [det_mul, det_mul, det_transpose, det_diagonal] at this
    rw [this]; congr 1
    simp only [c]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    congr 1
    rw [← ha] at haN
    have hm : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < a)).map Fin.valEmbedding = Finset.range a := by
      ext m; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro h; exact ⟨⟨m, by omega⟩, h, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hm, Finset.card_range]
  have hxmap : (Matrix.of X).map f = Matrix.of (fun i : Fin N => if (i : ℕ) < a then G.map f *ᵥ Pi.single (k i) 1 else Pi.single (k' i) 1) := by
    ext i j
    by_cases hi : (i : ℕ) < a
    · simp [X, hi, RingHom.map_mulVec]
    · simp [X, hi, Pi.single_apply, apply_ite f]
  have hymap : ∀ i, (Matrix.of Y).map f i = if (i : ℕ) < a then Pi.single (k i) 1 else F.map f *ᵥ Pi.single (k' i) 1 := by
    intro i; ext j
    by_cases hi : (i : ℕ) < a
    · simp [Y, hi, Pi.single_apply, apply_ite f]
    · simp [Y, hi, RingHom.map_mulVec]
  have hY := hI (fun i => if (i : ℕ) < a then G.map f *ᵥ Pi.single (k i) 1 else Pi.single (k' i) 1) (fun i => (Matrix.of Y).map f i)
    (by intro i hi; rw [hymap]; simp [hi]) (by intro i hi; rw [hymap]; simp [Nat.not_lt.mpr hi])
  refine ⟨(Matrix.of X).det, ν ^ a * (Matrix.of Y).det, ?_, ?_, ?_⟩
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, hxmap]; exact hdet
  · rw [hdetR, mul_pow]; ring
  · rw [map_mul, map_pow, RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hxmap]
    have : Matrix.of (fun i => (Matrix.of Y).map f i) = (Matrix.of Y).map f := rfl
    rw [this] at hY; rw [hY]; ring

end GlobalTheory.LeadDet
