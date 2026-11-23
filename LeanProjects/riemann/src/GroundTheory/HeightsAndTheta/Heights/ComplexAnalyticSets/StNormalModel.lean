import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

def zeroSetIn {σ : Type*} (I : Ideal (MvPolynomial σ ℂ)) : Set (σ → ℂ) :=
  {z | ∀ q ∈ I, eval z q = 0}

def firstCoords {n m : ℕ} (w : Fin n ⊕ Fin m → ℂ) : Fin n → ℂ :=
  fun i => w (Sum.inl i)

structure NormalModel {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) where

  m : ℕ

  ideal : Ideal (MvPolynomial (Fin n ⊕ Fin m) ℂ)
  isPrime : ideal.IsPrime
  isIntegrallyClosed : IsIntegrallyClosed (MvPolynomial (Fin n ⊕ Fin m) ℂ ⧸ ideal)
  comap_eq : ideal.comap
    (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ) = J
  integral : ∀ i : Fin m, ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P.Monic ∧
    P.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom
      (X (Sum.inr i)) ∈ ideal
  birational : ∀ i : Fin m, ∃ a b : MvPolynomial (Fin n) ℂ, b ∉ J ∧
    rename Sum.inl b * X (Sum.inr i) - rename Sum.inl a ∈ ideal

def lineDiagonalMap : MvPolynomial (Fin 1 ⊕ Fin 1) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  aeval (Sum.elim X fun _ => X 0)

theorem lineDiagonalMap_rename (q : MvPolynomial (Fin 1) ℂ) : lineDiagonalMap (rename Sum.inl q) = q := by
  rw [lineDiagonalMap, aeval_rename]
  exact aeval_X_left_apply q

theorem lineDiagonalMap_surjective : Function.Surjective lineDiagonalMap :=
  fun q => ⟨rename Sum.inl q, lineDiagonalMap_rename q⟩

def lineDiagonalIdeal : Ideal (MvPolynomial (Fin 1 ⊕ Fin 1) ℂ) :=
  RingHom.ker lineDiagonalMap.toRingHom

theorem lineDiagonalIdeal_isPrime : lineDiagonalIdeal.IsPrime :=
  RingHom.ker_isPrime _

theorem lineDiagonalIdeal_isIntegrallyClosed :
    IsIntegrallyClosed (MvPolynomial (Fin 1 ⊕ Fin 1) ℂ ⧸ lineDiagonalIdeal) :=
  IsIntegrallyClosed.of_equiv (RingHom.quotientKerEquivOfSurjective
    (f := lineDiagonalMap.toRingHom) lineDiagonalMap_surjective).symm

def lineDiagonalModel : NormalModel (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) where
  m := 1
  ideal := lineDiagonalIdeal
  isPrime := lineDiagonalIdeal_isPrime
  isIntegrallyClosed := lineDiagonalIdeal_isIntegrallyClosed
  comap_eq := by
    ext q
    rw [Ideal.mem_comap, Ideal.mem_bot]
    show lineDiagonalMap (rename Sum.inl q) = 0 ↔ q = 0
    rw [lineDiagonalMap_rename]
  integral := fun i => ⟨Polynomial.X - Polynomial.C (X 0), Polynomial.monic_X_sub_C _, by
    show lineDiagonalMap _ = 0
    simp [lineDiagonalMap, Polynomial.eval₂_sub]⟩
  birational := fun i => ⟨X 0, 1, by simp, by
    show lineDiagonalMap _ = 0
    simp [lineDiagonalMap]⟩

theorem eval_const_of_lineDiagonalMap_eq_zero (c : ℂ) (q : MvPolynomial (Fin 1 ⊕ Fin 1) ℂ)
    (hq : lineDiagonalMap q = 0) : eval (fun _ => c) q = 0 := by
  have h2 : ((aeval (fun _ : Fin 1 => c)).comp lineDiagonalMap) q = 0 := by
    rw [AlgHom.comp_apply, hq, map_zero]
  rw [lineDiagonalMap, MvPolynomial.comp_aeval] at h2
  have hpt : (fun i : Fin 1 ⊕ Fin 1 => (aeval (fun _ : Fin 1 => c) : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ)
      (Sum.elim (X : Fin 1 → MvPolynomial (Fin 1) ℂ) (fun _ => X 0) i)) = fun _ => c := by
    funext s
    rcases s with i | i <;> simp
  rw [hpt] at h2
  rw [← coe_aeval_eq_eval]
  exact h2

theorem const_mem_zeroSetIn_lineDiagonal (c : ℂ) :
    (fun _ => c : Fin 1 ⊕ Fin 1 → ℂ) ∈ zeroSetIn lineDiagonalIdeal :=
  fun q hq => eval_const_of_lineDiagonalMap_eq_zero c q hq

theorem X_inl_not_mem_lineDiagonalIdeal :
    (X (Sum.inl 0) : MvPolynomial (Fin 1 ⊕ Fin 1) ℂ) ∉ lineDiagonalIdeal := by
  intro hX
  have h1 : lineDiagonalMap (X (Sum.inl 0)) = 0 := hX
  simp [lineDiagonalMap] at h1

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
