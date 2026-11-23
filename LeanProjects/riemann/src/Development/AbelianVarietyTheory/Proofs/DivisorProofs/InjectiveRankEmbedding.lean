import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

noncomputable section

namespace GlobalTheory.CharPair

def leftInvVal (P Q R : ℕ) : Ix P Q × Ix R 0 → Mdl P Q
  | (Sum.inl a, Sum.inl c) => if (c : ℕ) = (a : ℕ) then 1 else 0
  | (Sum.inr b, Sum.inl c) => if hc : (c : ℕ) < P then X (⟨c, hc⟩, b) else 0
  | (_, Sum.inr _) => 0

theorem leftInv_mR (P Q R : ℕ) (h : P ≤ R) (a : Fin P) (b : Fin Q) :
    aeval (leftInvVal P Q R) (mR P Q R a b) = (X (a, b) : Mdl P Q) := by
  rw [mR, map_sum, Finset.sum_eq_single (Fin.castLE h a)]
  · simp [leftInvVal]
  · intro c _ hc
    have : (c : ℕ) ≠ (a : ℕ) := fun e => hc (Fin.ext e)
    simp [leftInvVal, this]
  · simp

theorem leftInv_detR (P Q R : ℕ) (h : P ≤ R) :
    aeval (leftInvVal P Q R) (detR P Q R h) = (1 : Mdl P Q) := by
  rw [detR, AlgHom.map_det, ← Matrix.det_one (n := Fin P)]
  congr 1
  ext1 a c
  simp [leftInvVal, Matrix.one_apply, Fin.val_inj, eq_comm]

theorem leftInv_embR (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (G : Mdl P Q) :
    aeval (leftInvVal P Q R) (embR P Q R h k G) = G := by
  have e : (aeval (leftInvVal P Q R) : Pol P Q R 0 →ₐ[ℂ] Mdl P Q).comp
      (aeval fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) = AlgHom.id ℂ (Mdl P Q) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, b⟩
    rw [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
    exact leftInv_mR P Q R h a b
  have e2 := AlgHom.congr_fun e G
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at e2
  simp only [embR, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, map_mul, map_pow,
    leftInv_detR, one_pow, mul_one, e2]

theorem embR_injective : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ), Function.Injective (embR P Q R h k) :=
  fun P Q R h k => Function.LeftInverse.injective (g := aeval (leftInvVal P Q R)) (leftInv_embR P Q R h k)

end GlobalTheory.CharPair

end
