import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.CharPair

variable (P Q R S : ℕ)

abbrev Mdl : Type := MvPolynomial (Fin P × Fin Q) ℂ

def mR (a : Fin P) (b : Fin Q) : Pol P Q R 0 :=
  ∑ c : Fin R, X (Sum.inl a, Sum.inl c) * X (Sum.inr b, Sum.inl c)

def mS (a : Fin P) (b : Fin Q) : Pol P Q 0 S :=
  ∑ c : Fin S, X (Sum.inl a, Sum.inr c) * X (Sum.inr b, Sum.inr c)

def detR (h : P ≤ R) : Pol P Q R 0 :=
  (Matrix.of fun a c : Fin P => (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)).det

def detS (h : Q ≤ S) : Pol P Q 0 S :=
  (Matrix.of fun b c : Fin Q => (X (Sum.inr b, Sum.inr (Fin.castLE h c)) : Pol P Q 0 S)).det

def embR (h : P ≤ R) (k : ℕ) : Mdl P Q →ₗ[ℂ] Pol P Q R 0 :=
  LinearMap.mulRight ℂ (detR P Q R h ^ k) ∘ₗ (aeval fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2).toLinearMap

def embS (h : Q ≤ S) (k' : ℕ) : Mdl P Q →ₗ[ℂ] Pol P Q 0 S :=
  LinearMap.mulRight ℂ (detS P Q S h ^ k') ∘ₗ (aeval fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2).toLinearMap

variable {P Q}

abbrev mulM (a : Fin P) (b : Fin Q) : Module.End ℂ (Mdl P Q) := LinearMap.mulLeft ℂ (X (a, b))

abbrev derM (a : Fin P) (b : Fin Q) : Module.End ℂ (Mdl P Q) := (pderiv (a, b)).toLinearMap

variable (P Q)

def opR (k : ℕ) : Ix P Q → Ix P Q → Module.End ℂ (Mdl P Q)
  | .inl a, .inr b => mulM a b
  | .inr b, .inl a => -(∑ a', ∑ b', mulM a' b' * derM a' b * derM a b' + ((R + k : ℕ) : ℂ) • derM a b)
  | .inl a, .inl a' => ∑ b, mulM a b * derM a' b + (if a = a' then (k : ℂ) + (R : ℂ) / 2 else 0) • 1
  | .inr b, .inr b' => -(∑ a, mulM a b' * derM a b) - (if b = b' then (R : ℂ) / 2 else 0) • 1

def opS (k' : ℕ) : Ix P Q → Ix P Q → Module.End ℂ (Mdl P Q)
  | .inl a, .inr b => -mulM a b
  | .inr b, .inl a => ∑ a', ∑ b', mulM a' b' * derM a' b * derM a b' + ((S + k' : ℕ) : ℂ) • derM a b
  | .inl a, .inl a' => -(∑ b, mulM a b * derM a' b) - (if a = a' then (S : ℂ) / 2 else 0) • 1
  | .inr b, .inr b' => ∑ a, mulM a b' * derM a b + (if b = b' then (k' : ℂ) + (S : ℂ) / 2 else 0) • 1

def actR (k : ℕ) : Mat P Q →ₗ[ℂ] Module.End ℂ (Mdl P Q) :=
  ∑ i, ∑ j, (Matrix.entryLinearMap ℂ ℂ i j).smulRight (opR P Q R k i j)

def actS (k' : ℕ) : Mat P Q →ₗ[ℂ] Module.End ℂ (Mdl P Q) :=
  ∑ i, ∑ j, (Matrix.entryLinearMap ℂ ℂ i j).smulRight (opS P Q S k' i j)

theorem actR_apply (k : ℕ) (Z : Mat P Q) : actR P Q R k Z = ∑ i, ∑ j, Z i j • opR P Q R k i j := by
  simp [actR, LinearMap.sum_apply]

theorem actS_apply (k' : ℕ) (Z : Mat P Q) : actS P Q S k' Z = ∑ i, ∑ j, Z i j • opS P Q S k' i j := by
  simp [actS, LinearMap.sum_apply]

theorem detR_ne_zero (P Q R : ℕ) (h : P ≤ R) : detR P Q R h ≠ 0 := by
  let g : Fin P × Fin P → Ix P Q × Ix R 0 := fun ac => (Sum.inl ac.1, Sum.inl (Fin.castLE h ac.2))
  have hf : Function.Injective g := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ hac
    simp only [g, Prod.mk.injEq, Sum.inl.injEq] at hac
    exact Prod.ext hac.1 (Fin.castLE_injective h hac.2)
  have : detR P Q R h = rename g (Matrix.det (Matrix.mvPolynomialX (Fin P) (Fin P) ℂ)) := by
    rw [detR, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext a c; simp [g, Matrix.mvPolynomialX]
  rw [this]; intro h0
  exact Matrix.det_mvPolynomialX_ne_zero _ _ ((map_eq_zero_iff _ (rename_injective _ hf)).1 h0)

theorem detS_ne_zero (P Q S : ℕ) (h : Q ≤ S) : detS P Q S h ≠ 0 := by
  let g : Fin Q × Fin Q → Ix P Q × Ix 0 S := fun bc => (Sum.inr bc.1, Sum.inr (Fin.castLE h bc.2))
  have hf : Function.Injective g := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ hbc
    simp only [g, Prod.mk.injEq, Sum.inr.injEq] at hbc
    exact Prod.ext hbc.1 (Fin.castLE_injective h hbc.2)
  have : detS P Q S h = rename g (Matrix.det (Matrix.mvPolynomialX (Fin Q) (Fin Q) ℂ)) := by
    rw [detS, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext b c; simp [g, Matrix.mvPolynomialX]
  rw [this]; intro h0
  exact Matrix.det_mvPolynomialX_ne_zero _ _ ((map_eq_zero_iff _ (rename_injective _ hf)).1 h0)

end GlobalTheory.CharPair

end
