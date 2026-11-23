import Mathlib

noncomputable section

open Matrix Polynomial
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section Cyc

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]

structure IsGal (σ : R ≃ₐ[k] R) (q : ℕ) : Prop where
  pos : 0 < q
  pow : σ ^ q = 1
  inj : Function.Injective (algebraMap k R)
  fix : ∀ r, σ r = r → r ∈ (algebraMap k R).range
  sep : ∃ (s : ℕ) (x y : Fin s → R), ∀ j < q, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0

variable {n : ℕ}

def sg (σ : R ≃ₐ[k] R) : GL (Fin n) R →* GL (Fin n) R := Matrix.GeneralLinearGroup.map (σ : R →+* R)

def up (R : Type) [CommRing R] [Algebra k R] : GL (Fin n) k →* GL (Fin n) R := Matrix.GeneralLinearGroup.map (algebraMap k R)

def nm (σ : R ≃ₐ[k] R) (q : ℕ) (δ : GL (Fin n) R) : GL (Fin n) R := ((List.range q).map fun i => sg (σ ^ i) δ).prod

def sgConj (σ : R ≃ₐ[k] R) (x δ : GL (Fin n) R) : GL (Fin n) R := x⁻¹ * δ * sg σ x

def cp {S : Type} [CommRing S] (g : GL (Fin n) S) : S[X] := (g : Matrix (Fin n) (Fin n) S).charpoly

def ct (c : R ≃ₐ[k] R) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := (M.map c)ᵀ

def th (c : R ≃ₐ[k] R) (g : GL (Fin n) R) : GL (Fin n) R :=
  ⟨ct c (g⁻¹ : GL (Fin n) R), ct c g,
    by rw [ct, ct, ← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero c) (map_one c), Matrix.transpose_one],
    by rw [ct, ct, ← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero c) (map_one c), Matrix.transpose_one]⟩

def thConj (c : R ≃ₐ[k] R) (x d : GL (Fin n) R) : GL (Fin n) R := x⁻¹ * d * th c x

def cong (c : R ≃ₐ[k] R) (y : GL (Fin n) R) (J : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := ct c y * J * (y : Matrix (Fin n) (Fin n) R)

def IsHerm (c : R ≃ₐ[k] R) (J : Matrix (Fin n) (Fin n) R) : Prop := ct c J = J ∧ IsUnit J.det

def IsCsr (c : R ≃ₐ[k] R) (n : ℕ) (P : R[X]) : Prop :=
  P.Monic ∧ P.natDegree = n ∧ IsUnit (P.coeff 0) ∧ reflect n (P.map (c : R →+* R)) = C (c (P.coeff 0)) * P

end Cyc

section Model

variable {k R A : Type} [CommRing k] [CommRing R] [Algebra k R] [CommRing A] [Algebra k A] {n : ℕ}

def io (c : R ≃ₐ[k] R) (A : Type) [CommRing A] [Algebra k A] : R ⊗[k] A ≃ₐ[k] R ⊗[k] A :=
  Algebra.TensorProduct.congr c AlgEquiv.refl

def mat (b : Module.Basis (Fin n) k A) (z : R ⊗[k] A) : Matrix (Fin n) (Fin n) R :=
  Algebra.leftMulMatrix (Algebra.TensorProduct.basis R b) z

def matU (b : Module.Basis (Fin n) k A) : (R ⊗[k] A)ˣ →* GL (Fin n) R :=
  Units.map (Algebra.leftMulMatrix (Algebra.TensorProduct.basis R b)).toMonoidHom

def gramL (b : Module.Basis (Fin n) k A) (s : R ⊗[k] A) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => Algebra.trace R (R ⊗[k] A) (s * (1 ⊗ₜ (b i * b j)))

def gram (R : Type) [CommRing R] [Algebra k R] (b : Module.Basis (Fin n) k A) (x : A) : Matrix (Fin n) (Fin n) R :=
  gramL b ((1 : R) ⊗ₜ[k] x)

def IsReg (c : R ≃ₐ[k] R) (b : Module.Basis (Fin n) k A) (g : (R ⊗[k] A)ˣ) : Prop :=
  (g : R ⊗[k] A) * io c A g = 1 ∧ (cp (matU b g)).Separable

def NormIn (c : R ≃ₐ[k] R) (x : Aˣ) : Prop := ∃ z : (R ⊗[k] A)ˣ, (1 : R) ⊗ₜ[k] (x : A) = z * io c A z

end Model

section Norms

variable (F E : Type) [Field F] [Field E] [Algebra F E]

def IsNm {A : Type} [CommRing A] [Algebra F A] (x : A) : Prop := ∃ z : A ⊗[F] E, Algebra.norm A z = x

open Classical in

def sgn {A : Type} [CommRing A] [Algebra F A] (x : A) : ℤˣ := if IsNm F E x then 1 else -1

variable {F E}

def ext (k : Type) [CommRing k] [Algebra F k] (σ : E ≃ₐ[F] E) : k ⊗[F] E ≃ₐ[k] k ⊗[F] E :=
  Algebra.TensorProduct.congr AlgEquiv.refl σ

def inc (k : Type) [CommRing k] [Algebra F k] : E →+* k ⊗[F] E := Algebra.TensorProduct.includeRight.toRingHom

def incL (k : Type) [CommRing k] [Algebra F k] (A : Type) [CommRing A] [Algebra F A] :
    E ⊗[F] A →ₐ[F] (k ⊗[F] E) ⊗[k] (k ⊗[F] A) :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft (S := F)).comp Algebra.TensorProduct.includeRight)
    (((Algebra.TensorProduct.includeRight : k ⊗[F] A →ₐ[k] (k ⊗[F] E) ⊗[k] (k ⊗[F] A)).restrictScalars F).comp
      Algebra.TensorProduct.includeRight) fun _ _ => Commute.all _ _

end Norms

end UpperTheory.ConvolutionTheory.D
