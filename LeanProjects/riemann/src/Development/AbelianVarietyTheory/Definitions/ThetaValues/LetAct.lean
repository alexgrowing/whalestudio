import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {n : ℕ} {Ix : Type} [Fintype Ix]
  (pl : Ix → (E →+* ℂ))

def gen (R : Type) [CommRing R] (n : ℕ) (t : Ix) : Matrix (Fin n) (Fin n) (MvPolynomial (Ix × Fin n × Fin n) R) :=
  Matrix.of fun a s => X (t, a, s)

def cof (R : Type) [CommRing R] (n : ℕ) : MvPolynomial (LtN Dw n) R →ₐ[R] MvPolynomial (Ix × Fin n × Fin n) R :=
  aeval fun ℓ =>
    if hi : (ℓ.2.1 : ℕ) < n then
      if h : ∃ t, pl t = ℓ.1 then gen R n h.choose ℓ.2.2 ⟨ℓ.2.1, hi⟩
      else if h' : ∃ t, ComplexEmbedding.conjugate (pl t) = ℓ.1 then
        (gen R n h'.choose).adjugate (Fin.rev ⟨ℓ.2.1, hi⟩) ℓ.2.2
      else 0
    else 0

def letAct (K : Type) [Field K] (g : Ix → GL (Fin n) K) : MvPolynomial (LtN Dw n) K →ₐ[K] MvPolynomial (LtN Dw n) K :=
  aeval fun ℓ =>
    if h : ∃ t, pl t = ℓ.1 then
      ∑ j, C ((g h.choose : Matrix (Fin n) (Fin n) K) j ℓ.2.2) * X (⟨ℓ.1, ℓ.2.1, j⟩ : LtN Dw n)
    else if h' : ∃ t, ComplexEmbedding.conjugate (pl t) = ℓ.1 then
      ∑ j, C ((((g h'.choose)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ℓ.2.2 j) * X (⟨ℓ.1, ℓ.2.1, j⟩ : LtN Dw n)
    else X ℓ

def IsEnum (H : Host E) (pl : Ix → (E →+* ℂ)) : Prop := Function.Injective pl ∧ ∀ τ, InPsi H τ ↔ τ ∈ Set.range pl

def WtIs (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n) : Prop :=
  ∀ t (i : Fin n), (lam t).w i = s t + (if (i : ℕ) < Dw.mult (pl t) then (a (pl t, i) : ℤ) else 0) -
    (if (Fin.rev i : ℕ) < Dw.mult (ComplexEmbedding.conjugate (pl t)) then
      (a (ComplexEmbedding.conjugate (pl t), (Fin.rev i : ℕ)) : ℤ) else 0)

def degC (a : (E →+* ℂ) × ℕ → ℕ) (t : Ix) : ℕ :=
  ∑ i : Fin (Dw.mult (ComplexEmbedding.conjugate (pl t))), a (ComplexEmbedding.conjugate (pl t), i)

def detFac (R : Type) [CommRing R] (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n) :
    MvPolynomial (Ix × Fin n × Fin n) R :=
  ∏ t, (gen R n t).det ^ ((degC Dw pl a t : ℤ) + (lam t).detShift - s t).toNat

end GlobalTheory.FrameRead
