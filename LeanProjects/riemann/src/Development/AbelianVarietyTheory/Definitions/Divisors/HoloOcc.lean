import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TransferToDefiniteQuaternion

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V

namespace GlobalTheory.TfJl

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def kw (lam : InfinitePlace F → DomWeight 2) (v : InfinitePlace F) : ℤ := (lam v).w 0 - (lam v).w 1 + 2

def IsHolo (lam : InfinitePlace F → DomWeight 2) (φ : TR.Sm F 2) : Prop :=
  TR.IsCuspForm φ ∧ ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * (kw lam v : ℂ)) • φ ∧
    TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ) ∧
    ∀ u : ℂ, TR.cap v u φ = (((GlobalTheory.UnitaryBC.infOfWeight (lam v)).map Neg.neg).map (u + ·)).prod • φ

def HoloOcc (lam : InfinitePlace F → DomWeight 2) (τ : SmIrr (GL (Fin 2) (Af F))) : Prop :=
  ∃ f : τ.V →ₗ[ℂ] TR.Sm F 2, f ≠ 0 ∧ (∀ x, IsHolo lam (f x)) ∧ ∀ g x, f (τ.ρ g x) = TR.finRep F 2 g (f x)

end GlobalTheory.TfJl
