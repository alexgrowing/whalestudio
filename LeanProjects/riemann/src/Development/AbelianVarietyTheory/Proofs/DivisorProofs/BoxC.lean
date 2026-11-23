import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.DblDatum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def topC {n d : ℕ} (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) : Matrix (Fin n) (Fin d) (AE F E) :=
  u.submatrix id (finSumFinEquiv ∘ Sum.inl)

def botC {n d : ℕ} (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) : Matrix (Fin n) (Fin d) (AE F E) :=
  u.submatrix id (finSumFinEquiv ∘ Sum.inr)

def dblE {σ : E →ₐ[F] E} {n d : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E} {κ : Type} [Fintype κ]
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) κ)
    (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) : (κ ⊕ κ → AF F) × (κ ⊕ κ → AF F) :=
  (Sum.elim (co.e (topC u)).1 (co.e (botC u)).1, Sum.elim (co.e (topC u)).2 (-(co.e (botC u)).2))

def boxC {κ : Type} (φ₁ φ₂ : (κ → AF F) → ℂ) : (κ ⊕ κ → AF F) → ℂ :=
  boxFun φ₁ fun x => star (φ₂ x)

end GlobalTheory.DblDatum
end
