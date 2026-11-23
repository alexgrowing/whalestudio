import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open Formalism.UG (cT)

namespace GlobalTheory.EisCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def StabL (x : Matrix (Fin n) (Fin 1) E) (g : GAd σ J) : Prop :=
  ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J g).1 * adMat F x = l.1 • adMat F x

def IsTransv (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) : Prop :=
  ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ StabL σ J x (γ * t⁻¹ : ratPts σ J).1

def OrthL (x : Matrix (Fin n) (Fin 1) E) (g : GAd σ J) : Prop :=
  adMat F (cT (σ : E →+* E) x * J) * (matHom _ σ J g⁻¹).1 * adMat F x = 0

def lineSet (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) : Set (ratPts σ J) :=
  {t | t ∈ T ∧ StabL σ J x t.1}

def midSet (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) : Set (ratPts σ J) :=
  {t | t ∈ T ∧ ¬ StabL σ J x t.1 ∧ OrthL σ J x t.1}

def bigSet (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) : Set (ratPts σ J) :=
  {t | t ∈ T ∧ ¬ OrthL σ J x t.1}

def fs (h : GAd σ J → ℝ) (s : ℂ) (g : GAd σ J) : ℂ := (h g : ℂ) ^ (s + ((n : ℂ) - 1) / 2)

def lineSum (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) (h : GAd σ J → ℝ) (s : ℂ) (g : GAd σ J) : ℂ :=
  ∑' t : lineSet σ J x T, fs σ J h s (t.1.1 * g)

def midSum (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) (h : GAd σ J → ℝ) (s : ℂ) (g : GAd σ J) : ℂ :=
  ∑' t : midSet σ J x T, fs σ J h s (t.1.1 * g)

def bigSum (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) (h : GAd σ J → ℝ) (s : ℂ) (g : GAd σ J) : ℂ :=
  ∑' t : bigSet σ J x T, fs σ J h s (t.1.1 * g)

end GlobalTheory.EisCT

end
