import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OmLocU

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def IsUnif (ϖ : Fv F v) : Prop := Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))

def UnifEx : Prop := ∃ ϖ : Fv F v, IsUnif v ϖ

def PO (ϖ : Fv F v) : Set (Fv F v ⊗[F] E) := {x | ∃ c ∈ OEv (E := E) v, x = sc (E := E) v ϖ * c}

def LamT {n : ℕ} (Λ : Set (Fin n → E)) (a : ℕ) : Set (TupV (E := E) v n a) :=
  {X | ∀ i, X i ∈ latLoc (E := E) v Λ}

variable (σ : E →ₐ[F] E)

def HermP (a : ℕ) (ϖ : Fv F v) : Set (HermR (Fv F v) σ a) :=
  {S | ∀ i j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ PO (E := E) v ϖ}

def NearT {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {a : ℕ} (ϖ : Fv F v)
    (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) : Set (TupV (E := E) v n a) :=
  {X | ∀ i j, gramR (Fv F v) σ J X i j - T i j ∈ PO (E := E) v ϖ}

def qv : ℝ := ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)

def prodEta (n a : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (n - a + 1) n, (1 - (etaV (E := E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)))

end Defs

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def GoodY (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  StdHyp σ J ψ ∧ (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) ∧
  IsSDLoc σ J v Λ ∧ UnramAt (E := E) v ∧ a ≤ n ∧ IsPrim v Λ Y ∧
  (∃ w ∈ OEv (E := E) v, (gramR (Fv F v) σ J Y).det ∈ OEv (E := E) v ∧ (gramR (Fv F v) σ J Y).det * w = 1)

def OrbAll (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ X ∈ LamT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
    ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • Y

def FibU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → (∃ fib, IsOm σ J ψ v a fib) → ∀ ϖ : Fv F v, IsUnif v ϖ →
    omAt σ J ψ v (gramR (Fv F v) σ J Y) (LamT v Λ a) =
      dX σ J ψ v a (LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) / dT σ ψ v a (HermP v σ a ϖ)

def CountU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) → ∀ ϖ : Fv F v, IsUnif v ϖ →
    dX σ J ψ v a (LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) =
      ENNReal.ofReal (qv v ^ (-((a : ℤ) ^ 2)) * prodEta (E := E) v n a) * dX σ J ψ v a (LamT v Λ a)

def SdVolW (a : ℕ) : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) →
    dX σ J ψ v a (LamT v Λ a) = ENNReal.ofReal (absV v (dV v) ^ ((n : ℝ) * a))

def SdVolH (a : ℕ) : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) → ∀ ϖ : Fv F v, IsUnif v ϖ →
    dT σ ψ v a (HermP v σ a ϖ) = ENNReal.ofReal (qv v ^ (-((a : ℤ) ^ 2)) * absV v (dV v) ^ ((a : ℝ) ^ 2 / 2))

def CondV : Prop :=
  StdHyp σ J ψ → ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) ↔
    dV v * t ∈ v.adicCompletionIntegers F

end Steps

end PI.OmLocU
