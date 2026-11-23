import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open IsDedekindDomain
open GlobalTheory.Doubling (absE absEv absEw)

namespace GlobalTheory.EisMidHt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

variable (F) in

def adVec (z : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (z i)

def firstColumn {r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Fin n → E := fun i => X i 0

variable (F) in

def normFin (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (u : Fin n → Fv F v ⊗[F] E) : ℝ≥0 :=
  sInf {c | ∃ l : (Fv F v ⊗[F] E)ˣ, ((l⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) • u ∈ latLoc F L v ∧ c = absEv F E v l}

def normInf (a : GL (Fin n) (AF F ⊗[F] E)) (w : InfinitePlace F) (u : Fin n → w.Completion ⊗[F] E) : ℝ :=
  let b : GL (Fin n) (w.Completion ⊗[F] E) := (Formalism.UG.bc (compInf F E w) a)⁻¹
  Norm.norm (Finset.univ.sum fun i => Algebra.norm w.Completion ((b.1 *ᵥ u) i)) ^ w.mult

def ht (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (u : Fin n → AF F ⊗[F] E) : ℝ :=
  (∏ᶠ v, (normFin F L v (fun i => compFin F E v (u i)) : ℝ)) * ∏ w, normInf a w (fun i => compInf F E w (u i))

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

def IsLineReps (x y : Fin n → E) (Y : Set (Fin n → E)) : Prop :=
  (∀ z ∈ Y, z ≠ 0 ∧ hE σ J z z = 0 ∧ hE σ J x z = 0 ∧ hE σ J y z = 0) ∧
  (∀ z ∈ Y, ∀ z' ∈ Y, ∀ c : E, z = c • z' → z = z') ∧
  ∀ z : Fin n → E, z ≠ 0 → hE σ J z z = 0 → hE σ J x z = 0 → hE σ J y z = 0 → ∃ z' ∈ Y, ∃ c : E, z = c • z'

end GlobalTheory.EisMidHt

end
