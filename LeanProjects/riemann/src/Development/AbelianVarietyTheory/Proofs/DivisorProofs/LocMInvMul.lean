import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAnisoAt

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow GlobalTheory.SWMidF GlobalTheory.SWOpCase

namespace GlobalTheory.SWOpFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}

def locM {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (T : GL (Fin (n + n)) E) (v₀ : HeightOneSpectrum (𝓞 F))
    (g : UA σ J₂) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v₀ ⊗[F] E) :=
  (inBasis σ T g).map (compFin F E v₀)

def scal {v : HeightOneSpectrum (𝓞 F)} (a : Fv F v) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
  (a ⊗ₜ[F] (1 : E)) • 1

def upAt (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E) (T : GL (Fin (n + n)) E) (v₀ : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Set (UA σ J₂) :=
  {g | g ∈ GlobalTheory.SWOpIndef.supAt σ J₂ v₀ ∧ ∃ b : Fv F v₀, Valued.v b ≤ WithZero.exp (-(N : ℤ)) ∧
    locM σ T v₀ g = blk 1 (scal b) 0 1}

variable {σ} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

end GlobalTheory.SWOpFin
