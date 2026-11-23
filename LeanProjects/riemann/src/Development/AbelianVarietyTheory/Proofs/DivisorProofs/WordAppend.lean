import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.ArchDecay

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def infAd (a : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a)

def arch (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i)

def dD (v : κ → mixedEmbedding.mixedSpace F) (f : (κ → AF F) → ℂ) (x : κ → AF F) : ℂ :=
  deriv (fun t : ℝ => f (x + fun i => infAd F (t • v i))) 0

def mM (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) (x : κ → AF F) : ℂ :=
  (l (arch F x) : ℂ) * f x

variable (κ) in

abbrev Op : Type := (κ → mixedEmbedding.mixedSpace F) ⊕ ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)

def app (o : Op F κ) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ := Sum.elim (fun v => dD F v f) (fun l => mM F l f) o

def size (o : Op F κ) : ℝ := Sum.elim (fun v => ‖v‖) (fun l => ‖l‖) o

def word (w : List (Op F κ)) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ := w.foldr (fun o g => app F o g) f

def wordD (w : List (κ → mixedEmbedding.mixedSpace F)) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  word F (w.map Sum.inl) f

def Per (m : ℕ) (f : (κ → AF F) → ℂ) : Prop :=
  ∀ x z : κ → AF F, (∀ i, ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧
    z i = (m : AF F) * a) → f (x + z) = f x

@[simp] theorem word_nil (f : (κ → AF F) → ℂ) : word F [] f = f := rfl

@[simp] theorem word_cons (o : Op F κ) (w : List (Op F κ)) (f : (κ → AF F) → ℂ) :
    word F (o :: w) f = app F o (word F w f) := rfl

theorem word_append (w w' : List (Op F κ)) (f : (κ → AF F) → ℂ) : word F (w ++ w') f = word F w (word F w' f) := by
  simp [word, List.foldr_append]

end GlobalTheory.ArchDecay
