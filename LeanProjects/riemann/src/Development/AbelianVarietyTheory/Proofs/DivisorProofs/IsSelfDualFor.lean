import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour

variable {F : Type} [Field F] [NumberField F]

def IsSelfDualFor {v : Pl F} (χ : AddChar (Fv F v) ℂ) (ν : Measure (Fv F v)) : Prop :=
  ν.IsAddHaarMeasure ∧ ∀ f ∈ SB (Fv F v), ∫ y, (∫ x, f x * χ (x * y) ∂ν) ∂ν = f 0

open Classical in

def measV (ψ : AddChar (AF F) ℂ) (v : Pl F) : Measure (Fv F v) :=
  if h : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν then h.choose else 0

def fourV (ψ : AddChar (AF F) ℂ) (v : Pl F) {κ : Type} [Fintype κ] (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) : ℂ :=
  ∫ x, φ x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y) ∂(Measure.pi fun _ : κ => measV ψ v)

open Classical in
variable (F) in

def measI (κ : Type) [Fintype κ] : Measure (κ → mixedEmbedding.mixedSpace F) :=
  Measure.pi fun _ : κ => (Measure.pi fun _ : {w : InfinitePlace F // w.IsReal} => (volume : Measure ℝ)).prod
    (Measure.pi fun _ : {w : InfinitePlace F // w.IsComplex} => (volume : Measure ℂ))

def eInf {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ))

end GlobalTheory.WeylFour

end
