import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L) (α β : GAf L n) (Ra Rb : Finset (GAf L n)), TrivOutside {s.v} α → TrivOutside {s.v} β → (∀ x : GAf L n, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * α * k₂) → ∃! γ, γ ∈ Ra ∧ γ⁻¹ * x ∈ Umax L n) → (∀ γ ∈ Ra, ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ γ = k₁ * α * k₂) → (∀ x : GAf L n, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * β * k₂) → ∃! γ, γ ∈ Rb ∧ γ⁻¹ * x ∈ Umax L n) → (∀ γ ∈ Rb, ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ γ = k₁ * β * k₂) → ∀ f : GAf L n → W, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → ∑ γ ∈ Ra, NG.rt L n γ (∑ δ ∈ Rb, NG.rt L n δ f) = ∑ δ ∈ Rb, NG.rt L n δ (∑ γ ∈ Ra, NG.rt L n γ f) := by
  first | exact @GlobalTheory.SplitHeckeComm.doubleCoset_comm | exact GlobalTheory.SplitHeckeComm.doubleCoset_comm | (intros; apply GlobalTheory.SplitHeckeComm.doubleCoset_comm <;> assumption)
