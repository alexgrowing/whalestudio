import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Objects
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

section Cusp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} (H : HodgeData D)
  {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂)

def cuspValues (z : (Σ k, ι k) → ℂ) : Set ℝ :=
  {x | ∃ I : Submodule O abelian₂, I ≠ ⊥ ∧ IsSaturated I ∧ IsIsoSub Cd.form I ∧ x = -Real.log (Cd.Nz z I)}

def phiI (z : (Σ k, ι k) → ℂ) (I : Submodule O abelian₂) : ℝ :=
  2 * phMu H z - Real.log (Cd.Nz z I)

def cuspCorrected2 (z : (Σ k, ι k) → ℂ) : ℝ :=
  phMu H z + Cd.cuspWeight z / 2

end Cusp

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

def phiHom (z : (Σ k, ι k) → ℂ) : ℝ := 2 * phMu D.mu z

def phiI (z : (Σ k, ι k) → ℂ) (I : Submodule (𝓞 Em) (Fin D.N → Em)) : ℝ :=
  D.phiHom z - Real.log (D.nz z I)

def cuspCorrected2 (z : (Σ k, ι k) → ℂ) : ℝ :=
  phMu D.mu z + D.cuspU z / 2

end FullerData

end GroundTheory.Heights₂.Heights.NineStatements
