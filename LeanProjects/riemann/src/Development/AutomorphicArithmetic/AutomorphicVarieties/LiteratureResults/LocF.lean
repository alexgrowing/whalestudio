import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DiscreteGL2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.V.Lit.JL

variable {F : Type} [Field F] [NumberField F]

def LocF (τ : SmIrr (GL (Fin 2) (Af F))) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] τ.V, f ≠ 0 ∧ ∀ g x, f (σ.ρ g x) = τ.ρ (locGL F 2 w g) (f x)

variable [IsTotallyReal F]

omit [IsTotallyReal F] in

def IsTw (s : ℂ) (τ τ' : SmIrr (GL (Fin 2) (Af F))) : Prop :=
  ∃ e : τ.V ≃ₗ[ℂ] τ'.V, ∀ g x, τ'.ρ g (e x) = ((chiDet 2 (Model.absC F s) (finGL F 2 g) : ℂˣ) : ℂ) • e (τ.ρ g x)

def FinG (V : Submodule ℂ (TR.Sm F 2)) (τ : SmIrr (GL (Fin 2) (Af F))) : Prop :=
  ∃ f : τ.V →ₗ[ℂ] TR.Sm F 2, f ≠ 0 ∧ (∀ x, f x ∈ V) ∧ ∀ g x, f (τ.ρ g x) = TR.finRep F 2 g (f x)

def FinD {Q : DefQuat F} (V : Submodule ℂ (DA Q → ℂ)) (τ : SmIrr (GL (Fin 2) (Af F))) : Prop :=
  ∃ f : τ.V →ₗ[ℂ] (DA Q → ℂ), f ≠ 0 ∧ (∀ x, f x ∈ V) ∧ ∀ g x, f (τ.ρ g x) = RD Q (1, g) (f x)

end UpperTheory.V.Lit.JL
