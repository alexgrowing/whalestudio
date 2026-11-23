import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.V.Af.Smo (Eig EigAt)

namespace UpperTheory.ConvolutionTheory.R2.Pp

variable (F : Type) [Field F] [NumberField F]

variable {F} in

def FinOne (g : G1 F) : Prop := ∀ i j, (g i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2

variable {F} in

def Lf (f : GL (Fin 2) (A F) → ℂ) : Prop := Continuous f ∧ ∀ γ g, f (ratGL F 2 γ * g) = f g

def WfBasic : Prop :=
  ∀ f : GL (Fin 2) (A F) → ℂ, Lf f → Continuous (Wf f) ∧ (∀ b g, Wf f (gl (nU b) * g) = ψ (-b) * Wf f g) ∧
    (∀ g, IntegrableOn (fun b => f (gl (nU b) * g) * ψ b) (fundamentalSet F) (adeleMeasure F)) ∧
    (∀ (c : ℂ) g, Wf (c • f) g = c * Wf f g) ∧ ∀ f', Lf f' → ∀ g, Wf (f + f') g = Wf f g + Wf f' g

def WfT : Prop :=
  ∀ f : GL (Fin 2) (A F) → ℂ, Lf f → ∀ (t : Fˣ) g,
    ∫ b in fundamentalSet F, f (gl (nU b) * g) * ψ (rt (t : F) * b) ∂(adeleMeasure F) = Wf f (aE (IdeleGroup.diagonal F t) * g)

def WfInj : Prop :=
  ∀ f : GL (Fin 2) (A F) → ℂ, Lf f → (∀ g, ∫ b in fundamentalSet F, f (gl (nU b) * g) ∂(adeleMeasure F) = 0) →
    (∀ g, Wf f g = 0) → f = 0

def WfEig : Prop :=
  ∀ f : GL (Fin 2) (A F) → ℂ, Lf f → ∀ v B, EigAt v B f → EigAt v B (Wf f)

variable [IsTotallyReal F]

def CuspZero : Prop :=
  ∀ π : TR.CuspSub F 2, ∀ f ∈ π.V, Lf f.1 ∧ ∀ g, ∫ b in fundamentalSet F, f.1 (gl (nU b) * g) ∂(adeleMeasure F) = 0

def Bdd : Prop :=
  ∀ π : TR.CuspSub F 2, ∀ f ∈ π.V, ∀ C : Set (GL (Fin 2) (A F)), IsCompact C →
    ∃ B : ℝ, ∀ g : G1 F, ∀ k ∈ C, ‖f.1 (gl g * k)‖ ≤ B ∧ ‖Wf f.1 (gl g * k)‖ ≤ B

def WfDecay : Prop :=
  ∀ π : TR.CuspSub F 2, ∀ f ∈ π.V, ∀ C : Set (GL (Fin 2) (A F)), IsCompact C → ∀ c : ℝ, 0 < c → ∀ r : ℕ,
    ∃ B : ℝ, ∀ b a, ∀ k ∈ C, c ≤ ab a → ‖Wf f.1 (gl (nU b * mD a) * k)‖ ≤ B * (ab a)⁻¹ ^ r

def InfDec : Prop :=
  ∀ x : GL (Fin 2) (A F), ∃ (g : G1 F) (s : (A F)ˣ) (k : TR.Kinf F 2) (y : GL (Fin 2) (Af F)), FinOne g ∧
    x = Matrix.GeneralLinearGroup.scalar (Fin 2) s * (gl g * TR.infGL F 2 (Unitary.toUnits k) * finGL F 2 y)

def WfNe : Prop := ∀ π : TR.CuspSub F 2, ∃ f ∈ π.V, ∃ g : G1 F, FinOne g ∧ Wf f.1 (gl g) ≠ 0

def SatAe : Prop := ∀ π : TR.CuspSub F 2, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ B, π.HasSat v B

def SphEig : Prop :=
  ∀ π : TR.CuspSub F 2, ∀ f ∈ π.V,
    (∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL v 2, f.1 (g * finGL F 2 (locGL F 2 v k)) = f.1 g) ∧
    ∀ v B, π.HasSat v B → (∀ g, ∀ k ∈ GlobalTheory.LFun.KGL v 2, f.1 (g * finGL F 2 (locGL F 2 v k)) = f.1 g) → EigAt v B f.1

def Isotyp : Prop :=
  ∀ (π : TR.CuspSub F 2) (v : HeightOneSpectrum (𝓞 F)) σ, π.IsLocComp v σ → ∀ x : π.V,
    x ∈ Submodule.span ℂ {y : π.V | ∃ j : σ.V →ₗ[ℂ] π.V, (∀ g u, j (σ.ρ g u) = π.locRep v g (j u)) ∧ y ∈ LinearMap.range j}

def IsotypQuot : Prop :=
  ∀ (π : TR.CuspSub F 2) (v : HeightOneSpectrum (𝓞 F)) σ σ', π.IsLocComp v σ →
    ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (Fin 2) (v.adicCompletion F)) X)
      (i : (σ' : SmIrr (GL (Fin 2) (v.adicCompletion F))).V →ₗ[ℂ] X), i ≠ 0 → (∀ g u, i (σ'.ρ g u) = ρ g (i u)) →
      (∀ u, i u ∈ Submodule.span ℂ {y : X | ∃ p : π.V →ₗ[ℂ] X, (∀ g x, p (π.locRep v g x) = ρ g (p x)) ∧ y ∈ LinearMap.range p}) →
      ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g u, e (σ.ρ g u) = σ'.ρ g (e u)

end UpperTheory.ConvolutionTheory.R2.Pp

end
