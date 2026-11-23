import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FlathTensorProduct
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnitaryIrreducibleAdmissible
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open scoped InnerProductSpace

namespace CompanionTheory.Rg.Fl

def StDict : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ v : HeightOneSpectrum (𝓞 F),
      ∃ (L : Type) (_ : NontriviallyNormedField L) (_ : IsUltrametricDist L) (_ : ProperSpace L) (_ : CharZero L),
        Nonempty (GLoc σ J v ≃ₜ* GL (Fin n) L) ∨
        ∃ (s : L →+* L) (J' : Matrix (Fin n) (Fin n) L), (∀ x, s (s x) = x) ∧ (∀ x, ‖s x‖ = ‖x‖) ∧ (∃ x, s x ≠ x) ∧
          (J'.map s).transpose = J' ∧ J'.det ≠ 0 ∧ Nonempty (GLoc σ J v ≃ₜ* UG s J')

def IsPosDef {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ x : Fin n → E, x ≠ 0 → ∀ τ : E →+* ℂ, 0 < (τ (dotProduct (fun i => σ (x i)) (J.mulVec x))).re

def StDefinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ v : HeightOneSpectrum (𝓞 F),
      ∃ J' : Matrix (Fin n) (Fin n) E, IsHermND σ J' ∧ IsPosDef σ J' ∧ Nonempty (GLoc σ J v ≃ₜ* GLoc σ J' v)

def StSepDef : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → IsPosDef σ J → ∀ (v : HeightOneSpectrum (𝓞 F))
      (K : Subgroup (GLoc σ J v)), IsOpen (K : Set (GLoc σ J v)) → IsCompact (K : Set (GLoc σ J v)) → IsSep K

def StSepMove : Prop :=
  ∀ (G G' : Type) [Group G] [Group G'] (e : G ≃* G') (K : Subgroup G), IsSep (K.map e.toMonoidHom) → IsSep K

def StFactor : Prop :=
  ∀ (G G₁ H : Type) [Group G] [Group G₁] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)), (∀ g v, ‖π g v‖ = ‖v‖) → IsTopIrreducible π → ∀ (j : G₁ →* G) (p : G →* G₁),
    (∀ x, p (j x) = x) → (∀ x g, p g = 1 → Commute (j x) g) → ∀ E, IsPIProj (π.comp j) E → ∃ W, IsIrredSubrep (π.comp j) W

def StArchPI : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (w : InfinitePlace F)
      (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
      (ρ : GArch σ J w →* (H →L[ℂ] H)), IsUnitaryRep ρ → ∃ P, IsPIProj ρ P

def StIso : Prop :=
  ∀ (G G₁ H : Type) [Group G] [TopologicalSpace G] [Group G₁] [TopologicalSpace G₁] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (π : G →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (j : G₁ →* G) (p : G →* G₁), Continuous j →
    (∀ x, p (j x) = x) → (∀ x g, p g = 1 → Commute (j x) g) → ∀ W, IsIrredSubrep (π.comp j) W →
      ∃ δ : IrrU G₁, IsIsotypic δ.π (π.comp j)

def StOp : Prop :=
  ∀ (G X H : Type) [Group G] [TopologicalSpace G] [NormedAddCommGroup X] [InnerProductSpace ℂ X] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (δ : G →* (X →L[ℂ] X)) (ρ : G →* (H →L[ℂ] H)), IsIrrUnitary δ →
    IsUnitaryRep ρ → IsIsotypic δ ρ → ∃ A : X → X → (H →L[ℂ] H),
      ∀ y ξ, ∀ T ∈ homIn δ ρ ⊤, ∀ x, A y ξ (T x) = ⟪ξ, x⟫_ℂ • T y

def StTensor : Prop := StOp → StFixVec → GlobalTheory.Published.UnitaryIrreducibleAdmissible →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GAd σ J →* (H →L[ℂ] H)), IsIrrUnitary π →
        ∀ R : ∀ v, IrrU (GPl σ J v), (∀ v, HasCompPl σ J v (R v).π π) →
          ∃ (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H), IsFactorisation σ J (fun v => (R v).π) ξ π B

end CompanionTheory.Rg.Fl

end
