import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.RealSt
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictDef

noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.KCo

def beta (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y)

def infV {F : Type} [Field F] [NumberField F] {κ : Type} (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i)

def IsTr {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (w : (κ → AF F) × (κ → AF F)) (f g : SInf F κ) : Prop :=
  ∀ x, g x = Complex.exp (-(2 * Real.pi * Complex.I) *
    ((beta F κ x (infV w.2) + beta F κ (infV w.1) (infV w.2) / 2 : ℝ) : ℂ)) * f (x + infV w.1)

def PureSt : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
  (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ), (∃ g, IsTr w f g) ∧ ∀ φ : ∀ v : Pl F, (κ → Fv F v) → ℂ,
    (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    (∀ᶠ v in cofinite, schr (psiV ψ v) (locW v w) (φ v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
    ∀ g, IsTr w f g → schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g fun v => schr (psiV ψ v) (locW v w) (φ v)

def FinSt : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
  (S : ((κ → AF F) × (κ → AF F)) ≃ₗ[AF F] ((κ → AF F) × (κ → AF F))),
  (∀ w w', (S w).1 ⬝ᵥ (S w').2 - (S w').1 ⬝ᵥ (S w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) →
  ∃ ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ),
    (∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _)) ∧
    (∀ v w, ∀ φ ∈ SB (κ → Fv F v), ev v (schr (psiV ψ v) (locW v w) φ) = schr (psiV ψ v) (locW v (S w)) (ev v φ)) ∧
    ∀ᶠ v in cofinite, ev v (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def InfSt : Prop := ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
  (S : ((κ → AF F) × (κ → AF F)) ≃ₗ[AF F] ((κ → AF F) × (κ → AF F))),
  (∀ w w', (S w).1 ⬝ᵥ (S w').2 - (S w').1 ⬝ᵥ (S w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) →
  ∃ ei : SInf F κ ≃L[ℂ] SInf F κ, ∀ w f g, IsTr w f g → IsTr (S w) (ei f) (ei g)

end PositivityTheory.Mix
