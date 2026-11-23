import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TNZ
def Step_cuspSupp_alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (X : Type)
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin d) k) X), IsSmooth σ → σ.IsIrreducible →
    ∀ η : kˣ →* ℂˣ, IsSmoothChar η → HasDetVec σ η →
      ∃ μ : Fin d → kˣ →* ℂˣ, (∀ j, IsSmoothChar (μ j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ j u = η u) ∧
        IsCuspSupport σ (fun _ => 1) (fun j => detRep (Fin 1) (μ j))
def Step_prodIrr_alt : Prop :=
  _root_.UpperTheory.TNZ.Step_cuspSupp_alt → _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s N : ℕ) (d : Fin s → ℕ)
    (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)] [∀ b, Module ℂ (X b)]
    (σ : ∀ b, Representation ℂ (GL (Fin (d b)) k) (X b)), (∀ b, IsSmooth (σ b)) → (∀ b, (σ b).IsIrreducible) →
    ∀ η : Fin s → kˣ →* ℂˣ, (∀ b, IsSmoothChar (η b)) → (∀ b, HasDetVec (σ b) (η b)) →
    (∀ b c, b ≠ c → ∃ u : kˣ, valuation k (u : k) = 1 ∧ η b u ≠ η c u) →
      (multiProd (stdBlocks d hd) σ).IsIrreducible
def GMainAlt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (ε : EpsFamily A) (rc : IrrGL (w.adicCompletion E) → WD h), Laws a ha ε rc → _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt →
    ∀ (s : ℕ) (d : Fin s → ℕ) (η : Fin s → (w.adicCompletion E)ˣ →* ℂˣ), (∀ b, IsSmoothChar (η b)) →
    (∀ b c, b ≠ c → ∃ t : Ine (F := E) A, η b (a (ineIncl h t)) ≠ η c (a (ineIncl h t))) →
    ∀ (x : IrrGL (w.adicCompletion E)) (hd : ∑ b, d b = x.1),
      ((rc x).mono0 ∧ ∀ t : Ine (F := E) A,
          (rc x).charPol (ineIncl h t) = ∏ b, (X - C ((η b (a (ineIncl h t)) : ℂˣ) : ℂ)) ^ d b) ↔
        IsTwSphProd x.rep d hd η
end UpperTheory.TNZ
end
end
