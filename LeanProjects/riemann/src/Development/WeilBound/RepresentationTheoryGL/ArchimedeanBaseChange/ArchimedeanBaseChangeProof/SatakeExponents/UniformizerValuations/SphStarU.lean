import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Eig

def SphStarU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ) (w : Pl E) (σ : SmIrr (UL n w)),
  GlobalTheory.SmGL.IsUnitarisable σ.ρ → Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1 → ∀ h₁ h₂, IsHecke (KL n w) h₁ → IsHecke (KL n w) h₂ →
    twTr σ.ρ (KL n w) (KL n w) (lconv h₁ h₂) LinearMap.id =
      twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id * twTr σ.ρ (KL n w) (KL n w) h₂ LinearMap.id ∧
    twTr σ.ρ (KL n w) (KL n w) (lstar h₁) LinearMap.id = starRingEnd ℂ (twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id) ∧
    twTr σ.ρ (KL n w) (KL n w) ((KL n w : Set (UL n w)).indicator 1) LinearMap.id = 1

end PositivityTheory.Rg.BcB.F.Eig

end
