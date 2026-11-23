import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HintSmaller

theorem hint_eq_of_le : ∀ {H : Type} [Group H] (K S : Subgroup H) (u : H → ℂ), S ≤ K → S ≤ rStab u →
    S.relIndex K ≠ 0 → (Function.support fun q : H ⧸ S => u q.out).Finite →
    hint K u = ((S.relIndex K : ℂ))⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  intro H _ K S u hSK hSu hfin _
  exact GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K S u hSK hSu hfin

end GlobalTheory.CompanionTheory.HintSmaller
