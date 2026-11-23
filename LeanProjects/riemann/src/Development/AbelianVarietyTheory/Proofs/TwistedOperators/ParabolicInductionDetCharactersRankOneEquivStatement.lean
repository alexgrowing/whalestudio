import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicInductionDetCharactersRankOneEquiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInduction_detCharacters_rank_one_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (c : α → Type) [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Nonempty ((multiProd g fun i => detRep (c i) (ψ i)).Equiv (detRep Unit (ψ (g.symm ()).1))) := by
  first | exact @GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit | exact GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit | (intros; apply GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit <;> assumption)
