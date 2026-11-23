import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_detCharacter_of_irreducible_rank_le_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (c : Type) [Fintype c] [DecidableEq c] [Subsingleton c] (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL c k) V), IsSmooth σ → σ.IsIrreducible → ∃ ψ : kˣ →* ℂˣ, IsSmoothChar ψ ∧ Nonempty (σ.Equiv (detRep c ψ)) := by
  first | exact @GlobalTheory.SmGL.RankLeOne.exists_equiv_detRep | exact GlobalTheory.SmGL.RankLeOne.exists_equiv_detRep | (intros; apply GlobalTheory.SmGL.RankLeOne.exists_equiv_detRep <;> assumption)
