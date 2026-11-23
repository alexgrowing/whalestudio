import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitDegreeOnePlaceEqExp
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemUnderSq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilCharacter_splitDegreeOne_place_eq_exp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → (Formalism.L2.Col.qOf PP).Prime → ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk → ∀ (a : D.host.E) (b : ℤ) (n : ℕ), Formalism.L2.Col.IntAt PP (D.host.xi0 * a - (b : D.host.E) / (Formalism.L2.Col.qOf PP : D.host.E) ^ n) → (ψk ((ofSplit q).pr a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (Formalism.L2.Col.qOf PP : ℂ) ^ n) := by
  first | exact @GlobalTheory.SplitDegOnePow.weilChar_pr_eq_exp | exact GlobalTheory.SplitDegOnePow.weilChar_pr_eq_exp | (intros; apply GlobalTheory.SplitDegOnePow.weilChar_pr_eq_exp <;> assumption)
