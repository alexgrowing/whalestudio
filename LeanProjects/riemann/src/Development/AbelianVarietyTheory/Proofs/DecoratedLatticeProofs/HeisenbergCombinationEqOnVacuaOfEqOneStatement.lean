import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationEqOnVacuaOfEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCombination_eq_on_vacua_of_eq_one : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (q i).v) → (∀ p, P p ↔ ∃ i, (q i).v = p) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ c₁ c₂ : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P c₁ → GlobalTheory.FinPl.CombAt P c₂ → ∀ f₀, GlobalTheory.FinPl.Vac ψ S T LS LT P f₀ → f₀ ≠ 0 → comb ψ S T c₁ f₀ = comb ψ S T c₂ f₀ → ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT P f → comb ψ S T c₁ f = comb ψ S T c₂ f := by
  first | exact @GlobalTheory.FinPl.Transfer.comb_eq_on_vacua | exact GlobalTheory.FinPl.Transfer.comb_eq_on_vacua | (intros; apply GlobalTheory.FinPl.Transfer.comb_eq_on_vacua <;> assumption)
