import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDataDistinctPlacesCommute
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix GlobalTheory.FinPl GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceData_distinct_places_commute : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p p' : SplitPt D k) (n n' m m' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype m]
    [DecidableEq m] [Fintype m'] [DecidableEq m'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA →
    p'.UnitAA → p.v ≠ p'.v → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (α' : Frame p' S m')
    (β' : Frame p' T m) (LS : Lat S) (LT : Lat T) (f₀ g h : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ)
    (Ψ' : Matrix m m' k → ℂ), Vac ψ S T LS LT (· = p'.v) f₀ → Over ψ α β LS LT f₀ Ψ g →
      Over ψ α' β' LS LT g Ψ' h → ∃ g', Over ψ α' β' LS LT f₀ Ψ' g' ∧ Over ψ α β LS LT g' Ψ h := by
  first | exact @GlobalTheory.FinPl.overSwap | exact GlobalTheory.FinPl.overSwap | (intros; apply GlobalTheory.FinPl.overSwap <;> assumption)
