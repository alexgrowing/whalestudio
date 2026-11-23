import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver cechHc quotPart)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

open IndefiniteRowSideFullHecke.Kleiman2 (pnIdx pnField pnPt) in

theorem isStepData_dimZero (F : Type) [Field F] :
    IndefiniteRowSideFullHecke.Kleiman2.IsStepData F (pnPt F 0) () 0 0 (1 / 2) 2 1 1 1 := by
  refine ⟨IndefiniteRowSideFullHecke.Kleiman2.isModelWithBase_pnPt F 0, IndefiniteRowSideFullHecke.Kleiman2.relDim_pnPt F 0, IndefiniteRowSideFullHecke.Kleiman2.isNef_zero F _,
    by norm_num, by norm_num, by norm_num, le_rfl, ?_, one_ne_zero⟩
  have e : IndefiniteRowSideFullHecke.Kleiman2.stepL () (0 : Unit → ℤ) 2 1 - ((1 : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg () = 0 := by
    funext k
    simp [IndefiniteRowSideFullHecke.Kleiman2.stepL, IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  rw [e]
  simp only [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  intro c _
  simp

def ClaimVanishDimZero.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (μ : K → ℤ)
    (r : ℚ) (a : ℕ) (m : ℤ) (c₁ : ℕ) (σ : Ω),
    IndefiniteRowSideFullHecke.Kleiman2.IsStepData F y k₀ 0 μ r a m c₁ σ →
    ∃ c₀ : ℕ, ∀ b c : ℕ, c₀ ≤ c →
      Subsingleton (cechHc ι (quotPart F (mIdealOver F y))
        (b • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ μ a m + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) 1)

example (F : Type) [Field F] (h : ClaimVanishDimZero.Statement) :=
  h F Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 0) (IndefiniteRowSideFullHecke.Kleiman2.pnField F 0) (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 0) () 0 (1 / 2) 2 1 1 1
    (isStepData_dimZero F)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
