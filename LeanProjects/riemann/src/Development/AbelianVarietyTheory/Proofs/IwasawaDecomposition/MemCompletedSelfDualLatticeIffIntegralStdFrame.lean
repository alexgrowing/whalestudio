import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.SDFrameStd

theorem lamHat_iff_int : ∀ {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V 1 Λ 1 → ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, y ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ j, swapAE D (y j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D V Λ hβ y
  obtain ⟨c, hf, -, -, h1, h2⟩ := hβ
  have hset : (Λ : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext x
    constructor
    · intro hx
      have := h2 x hx
      simpa using this
    · intro hx
      have := h1 x hx
      simpa using this
  have e1 : y ∈ Formalism.L2.NTheta.LamHat V ↔ (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [← GlobalTheory.LevSplit.latHat_iff Λ y, hset]
  rw [e1, hf]
  simp only [inv_one, Units.val_one, one_mulVec]
  rfl

end GlobalTheory.Mem.SDFrameStd
