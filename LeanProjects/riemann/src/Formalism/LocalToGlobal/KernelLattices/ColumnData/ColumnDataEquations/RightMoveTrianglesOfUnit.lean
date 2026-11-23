import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.EqPOf
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def MuOneL (B : Cd.Base D cc δ) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → Even N' → SD D L → SD D L₁ →
    ∃ S₂ S₃ : Finset (TaylorLogMetric.VC D N N'),
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) S₂ ∧
      IsReps (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) S₃ ∧
      tripleMu (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N'))
        (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) S₂ S₃ = 1

def MuOneR (B : Cd.Base D cc δ) : Prop :=
  ∀ N N' (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Even N → Even N' → SD D L' → SD D L'' →
    ∃ S₂ S₃ : Finset (TaylorLogMetric.VC D N N'),
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') S₂ ∧
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L'') S₃ ∧
      tripleMu (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L')
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L'') S₂ S₃ = 1

theorem tripleData_of {B : Cd.Base D cc δ} (hL : B.LatAll) {N N' : ℕ}
    {L₁ L₂ L₃ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' L₂' L₃' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (a1 : TaylorLogMetric.admitted D N N' L₁ L₁') (a2 : TaylorLogMetric.admitted D N N' L₂ L₂') (a3 : TaylorLogMetric.admitted D N N' L₃ L₃') :
    TripleData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂') (TaylorLogMetric.La D B.tor L₃ L₃') where
  herm := formV_herm' _ _ _ _
  sd₁ := (hL.1 N N' _ _ a1).1
  sd₂ := (hL.1 N N' _ _ a2).1
  sd₃ := (hL.1 N N' _ _ a3).1
  sc₁ := (hL.1 N N' _ _ a1).2
  sc₂ := (hL.1 N N' _ _ a2).2
  sc₃ := (hL.1 N N' _ _ a3).2
  i₁₂ := (hL.2 N N' _ _ _ _ a1 a2).1
  i₂₁ := (hL.2 N N' _ _ _ _ a1 a2).2
  i₁₃ := (hL.2 N N' _ _ _ _ a1 a3).1
  i₃₁ := (hL.2 N N' _ _ _ _ a1 a3).2
  i₂₃ := (hL.2 N N' _ _ _ _ a2 a3).1
  i₃₂ := (hL.2 N N' _ _ _ _ a2 a3).2

theorem left_move_triangles_of_unit {B : Cd.Base D cc δ} (hL : B.LatAll) (hM : MuOneL B) : Tr0L D B.tor := by
  intro N N' L L₁ hN hN' hSL hSL1 G hG
  obtain ⟨S₂, S₃, h2, h3, hmu⟩ := hM N N' L L₁ hN hN' hSL hSL1
  have hA0 : TaylorLogMetric.admitted D N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') := ⟨hN, hN', sd0 N, sd0 N'⟩
  have hA1 : TaylorLogMetric.admitted D N N' L (StandardLatticesGL3.stdL D N') := ⟨hN, hN', hSL, sd0 N'⟩
  have hA2 : TaylorLogMetric.admitted D N N' L₁ (StandardLatticesGL3.stdL D N') := ⟨hN, hN', hSL1, sd0 N'⟩
  have hT := tripleData_of hL hA0 hA1 hA2
  funext v
  have h5 := tripleFormula _ _ _ _ _ _ hT S₂ S₃ h2 h3 G hG.2 v
  rw [hmu, one_mul] at h5
  simp only [Cd.Iop_eq]
  exact h5

theorem right_move_triangles_of_unit {B : Cd.Base D cc δ} (hL : B.LatAll) (hM : MuOneR B) : Tr0R D B.tor := by
  intro N N' L' L'' hN hN' hSL hSL1 G hG
  obtain ⟨S₂, S₃, h2, h3, hmu⟩ := hM N N' L' L'' hN hN' hSL hSL1
  have hA0 : TaylorLogMetric.admitted D N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') := ⟨hN, hN', sd0 N, sd0 N'⟩
  have hA1 : TaylorLogMetric.admitted D N N' (StandardLatticesGL3.stdL D N) L' := ⟨hN, hN', sd0 N, hSL⟩
  have hA2 : TaylorLogMetric.admitted D N N' (StandardLatticesGL3.stdL D N) L'' := ⟨hN, hN', sd0 N, hSL1⟩
  have hT := tripleData_of hL hA0 hA1 hA2
  funext v
  have h5 := tripleFormula _ _ _ _ _ _ hT S₂ S₃ h2 h3 G hG.2 v
  rw [hmu, one_mul] at h5
  simp only [Cd.Iop_eq]
  exact h5

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
