import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.EqPOf
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def MuOneL (B : Ker.Base D cc δ) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → Even N' → SD D L → SD D L₁ →
    ∃ S₂ S₃ : Finset (TaylorLogMetric.VC D N N'),
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) S₂ ∧
      IsReps (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) S₃ ∧
      tripleMu (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N'))
        (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) S₂ S₃ = 1

def MuOneR (B : Ker.Base D cc δ) : Prop :=
  ∀ N N' (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Even N → Even N' → SD D L' → SD D L'' →
    ∃ S₂ S₃ : Finset (TaylorLogMetric.VC D N N'),
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') S₂ ∧
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L'') S₃ ∧
      tripleMu (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L')
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L'') S₂ S₃ = 1

theorem tripleData_of {B : Ker.Base D cc δ} (hL : B.LatAll) {N N' : ℕ}
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

theorem left_move_triangles_of_unit {B : Ker.Base D cc δ} (hL : B.LatAll) (hM : MuOneL B) : Tr0L D B.tor := by
  intro N N' L L₁ hN hN' h1 h2 G hG
  obtain ⟨S₂, S₃, hS₂, hS₃, hμ⟩ := hM N N' L L₁ hN hN' h1 h2
  have hT := tripleData_of hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' h1 (sd0 N')) (admissible_of_integral_conj_le hN hN' h2 (sd0 N'))
  funext v
  have := tripleFormula _ _ _ _ _ _ hT S₂ S₃ hS₂ hS₃ G (fun x hx z => hG.2 x hx z) v
  rw [hμ, one_mul] at this
  exact this

theorem right_move_triangles_of_unit {B : Ker.Base D cc δ} (hL : B.LatAll) (hM : MuOneR B) : Tr0R D B.tor := by
  intro N N' L' L'' hN hN' h1 h2 G hG
  obtain ⟨S₂, S₃, hS₂, hS₃, hμ⟩ := hM N N' L' L'' hN hN' h1 h2
  have hT := tripleData_of hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' (sd0 N) h1) (admissible_of_integral_conj_le hN hN' (sd0 N) h2)
  funext v
  have := tripleFormula _ _ _ _ _ _ hT S₂ S₃ hS₂ hS₃ G (fun x hx z => hG.2 x hx z) v
  rw [hμ, one_mul] at this
  exact this

end Formalism.L2.PairingIndexBounds.Eq
