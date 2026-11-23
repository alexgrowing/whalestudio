import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

namespace GlobalTheory.RatMoveJets

theorem exists_unitary_ratCoord {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (r : FinPt G X) (hr : GlobalTheory.MovedKappaEx.RatFin (G.V X) r) :
    ∃ U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E, GlobalTheory.RatMoveJets.RatCoord (G.V X) (S.N.fr X) r U := by
  obtain ⟨γ, hγ, hf⟩ := hr
  obtain ⟨γ', h1, h2⟩ := id hγ
  have hG : star γ'.1 * (G.V X).gram * γ'.1 = (G.V X).gram := h1
  have hmt : Formalism.L2.Theta.mt (G.V X) γ = γ'.1.map (incA D) := congrArg Units.val h2.symm
  set F := (S.N.fr X).1 with hFdef
  set Fi := ((S.N.fr X)⁻¹ : GL (Fin (G.V X).rank) D.host.E).1 with hFidef
  have hF : star F * (G.V X).gram * F = 1 := S.N.fr_on X hX
  have e1 : Fi * F = 1 := by rw [hFdef, hFidef]; exact Units.inv_mul _
  have e2 : F * Fi = 1 := by rw [hFdef, hFidef]; exact Units.mul_inv _
  have hGram : star Fi * Fi = (G.V X).gram := by
    have : star Fi * (star F * (G.V X).gram * F) * Fi = (G.V X).gram := by
      calc star Fi * (star F * (G.V X).gram * F) * Fi = star (F * Fi) * (G.V X).gram * (F * Fi) := by
            rw [star_mul]; simp only [Matrix.mul_assoc]
        _ = (G.V X).gram := by rw [e2, star_one, Matrix.one_mul, Matrix.mul_one]
    rw [hF, Matrix.mul_one] at this
    exact this
  have hU : star (Fi * γ'.1 * F) * (Fi * γ'.1 * F) = 1 := by
    calc star (Fi * γ'.1 * F) * (Fi * γ'.1 * F) = star F * (star γ'.1 * (star Fi * Fi) * γ'.1) * F := by
          simp only [star_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hGram, hG]; exact hF
  refine ⟨⟨Fi * γ'.1 * F, Matrix.mem_unitaryGroup_iff'.2 hU⟩, γ, hγ, hf, ?_⟩
  rw [hmt]
  congr 1
  change γ'.1 = F * (Fi * γ'.1 * F) * Fi
  simp only [← Matrix.mul_assoc, e2, Matrix.one_mul]
  rw [Matrix.mul_assoc, e2, Matrix.mul_one]

end GlobalTheory.RatMoveJets
