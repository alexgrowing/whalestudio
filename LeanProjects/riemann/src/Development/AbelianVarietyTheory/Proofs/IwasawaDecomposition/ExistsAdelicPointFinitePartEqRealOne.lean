import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.FinPartLift

theorem exists_gfC_finHom_eq : ∀ {D : D7} (V : HSp D) (g : Bridge.Gf V), ∃ α ∈ GfC V, finHom V α = (g : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D V g
  obtain ⟨β, hβ⟩ := g.2
  obtain ⟨α, hα, e⟩ := GlobalTheory.AdIsomCorrection.exists_finE V (Formalism.IndefR.Lev.finE V β) (GlobalTheory.LevSplit.finE_mem_UA V β)
  refine ⟨α, hα, ?_⟩
  rw [← hβ]
  apply Units.ext
  ext i j
  have h := congrArg (fun x : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => x.val i j) e
  exact (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective h

end GlobalTheory.Mem.FinPartLift
