import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.FlagOnto

theorem exists_flag_rTup : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L →
    ∀ (t : TupU I U) (y : G0 L.Pg X.toD7.R.r), ∃ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
      rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) = y := by
  intro X px I hX U L hI hV hL t y
  obtain ⟨c, hc⟩ := hL.is.βX
  have hsep := GlobalTheory.ChainEquiv.places_sep L (mu0F (tuOf I U)) hL.is t
  obtain ⟨κ, -, hκP, hκr⟩ := GlobalTheory.ParahoricLift.liftsExist X.toD7.sp.X' L.βX (L.datXt t) L.ΛX _ hc hsep.1 hsep.2 y
  exact ⟨⟨(finHom X.toD7.sp.X').rangeRestrict κ, hκP, Subgroup.mem_top _⟩, hκr⟩

end GlobalTheory.Mem.R3.FlagOnto

end
