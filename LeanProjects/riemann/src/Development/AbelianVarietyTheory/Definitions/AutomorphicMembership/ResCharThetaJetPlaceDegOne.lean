import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure GJStage (B : Base) (C : Cols B) where
  vol : @HSpace B.host.E _ _ B.host.cmStar → ℝ
  vol_pos : ∀ W, 0 < vol W
  cd : CDHaar
  jet : ThetaJet B.R B.host
  jetU : jet.Sit → B.Word
  jetL : ∀ i, (C.mem (jetU i)).C.cls (jet.jOf i - 1)
  jetL' : ∀ i, (C.mem (jetU i)).C.cls (jet.jOf i)
  jetW : jet.Sit → B.places.Pl
  jetW_l : ∀ i, B.places.resChar (jetW i) = (jet.loc i).l
  jetTau : ∀ i, ZMod (jet.loc i).d → (Tau B.R)
  jetW1 : jet.Sit1 → B.places.Pl
  resChar_thetaJetPlaceDegOne : ∀ i, B.places.resChar (jetW1 i) = (jet.loc1 i).l
  jetTau1 : jet.Sit1 → (Tau B.R)
  jetU1 : jet.Sit1 → B.Word
  jetL1 : ∀ i, (C.mem (jetU1 i)).C.cls (jet.j1Of i - 1)
  jetL1' : ∀ i, (C.mem (jetU1 i)).C.cls (jet.j1Of i)
  gx : GlobalExtra B.LL (Tau B.R)
  gat : ∀ u (w : B.places.Pl), GIdx B.host (C.mem u).A.T (B.places.resChar w) →
    Formalism.MainNotions.G.GAtP (B.places.resChar w)
  gat_d : ∀ u w h, (gat u w h).d = Module.finrank ℂ (C.mem u).A.Mu0

end GlobalTheory.Mem

end
