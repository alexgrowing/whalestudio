import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.InertJacobiLevels.TiesAsm

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def TieHyp.tiesAtY {D : D7} {gatT : GatTies D} {L0 : SizeData₂ D} {kapI : KapI} {ep : ℕ → ℕ}
    (H : TieHyp gatT L0 kapI ep) (C : FC) (Λ : LatIn D) (Gy : G.LatInst D)
    (hGy : G.LatTied gatT (H.Gx C.GK C.Cr Λ) Gy)
    (hl : ∀ w, G.LatticeLengthsAtPlace (H.Gx C.GK C.Cr Λ) Gy C.GK w) : TiesAt C (H.L C.GK C.Cr Λ) gatT where
  Gx := H.Gx C.GK C.Cr Λ
  Gy := Gy
  supp_sat := H.supp_sat C.GK C.Cr Λ
  tw_supp := H.tw_supp C.GK C.Cr Λ
  fills := H.fills C.GK C.Cr Λ
  lats0 := fun w u h1 h2 => (hl w).2 u h1 h2
  latTied := hGy
  drop_iff := fun p _ => H.drop_iff C.GK C.Cr Λ p

def TieHyp.tiesAt {D : D7} {gatT : GatTies D} {L0 : SizeData₂ D} {kapI : KapI} {ep : ℕ → ℕ}
    (H : TieHyp gatT L0 kapI ep) (C : FC) (Λ : LatIn D)
    (hl : ∀ w, G.LatticeLengthsAtPlace (H.Gx C.GK C.Cr Λ) (H.Gy C.GK C.Cr Λ) C.GK w) : TiesAt C (H.L C.GK C.Cr Λ) gatT where
  Gx := H.Gx C.GK C.Cr Λ
  Gy := H.Gy C.GK C.Cr Λ
  supp_sat := H.supp_sat C.GK C.Cr Λ
  tw_supp := H.tw_supp C.GK C.Cr Λ
  fills := H.fills C.GK C.Cr Λ
  lats0 := fun w u h1 h2 => (hl w).2 u h1 h2
  latTied := H.latTied C.GK C.Cr Λ
  drop_iff := fun p _ => H.drop_iff C.GK C.Cr Λ p

end Formalism.MainNotions.Inhab

end
