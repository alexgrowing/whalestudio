import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WeightUpdateAtPlace
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.FrobeniusSqIterateTeichmuller

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

abbrev sysC {p : ℕ} [Fact p.Prime] (G : GAtP p) (Fl : Fills G) (Lv : Levels Fl) (Ch : Chain Lv)
    (std : ∀ v, Std p (G.P.n' v) G.P.m Fl.t Fl.mm Fl.c G.P.r (Fl.TT v) (Fl.a v) (Fl.b v) (G.P.lam0 v) (Fl.w v))
    (hfin : ∀ j c, (Lv.lev j c).FinClasses) (h0 : (p : G.O) ≠ 0) : Sys p :=
  sysOf G Fl Lv Ch std hfin h0 fun v => omOf p (G.P.n' v) (G.P.setting v).even (G.P.setting v).two_le

end Formalism.L2.G.Pend
