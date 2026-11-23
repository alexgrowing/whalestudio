import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt.Side

set_option maxHeartbeats 3200000 in

theorem exportTie_upd : ∀ (D : D7) (nch : NChoice D) (s : Side D nch) kap lam err, Nonempty (GlobalTheory.SeriesTie.ExportTie s.YS s.v₀) → Nonempty (GlobalTheory.SeriesTie.ExportTie (s.upd kap lam err).YS (s.upd kap lam err).v₀) := by
  intro D nch s kap lam err ⟨Z⟩
  exact ⟨{
    ρ := Z.ρ
    good := Z.good
    pin := { Z.pin with }
    vec := Z.vec
    ν := Z.ν
    scalar := fun i j b => ⟨(Z.scalar i j b).ne, fun h => (Z.scalar i j b).norm h, fun h => (Z.scalar i j b).rat h⟩
    tie := Z.tie
    hecke := Z.hecke
    univ := Z.univ }⟩

end GlobalTheory.PlugPt.Side
