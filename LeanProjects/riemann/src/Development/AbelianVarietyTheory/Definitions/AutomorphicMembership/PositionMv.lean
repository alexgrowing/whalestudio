import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PositionMv (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) (x : Wit 𝒮 K w Z O)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (O' : Obj2 (w.D (Db.setDivZ Z N h))), O' = O.tr N h →
    ∀ (col : ColumnDataSplitPrimes K w (Db.setDivZ Z N h)) (n : NchT w (Db.setDivZ Z N h) x.Wt O'.nch),
    ∃ t : RowsT K w (Db.setDivZ Z N h) x.Wt O'.p0, ObjT O' t ∧
      Nonempty (𝒮.Rx K B f T w (Db.setDivZ Z N h) x.Wt O'.p0 t) ∧
      Nonempty (𝒮.Nx K B f T w (Db.setDivZ Z N h) x.Wt O'.p0 t O'.nch n O'.xd) ∧
      Nonempty (𝒮.Sx K B f T w (Db.setDivZ Z N h) x.Wt O'.p0 t col.toColT) ∧
      Nonempty (𝒮.Ox K B f T w (Db.setDivZ Z N h) x.Wt O' t)

def WitMv (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) (x : Wit 𝒮 K w Z O)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), EntC x.ker →
    ∃ x' : Wit 𝒮 K w (Db.setDivZ Z N h) (O.tr N h), EntC x'.ker

end GlobalTheory.Mem.Top.Bl

end
