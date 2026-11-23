import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricParameterUniformStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalRepresentationInputsImplyStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy

def witDropA {hL : GlobalTheory.Published.LocalLanglandsGL} {N : NExt hL} {S : SExt} {Γ : GeoP} {A : AtP} {K : Ctx} {B : Base}
    {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {O : Obj2 (w.D Z)}
    (x : Wit (prmR (NEa hL N A) S Γ).s K w Z O) : Wit (prmR N S Γ).s K w Z O :=
  { x with nx := ⟨x.nx.1, x.nx.2.1⟩ }

theorem movable_NEa {hL : GlobalTheory.Published.LocalLanglandsGL} {N : NExt hL} {S : SExt} {Γ : GeoP} (A : AtP)
    (hs : PositionMv (prmR N S Γ).s) : PositionMv (prmR (NEa hL N A) S Γ).s := by
  intro K B f T w Z O x Nd h O' hO' col n
  obtain ⟨t, hobj, hrx, ⟨c⟩, hsx, hox⟩ := hs K B f T w Z O (witDropA x) Nd h O' hO' col n
  exact ⟨t, hobj, hrx, ⟨⟨c.1, c.2, x.nx.2.2⟩⟩, hsx, hox⟩

theorem exBL_NEa : HypA → HypH → PrM → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (A : AtP),
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
      Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) →
    PositionMv (prmR N SExt.none Γ).s →
    ExBL KPx (IsBuiltE (prmR (NEa hL N A) SExt.none Γ).s) (IsGoodE (prmR (NEa hL N A) SExt.none Γ).s)
      (IsLinked (prmR (NEa hL N A) SExt.none Γ)) := by
  intro ha hh pm hL N Γ A hb hs
  exact GlobalTheory.T.geometric_parameter_uniform pm.m14 hh.cover ha.a5 ha.a7 ha.a8 ha.a9 ha.a10 ha.a6 ha.a22 ha.a23 ha.a1 hL (NEa hL N A) Γ _ rfl
    (fun K B f T w Z Wt p0 t nch n xd c e => hb K B f T w Z Wt p0 t nch n xd c e.1) (movable_NEa A hs)
    (GlobalTheory.T.local_representation_inputs_imply pm.m1 pm.m2 pm.m3 pm.m4 pm.m5 pm.m6 pm.m7 pm.m8 pm.m9 pm.m10 pm.m11 pm.m12 pm.m13 pm.m14 hL _ _ _)

end GlobalTheory.Mem.LiteralAutomorphy

end
