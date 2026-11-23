import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 in

def DictAt : Prop := ∀ (t : T) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d →
  d.z = 1 → d.P = locPl ch.G t → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.pS p).rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.pT p).rank → D.host.E))
      (κ : ℂ) (n : ℕ) (r : Fin n → Qbar) (s : Fin n → VC D (ch.G.pS p).rank (ch.G.pT p).rank),
      SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ (∀ i, k • s i ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) ∧
      (∀ i, IsIntegral ℤ ((k : Qbar) ^ (D.R.f * (ch.G.pS p).rank * (ch.G.pT p).rank) * r i)) ∧
      (∀ ρ : Qbar →+* ℂ, ∑ i, ‖ρ (r i)‖ ≤ 1) ∧
      (∀ (q : ℕ) [Fact q.Prime], EqAt D q (latAt ch.S.toGridChoice p.small x) (stdL D _) →
        EqAt D q (latAt ch.S.toGridChoice p.big y) (stdL D _) →
          EqAt D q Ls (stdL D _) ∧ EqAt D q Lt (stdL D _) ∧ ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧
      ∀ mon, jetTab ch.W ch.S.N.frC p (ch.S.Z.vec d) (x * ch.S.N.u _) (y * ch.S.N.u _) mon =
        ch.S.Z.c0 p * opp p (((mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar ch.G p)) 1) fun z => κ * ∑ i, (r i : ℂ) *
            Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) (s i)
              (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
                (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) z)

end Claims

def DictK : Prop := BigC fun _ ch _ _ => DictAt ch

end GlobalTheory.SumSize

end
