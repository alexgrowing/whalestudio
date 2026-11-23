import Formalism.LocalToGlobal.ClassSK
import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPtTw

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2.GlobalTheoryTheory.PerDec

open Formalism.MainNotions.RT.PeriodPointConditions

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

def PeriodDecompositionBase (T : Formalism.L2.TiedDataSK ex) : Prop :=
  ∀ u : D.what₂.Word, PerDec0At (T.cols.forms u)

end

def LevelZeroPeriodReduction (D : D7) : Prop :=
  (∀ u : D.what₂.Word, PerDec0 D u) → Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl D

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

end

section Tw

attribute [local instance] MemberForms.clsPFin

open Formalism.L2.Forms

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

def resCTw (T : Formalism.L2.TiedDataSK ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (c : (ex.tw.fm u μ).clsP) (z : (D.PTw u μ).Wrow) : (D.PTw u μ).Wrow :=
  open Classical in
  (T.tw.pt.val u μ hμ).eW.symm (fun c' => if c' = c then (T.tw.pt.val u μ hμ).eW z c' else 0)

def pcLTw (T : Formalism.L2.TiedDataSK ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (c : (ex.tw.fm u μ).clsP) (z : (D.PTw u μ).Wrow) (G : (D.PTw u μ).Mt) : ℂ :=
  ((Nat.card ((ex.tw.fm u μ).stabilizer₂ c) : ℕ) : ℂ) *
    (ex.tw.fm u μ).ipP (resCTw T u μ hμ c (T.tw.ptE.jM u μ G)) (resCTw T u μ hμ c z)

def PerDecTwAt (T : Formalism.L2.TiedDataSK ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) : Prop :=
  ∀ x ∈ (ex.tw.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier, ∀ c,
    ∃ y : D.what₂.LL, D.what₂.embLL y = pcLTw T u μ hμ c ((ex.tw.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) ∧
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ∉ Y.Qp μ → y = 0 ∨ 0 ≤ vAdd (D.plEq w) y

def PeriodDecompositionTwisted (T : Formalism.L2.TiedDataSK ex) : Prop :=
  ∀ u μ (hμ : μ ≠ D.what₂.mu0), PerDecTwAt T u μ hμ

def PerTwRed (T : Formalism.L2.TiedDataSK ex) : Prop :=
  PeriodDecompositionTwisted T → Formalism.MainNotions.WeightDegreeSizes.TwistedPeriodIntegral D Y ex.tw

def PtTwLatM (T : Formalism.L2.TiedDataSK ex) : Prop :=
  ∀ u μ (hμ : μ ≠ D.what₂.mu0) (h1 : 1 ≤ D.R.m),
    ValuationCompatibleChart (ex.tw.fm u μ) (twYS T.tw.ch T.cols.forms u μ D.R.m le_rfl) (fun _ => True) (T.tw.ch.chOf u μ D.R.m)
      (lat := fun c => latCrd D D.R.m le_rfl (T.tw.ch.lat u μ D.R.m c)) (T.tw.forms.ch u μ hμ D.R.m h1 le_rfl)

def PtTwLatP (T : Formalism.L2.TiedDataSK ex) : Prop :=
  ∀ u μ (hμ : μ ≠ D.what₂.mu0) (w : D.what₂.places.Pl) (x : (ex.tw.fm u μ).ptLat.V),
    x ∈ (ex.tw.fm u μ).SP w ↔
      ∀ (c : (ex.tw.fm u μ).clsP) (B : GL (Fin (D.R.N D.R.m - 1)) D.host.E),
        IsLocBasis (D.what₂.places.resChar w) ((T.tw.pt.cls u μ hμ).lat c : Set _) B →
        ∃ Pc ∈ IntSpan D w (ex.tw.fm u μ).sg, (T.tw.pt.val u μ hμ).eW ((ex.tw.fm u μ).ptEmb x) c =
          fnOf _ (shiftOf (sgTG (ex.tw.fm u μ))) (atInf (Formalism.L2.Forms.embT D) (B⁻¹ : GL (Fin (D.R.N D.R.m - 1)) D.host.E).1) Pc

def TwistedLatticeConditions (T : Formalism.L2.TiedDataSK ex) : Prop :=
  PtTwLatM T ∧ PtTwLatP T

def LowerTwistedAtTuples (T : Formalism.L2.TiedDataSK ex) : Prop :=
  ∀ u μ, μ ≠ D.what₂.mu0 → Formalism.MainNotions.DIV.HookProducts.AdmPtTw.LowerTieTwAt D ex.tw u μ

end Tw

end Formalism.L2.GlobalTheoryTheory.PerDec

end
