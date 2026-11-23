import Mathlib
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre

noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV NumberField IsDedekindDomain

def stabSet {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG)
    (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q) (q : UF X.E n → Prop) : Set (Matrix (Fin n) (Fin n) D.host.E × ℂ) :=
  {g | ∃ a : FrmG Λ Θ, a • p = p ∧ q a.1 ∧ g = (matE s a.1.1, s.σ₀ ((Λ.chr a.2.1 * Θ.chr a.2.2 : X.Kˣ) : X.K))}

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

def StabPin (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (G : StabDat (D.chTw u μ)) : Prop :=
  ∃ (pt : ∀ i, i ≤ t.m2 + 1 → (D.chTw u μ).cls i → ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i)
    (ix : ∀ i, i ≤ t.m2 → (D.chTw u μ).cls i → (t.idx μ).β i)
    (yb : (D.chTw u μ).cls (t.m2 + 1) → Set (Sp t.X.E (D.R.N (t.m2 + 1))))
    (pT : (D.chTw u μ).cls (t.m2 + 1 + 1) → ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1 + 1)),
    (∀ i (hi : i ≤ t.m2 + 1) c, (t.rd u μ).N i c = (pt i hi c).deco.1.N) ∧
    (∀ c', yb c' ∈ ybSet t.sel (t.tup μ) (t.cst μ) (pt (t.m2 + 1) le_rfl c').deco.1.N) ∧
    (∀ i (hi : i < t.m2) c c' x, (t.rd u μ).Xi i c c' x = t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (ix i hi.le c)
      (ix (i + 1) hi c') (pt i (by omega) c) (pt (i + 1) (by omega) c') x)) ∧
    (∀ c c' x, (t.rd u μ).Xi t.m2 c c' x = t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (ix t.m2 le_rfl c)
      (pt t.m2 (Nat.le_succ _) c) (pt (t.m2 + 1) le_rfl c') (yb c') x)) ∧
    (t.rd u μ).TopPinAt t.Ch t.sel (t.tup μ) (t.cst μ) t.seam.σ₀ (t.word u) t.m2 (pt (t.m2 + 1) le_rfl) yb pT ∧
    (∀ i, 1 ≤ i → ∀ (hi : i ≤ t.m2) c, G i c = stabSet t.seam ((t.idx μ).levG i (ix i hi c)) ((t.idx μ).levQ i (ix i hi c))
      (pt i (Nat.le_succ_of_le hi) c) fun _ => True) ∧
    (∀ (b : (t.idx μ).β (t.m2 + 1)) c, G (t.m2 + 1) c = stabSet t.seam ((t.idx μ).levG (t.m2 + 1) b) ((t.idx μ).levQ (t.m2 + 1) b)
      (pt (t.m2 + 1) le_rfl c) fun γ => (fun v => γ.1 v) '' yb c = yb c) ∧
    ∀ c, G (t.m2 + 1 + 1) c = stabSet t.seam (twLt t.Ch (t.m2 + 1 + 1)) (twTt (R := D.R) t.sel (t.tup μ) (t.m2 + 1 + 1)) (pT c) fun _ => True

def FormsPin (t : KerEntTied ex) : Prop :=
  ∀ u μ, DV.Used D μ → ∃ G : StabDat (D.chTw u μ), FormsAre (ex.tw.fm u μ) (t.O u μ) G ∧ StabPin t u μ G

structure ColSide (t : KerEntTied ex) : Prop where
  fields : t.X.Ok
  sel : IsSel t.X t.sel
  bad : (∀ i, t.Pr.g i ∈ t.S) ∧ (∀ v, t.Pr.T v ∈ t.S) ∧ (∀ l ∈ D.host.small, l ∈ t.S) ∧ D.host.q ∈ t.S
  chOk : t.Ch.Ok
  chars : ∃ eta, t.Ch.Tied t.glob.σ₀ (fun j τ => (D.hc (t.seam.iT τ)).e j) t.glob.mu0 eta
  sharp : ∀ μ, (t.cst μ).sharp = true
  deep : ∀ μ, D.R.m ≤ (t.cst μ).A ∧ 2 * (t.cst μ).M ≤ twTopDepth D.R
  repOne : ∀ μ j, j ≤ t.m2 + 1 → ∀ (b : (t.idx μ).β j) (P : rowSG t.Pr t.sel (t.tup μ)), P.1 ∈ t.Pr.vGs → (t.idx μ).h j b P = 1

end GlobalTheory.KerJ
