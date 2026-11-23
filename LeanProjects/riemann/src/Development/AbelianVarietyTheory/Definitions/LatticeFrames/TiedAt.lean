import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.StepData GlobalTheory.SymBridge
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

section Gen
variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}
  {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP)

def GAt.emb : D.host.E →+* G.k := (ofSplit G.q).π.comp (incA D)

structure GAt.FrTie (fr : ∀ i, i ≤ D.R.m → Matrix (Fin (D.sp.X i).rank) (Fin (D.R.N i)) D.host.E)
    (y : ∀ i, Fin (D.R.N i) → D.host.E) : Prop where
  frX : ∀ i (hi : i ≤ G.s + 1) (hm : i ≤ D.R.m), ∃ e : XIx (Fin D.R.k) (Fin D.R.t) i ≃ Fin (D.R.N i), IsOrd xPos e ∧
    ∀ r a, (G.FX i hi).β r a = G.emb (fr i hm r (e a))
  frM : ∀ hm : G.s + 1 + 1 ≤ D.R.m, ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (G.s + 2) ⊕ Unit ≃ Fin (D.R.N (G.s + 1 + 1)),
    IsOrd (Sum.elim zPos fun _ => D.R.N D.R.m - 1) e ∧ ∀ r a, G.FM.β r a = G.emb (fr (G.s + 1 + 1) hm r (e a))
  coset : ∀ e : XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) ≃ Fin (D.R.N (G.s + 1)), IsOrd xPos e → ∀ a,
    G.emb (y (G.s + 1) (e a)) - G.S.y0 (Fin D.R.t) a ∈ 𝒪[G.k]

end Gen

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {Ch : ℕ → Type}
  (A : ColDat I l Z u Ch) {d : Dat (I.rec7 l Z) u}
  {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) (I.rec7 l Z).host.E}

def baseFr (i : ℕ) (hi : i ≤ B.R.m) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0)) :
    Matrix (Fin ((I.rec7 l Z).sp.X i).rank) (Fin (B.R.N i)) (I.rec7 l Z).host.E := fun r a =>
  Formalism.L2.Col.frsF I.sel (I.tup I.mu0) (A.p0 i).1.1 P (Pi.single a 1) (finCongr (rankN (I.rec7 l Z) i hi) r)

structure TiedAt {PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E} (G : GAt d τ PP)
    (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0)) : Prop where
  eq : P.1 = PP
  type : letI := G.fld; letI := G.val; letI := G.top; letI := G.loc
    AtType (k := G.k) I.Ch I.sel (I.tup I.mu0) (I.cst I.mu0) B.embLL P G.emb G.S
  fr : G.FrTie (fun i hi => baseFr A i hi P) fun i =>
    (Formalism.L2.Col.frsF I.sel (I.tup I.mu0) (A.p0 i).1.1 P).symm (Formalism.L2.Col.repY (A.p0 i).1.2)

def xiT (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (γ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) : ℂ :=
  B.embLL (Formalism.L2.Col.phiT B.fields.K (A.p0 i).1.1.deco.1 (A.p0 (i + 1)).1.1.deco.1
    (Matrix.toLin' (γ.reindex (finCongr (rankN (I.rec7 l Z) (i + 1) hi)) (finCongr (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))))))

def JoinG : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (Ch : ℕ → Type)
    (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) (A : ColDat I l Z u Ch)
    (d : Dat (I.rec7 l Z) u) τ cG (G : ∀ PP : d.c.Pg, GAt d τ PP.1), I.Ok → I.IsTw → PinColAt d F A → PinGBy G cG →
    d.c.Pg = Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0) → (∀ PP, ∃ P, TiedAt A (G PP) P) →
    ∀ eT, IsIdemSum eT ((B.primes X).vT u) → ∀ i (hi : i + 1 ≤ B.R.m) wT,
      IsRatDatum d.c.ψ _ _ eT (xiT A i hi) (A.vac i) wT → IsThetaFunO d.c.ψ _ _ wT →
      ∃ C : ℂ, C ≠ 0 ∧ A.w i = C • comb d.c.ψ _ _ (cG i) wT

end GlobalTheory.LocMod
end
