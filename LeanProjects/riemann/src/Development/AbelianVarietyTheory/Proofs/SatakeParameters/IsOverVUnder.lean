import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdLawAtOfSteps

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section MidDatum

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  (A : AdData t u μ St) (a : 𝓞 D.host.E)

def mvN (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)) :=
  Submodule.span (𝓞 t.X.E) ((fun (y : Fin (D.R.N i) → D.host.E) (l : Fin (D.R.N i)) => t.seam.iE.symm (y l)) ''
    (latCo D.sp (gramN D i hi) (A.crd i hi) a x.1 ((St i hi).K β).lev.Lb : Set (Fin (D.R.N i) → D.host.E)))

def vUnder (P : HeightOneSpectrum (𝓞 t.X.E)) : HeightOneSpectrum (𝓞 D.host.F) :=
  HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P)

theorem isOver_vUnder (P : HeightOneSpectrum (𝓞 t.X.E)) : IsOver (vUnder (t := t) P) (seamP t.seam P) := by
  unfold IsOver vUnder
  rw [HeightOneSpectrum.under_asIdeal]

def vecAt {n : ℕ} (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (w : Sp t.X.E n) : Fin n → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F :=
  fun l => prV (E := D.host.E) v (pullV (F := D.host.F) g (fun b => t.seam.iE (w b)) l)

def iotaSel (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal := by
  classical
  exact if hι : ∃ ι : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal,
      ∀ c, (St i hi).chOf c = β → FunMoved t.seam ((St i hi).K β).lev P v h ι (A.mov i hi c) (A.pt i hi c).deco.1
    then hι.choose else 0

def InDom (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N i)) : Prop :=
  vecAt (t := t) (ratA D.host.F (A.crd i hi) * x.1) (vUnder (t := t) P.1) w ∈
    latS (F := D.host.F) ((vUnder (t := t) P.1).adicCompletion D.host.F) (intV D.host.E (vUnder (t := t) P.1))
      (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) ((St i hi).K β).lev.Lb))

def mvG (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N i)) :
    𝓞 t.X.E ⧸ P.1.asIdeal := by
  classical
  exact if h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ (vUnder (t := t) P.1).asIdeal then
    (if hz : InDom A i hi β x P w then
      iotaSel A i hi β P (vUnder (t := t) P.1) h (((St i hi).K β).lev.fT (vUnder (t := t) P.1) h ⟨_, hz⟩) else 0)
    else 0

def mvF (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N i)) :
    𝓞 t.X.E ⧸ P.1.asIdeal :=
  let s : 𝓞 t.X.E := Classical.epsilon fun s : 𝓞 t.X.E => s ∉ P.1.asIdeal ∧ InDom A i hi β x P (s • w)
  Ring.inverse (Ideal.Quotient.mk P.1.asIdeal s) * mvG A i hi β x P (s • w)

def mvDeco (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Deco t.X.E (D.R.N i) (t.Pr.vT (t.word u)) t.Pr.vGs where
  N := mvN A a i hi β x
  f P w := mvF A i hi β x P w
  be _ _ := 0

def gAt (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (P : SB t μ) : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i) :=
  Classical.epsilon fun g : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i) =>
    NearAt (seamP t.seam P.1) ((t.cst μ).D P) (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (seamGL t.seam g)

def wOf (i : ℕ) (hi : i + 1 ≤ D.R.m) (z : HomE D.host.E (D.R.N i) (D.R.N (i + 1))) : HomE t.X.E (D.R.N i) (D.R.N (i + 1)) :=
  seamHom t.seam (inFr
    (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
    (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z)

def XiMid (i : ℕ) (hi : i + 1 < D.R.m) : StepDatum St i hi.le := fun β β' x x' z =>
  t.seam.σ₀ (phiT t.X.K (mvDeco A a i (Nat.le_of_succ_le hi.le) β x) (mvDeco A a (i + 1) hi.le β' x') (wOf A i hi.le z) *
    ∏ P : SB t μ, XiAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((t.idx μ).h i (A.ib i (Nat.lt_of_succ_lt hi) β) P)
      ((t.idx μ).h (i + 1) (A.ib (i + 1) hi β') P)
      (inFr (gAt A i (Nat.le_of_succ_le hi.le) β x P) (gAt A (i + 1) hi.le β' x' P) (wOf A i hi.le z)))

end MidDatum

end GlobalTheory.TwU

end
