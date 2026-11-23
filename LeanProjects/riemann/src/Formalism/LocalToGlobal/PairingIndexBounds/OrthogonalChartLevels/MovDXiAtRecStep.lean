import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepRec

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.MainNotions.G.CmpJ
open Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.Col
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def homIE {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (x : HomE D.host.E a b) : HomE X.E a b :=
  Matrix.toLin' ((LinearMap.toMatrix' x).map s.iE.symm)

def homRe {E : Type} [Field E] {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (x : HomE E a b) : HomE E a' b' :=
  (LinearEquiv.funCongrLeft E E (finCongr hb.symm)).toLinearMap ∘ₗ x ∘ₗ
    (LinearEquiv.funCongrLeft E E (finCongr ha.symm)).symm.toLinearMap

def rdH {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {X : Fields} (s : Seam D X) (rd : KerRead (D.chTw u μ) X)
    {p : ℕ} [Fact p.Prime] {G : GAtP p} {Fl : Fills G} {Lv : Levels Fl}
    (cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j) (j : ℕ)
    (La : Lv.comp j × (Fl.Pj j).Tup) (La' : Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup)
    (x : HomE D.host.E (D.R.N j) (D.R.N (j + 1))) : ℂ :=
  rd.Xi j (cls j La.1 La.2) (cls (j + 1) La'.1 La'.2) (homIE s x)

def RdAway {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {X : Fields} (p : ℕ) (rd : KerRead (D.chTw u μ) X) : Prop :=
  ∃ S₀ : Finset ℕ, p ∉ S₀ ∧ ∀ i c c' x, IntOff S₀ (rd.Xi i c c' x)

theorem intOff_zero (S : Finset ℕ) : IntOff S 0 := by
  refine ⟨zero_mem _, fun p _ lam _ => ?_⟩
  unfold TaylorLogMetric.lamC
  split_ifs with h
  · have e : (⟨0, h⟩ : TaylorLogMetric.Qbar) = 0 := rfl
    rw [e, map_zero, norm_zero]
    exact zero_le_one
  · rw [norm_zero]
    exact zero_le_one

section AtS

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
  {X : Fields} (s : Seam D X) (rd : KerRead (D.chTw u μ) X)
  (cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j)

open Classical in

def xiAt0 : ∀ j, (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1) →
    HomE D.host.E (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1) (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1) → ℂ :=
  fun j La La' z =>
    if hr : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1 = D.R.N j ∧ ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1 = D.R.N (j + 1) then
      rdH s rd cls j La La' (homRe hr.1 hr.2 (inFr ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).trG j La).symm ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).trG (j + 1) La').symm z))
    else 0

theorem movD_xiAt0 (j : ℕ) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j) (La' : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1))
    (hr : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1 = D.R.N j ∧ ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1 = D.R.N (j + 1)) :
    movD (xiAt0 Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad s rd cls j La La') ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).trG j La) ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).trG (j + 1) La') =
      fun x => rdH s rd cls j La La' (homRe hr.1 hr.2 x) := by
  funext x
  unfold movD xiAt0
  rw [dif_pos hr]
  congr 2
  apply LinearMap.ext
  intro y
  simp [inFr]

include I L0 in

theorem rankAt : ∀ j, j ≤ D.R.m → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1 = D.R.N j
  | 0, _, _ => by exact L0.A.rk
  | i + 1, hi, La => by exact ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk

theorem movD_xiAt0_step (j : ℕ) (hj : j + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j) (La' : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1)) :
    movD (xiAt0 Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad s rd cls j La La') ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).trG j La) ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).trG (j + 1) La') =
      fun x => rdH s rd cls j La La'
        (homRe (rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 j (by omega) La) (rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 (j + 1) hj La') x) :=
  movD_xiAt0 Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad s rd cls j La La' ⟨rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 j (by omega) La, rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 (j + 1) hj La'⟩

theorem xiAway_xiAt0 (H : RdAway (D.what₂.places.resChar w) rd) :
    Formalism.L2.KerInert.RepRec.XiAway (sysAt Ch std vp unif eO eO_spec dG dG_spec om) D (xiAt0 Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad s rd cls) := by
  obtain ⟨S₀, hp, hS⟩ := H
  refine ⟨S₀, hp, fun j La La' y => ?_⟩
  unfold xiAt0
  split_ifs
  · exact hS _ _ _ _
  · exact intOff_zero S₀

theorem dataAway_xiAt0 (cl : ℕ) (hcl : Formalism.L2.KerInert.RepRec.ClAway (D.what₂.places.resChar w) cl)
    (H : RdAway (D.what₂.places.resChar w) rd) :
    Formalism.L2.KerInert.RepRec.ClAway (D.what₂.places.resChar w) cl ∧
      Formalism.L2.KerInert.RepRec.XiAway (sysAt Ch std vp unif eO eO_spec dG dG_spec om) D (xiAt0 Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad s rd cls) :=
  ⟨hcl, xiAway_xiAt0 Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad s rd cls H⟩

def sameChartAt : ∀ j, (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → Prop
  | 0, _, _ => True
  | i + 1, La, Lb =>
    if hi : i + 1 ≤ D.R.m then ((I.at' i hi).st.eC.symm La.1).1 = ((I.at' i hi).st.eC.symm Lb.1).1 else La = Lb

def XiChartAt (Ξ₀ : ∀ j, (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1) →
    HomE D.host.E (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1) (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1) → ℂ) : Prop :=
  ∀ j (La Lb : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j) (La' Lb' : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1)),
    sameChartAt Ch std vp unif eO eO_spec dG dG_spec om I j La Lb → sameChartAt Ch std vp unif eO eO_spec dG dG_spec om I (j + 1) La' Lb' → Ξ₀ j La La' = Ξ₀ j Lb Lb'

def XiChartXi0 : Prop := XiChartAt Ch std vp unif eO eO_spec dG dG_spec om I (xiAt0 Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad s rd cls)

end AtS

section Rec

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} (I : CmpJIn ex.tw u μ w h Lv)
  (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
  (t : KerEntTied ex) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)

def xiAtRec : ∀ j, (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1) →
    HomE D.host.E (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1) (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1) → ℂ :=
  xiAt0 Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t.seam (t.rd u μ) KA.cls

theorem movD_xiAtRec_step (j : ℕ) (hj : j + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j) (La' : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1)) :
    movD (xiAtRec Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t KA j La La') ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).trG j La) ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).trG (j + 1) La') =
      fun x => (t.rd u μ).Xi j (KA.cls j La.1 La.2) (KA.cls (j + 1) La'.1 La'.2)
        (homIE t.seam (homRe (rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 j (by omega) La) (rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 (j + 1) hj La') x)) :=
  movD_xiAt0_step Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t.seam (t.rd u μ) KA.cls j hj La La'

theorem dataAway_xiAtRec (cl : ℕ) (hcl : Formalism.L2.KerInert.RepRec.ClAway (D.what₂.places.resChar w) cl)
    (H : RdAway (D.what₂.places.resChar w) (t.rd u μ)) :
    Formalism.L2.KerInert.RepRec.ClAway (D.what₂.places.resChar w) cl ∧
      Formalism.L2.KerInert.RepRec.XiAway (sysAt Ch std vp unif eO eO_spec dG dG_spec om) D (xiAtRec Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t KA) :=
  dataAway_xiAt0 Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t.seam (t.rd u μ) KA.cls cl hcl H

def XiChartRec : Prop := XiChartAt Ch std vp unif eO eO_spec dG dG_spec om I (xiAtRec Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t KA)

end Rec

end Formalism.L2.PairingIndexBounds.F
