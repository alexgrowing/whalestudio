import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalRingCardinality.DataKerP

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem

theorem Pj_rank {p : ℕ} {G : GAtP p} (Fl : Fills G) (j : ℕ) : (Fl.Pj j).m + 1 = NN G.P.m Fl.t j := by
  cases j with
  | zero => simp [Fills.Pj, NN]
  | succ j => simp only [Fills.Pj, Places.withWt, NN]; omega

theorem GIdx.ne_two {R : Ranks} {H : Host R} {T p : ℕ} (h : GIdx H T p) : p ≠ 2 := by
  have := h.2.1; omega

theorem GIdx.ne_d {R : Ranks} {H : Host R} {T p : ℕ} (h : GIdx H T p) : p ≠ H.d := by
  intro hd
  have hc : H.cls p = .inertClass := h.2.2.1
  unfold Host.cls primeClass at hc
  split_ifs at hc

def Pend.xForm {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1))
    (φ : Y.Frm j La La') (e : X.EA j ⊕ X.EA j) (z : X.ZA j) : Y.Kc :=
  ∑ z' : X.ZA j, MvPowerSeries.coeff (Finsupp.single z' 1) (X.coordZA Y.Kc j e) * Y.bc j La La' φ z' z

structure KerTies (D : D7) (Gt : GatTies D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    [Fact (D.what₂.places.resChar w).Prime] (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (e : Formalism.MainNotions.TaylorLogMetric.FamE D)
    (X : Sys (D.what₂.places.resChar w)) (Y : Pend X) where

  hG : X.G = D.gat u w h

  lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]

  iC : Y.Kc →+* ℂ_[D.what₂.places.resChar w]
  iC_int : ∀ x : Y.Kc, x ∈ Y.Oc ↔ ‖iC x‖ ≤ 1

  pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau

  iw : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v

  iw_lam : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : D.host.E),
    iC (algebraMap X.G.Kf Y.Kc (X.G.P.ι v ((X.G.P.σ v ^ s.val) (iw v x)))) =
      Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) (if IsOddPos s then D.host.conj x else x))

  glob : ∀ j, X.Lt j → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E)

  glob_adm : ∀ j (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    Formalism.MainNotions.TaylorLogMetric.admitted D _ _ (glob j La) (glob (j + 1) La')

  glob_loc : ∀ j (La : X.Lt j), (X.Pj j).IsLatTup La.2 → ∀ v : X.Pl,
    X.latAt v j La.2 = Submodule.span (X.G.P.W v) {y | ∃ x ∈ glob j La, y = fun i => iw v (x i)}

  F : ∀ j, X.Lt j → X.Lt (j + 1) →
    MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w]

  F_comb : ∀ j (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    Formalism.MainNotions.TaylorLogMetric.IsComb D T e lam (glob j La) (glob (j + 1) La') (F j La La')

  ThF_eq : ∀ j (La : X.Lt j) (La' : X.Lt (j + 1)) (n : X.ZA j →₀ ℕ),
    iC (MvPowerSeries.coeff n (Y.ThF j La La')) =
      MvPowerSeries.coeff (n.mapDomain fun z : X.ZA j =>
        (pos ⟨z.1, z.2.1⟩, Fin.cast (Pj_rank X.Fl (j + 1)).symm z.2.2.2, Fin.cast (Pj_rank X.Fl j).symm z.2.2.1))
        (F j La La')

  iLL : D.what₂.LL →+* X.G.Kf
  iLL_w : ∀ x : D.what₂.LL, x ∈ intW D.what₂.places w ↔ iLL x ∈ Set.range (algebraMap X.G.O X.G.Kf)
  iLL_lam : ∀ (x : D.what₂.LL) (hx : D.what₂.embLL x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar),
    iC (algebraMap X.G.Kf Y.Kc (iLL x)) = lam ⟨D.what₂.embLL x, hx⟩

  cmp : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[iLL] X.Fm j
  cmp_inj : ∀ j, j ≤ D.R.m → Function.Injective (cmp j)
  cmp_int : ∀ j, j ≤ D.R.m → Submodule.span X.G.O
    (cmp j '' (((Tw.fm u (D.what₂.muAt w)).lat j).L : Set ((Tw.fm u (D.what₂.muAt w)).lat j).V)) = X.Int j
  cmp_K : ∀ j, j < D.R.m → ∀ (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) (y : ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V),
    (Tw.fm u (D.what₂.muAt w)).emb (j + 1) y = (D.chTw u (D.what₂.muAt w)).K j ((Tw.fm u (D.what₂.muAt w)).emb j x) →
    cmp (j + 1) y = X.Kz j (cmp j x)

  fl_t : X.t = D.R.t
  fl_m : X.mm = D.R.m

  cls : ∀ j, X.Lt j → (D.chTw u (D.what₂.muAt w)).cls j
  cls_iff : ∀ j, j ≤ D.R.m → ∀ (La La' : X.Lt j), (X.Pj j).IsLatTup La.2 → (X.Pj j).IsLatTup La'.2 →
    (cls j La = cls j La' ↔ La.1 = La'.1 ∧ ∃ γ : (X.Lv.lev j La.1).Γ, La'.2 = (X.Lv.lev j La.1).smul γ La.2)
  cls_surj : ∀ j, j ≤ D.R.m → ∀ x : (D.chTw u (D.what₂.muAt w)).cls j, ∃ La : X.Lt j, (X.Pj j).IsLatTup La.2 ∧ cls j La = x

  stab_eq : ∀ j, j ≤ D.R.m → ∀ La : X.Lt j, (X.Pj j).IsLatTup La.2 →
    X.stab j La = Nat.card ((D.chTw u (D.what₂.muAt w)).stab j (cls j La))

  val : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V → X.Lt j →
    MvPolynomial (Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v) × (Fin ((X.Pj j).m + 1) × Fin ((X.Pj j).m + 1))) D.what₂.LL

  val_cmp : ∀ j, j ≤ D.R.m → ∀ (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) (La : X.Lt j), (X.Pj j).IsLatTup La.2 →
    cmp j x La.1 La.2 = MvPolynomial.map iLL (val j x La)

  evC : ∀ j, MvPolynomial (Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v) × (Fin ((X.Pj j).m + 1) × Fin ((X.Pj j).m + 1))) ℂ
    →ₗ[ℂ] ((D.chTw u (D.what₂.muAt w)).Y j → ℂ)

  val_emb : ∀ j, j ≤ D.R.m → ∀ (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V), ∀ La ∈ Y.Rep j,
    (Tw.fm u (D.what₂.muAt w)).emb j x (cls j La) = evC j (MvPolynomial.map D.what₂.embLL (val j x La))

def KerTies.kap {D : D7} {Gt : GatTies D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime] {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {T : Formalism.MainNotions.TaylorLogMetric.Tor D} {e : Formalism.MainNotions.TaylorLogMetric.FamE D} {X : Sys (D.what₂.places.resChar w)} {Y : Pend X}
    (K : KerTies D Gt Tw u w h T e X Y) (j : ℕ) (z : X.ZA j) :
    D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1) :=
  (K.pos ⟨z.1, z.2.1⟩, Fin.cast (Pj_rank X.Fl (j + 1)).symm z.2.2.2, Fin.cast (Pj_rank X.Fl j).symm z.2.2.1)

structure KerTies.Frames {D : D7} {Gt : GatTies D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime] {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {T : Formalism.MainNotions.TaylorLogMetric.Tor D} {e : Formalism.MainNotions.TaylorLogMetric.FamE D} {X : Sys (D.what₂.places.resChar w)} {Y : Pend X}
    (K : KerTies D Gt Tw u w h T e X Y) where
  cc : Ideal (𝓞 D.host.K)
  δ : ℂ
  hT : T = Formalism.MainNotions.TaylorLogMetric.tor0 D cc δ
  g : Formalism.MainNotions.GL3Theta.G1 (D.what₂.places.resChar w)
  g_at : Formalism.MainNotions.GL3Theta.At D cc δ g
  g_lam : g.lam = K.lam

  th : PowerSeries (WW (D.what₂.places.resChar w))
  th_zero : PowerSeries.constantCoeff th = 0
  th_unit : IsUnit (PowerSeries.coeff 1 th)
  ep : (WW (D.what₂.places.resChar w))ˣ
  th_log : PowerSeries.subst
      (PowerSeries.map (K.iC.comp ((algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc).comp
        (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w))))) th)
      (PowerSeries.map (K.iC.comp (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc)) (logF (D.what₂.places.resChar w))) =
    PowerSeries.C (K.iC (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc
      (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w)) (ep : WW (D.what₂.places.resChar w))))) * g.l

  be_tie : MvPowerSeries.subst
      ![MvPowerSeries.C (K.iC (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc
          (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w)) (ep : WW (D.what₂.places.resChar w))))) *
          g.lg (MvPowerSeries.X (0 : Fin 2)),
        MvPowerSeries.C (K.iC (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc
          (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w)) (ep : WW (D.what₂.places.resChar w))))) *
          g.lg (MvPowerSeries.X (1 : Fin 2))]
      (MvPowerSeries.map (K.iC.comp (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc)) Y.be) =
    g.be (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))

  okp : ∀ α : WW (D.what₂.places.resChar w), (sigW (D.what₂.places.resChar w))^[2] α = α →
    (K.iC (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc
        (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w)) α)),
      K.iC (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc
        (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w)) (sigW (D.what₂.places.resChar w) α)))) ∈
      Formalism.MainNotions.GL3Theta.OKp D K.lam

  yb : ∀ j (La : X.Lt j) (La' : X.Lt (j + 1)), Y.Frm j La La' → X.EA j ⊕ X.EA j →
    Formalism.MainNotions.GL3Theta.Idx D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) →
      ℂ_[D.what₂.places.resChar w] × ℂ_[D.what₂.places.resChar w]
  yb_basis : ∀ j La La' (φ : Y.Frm j La La'), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    Formalism.MainNotions.GL3Theta.BasisP D K.lam (Formalism.MainNotions.GL3Theta.YYp D K.lam (K.glob j La) (K.glob (j + 1) La')) (yb j La La' φ)
  yb_dual : ∀ j La La' (φ : Y.Frm j La La'), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    Formalism.MainNotions.GL3Theta.DualIso (fun e => yb j La La' φ (Sum.inl e)) (fun e => yb j La La' φ (Sum.inr e))

  frameCompatibleExchange : ∀ j La La' (φ : Y.Frm j La La') (e e' : X.EA j ⊕ X.EA j),
    ∑ z : X.ZA j, K.iC (Y.xForm j La La' φ e z) *
      ((((g.C.u⁻¹ : ℂ_[D.what₂.places.resChar w]ˣ) : ℂ_[D.what₂.places.resChar w]) *
        (K.iC (algebraMap (K0 (D.what₂.places.resChar w)) Y.Kc
          (algebraMap (WW (D.what₂.places.resChar w)) (K0 (D.what₂.places.resChar w))
            (ep : WW (D.what₂.places.resChar w)))))⁻¹) * (yb j La La' φ e' (K.kap j z)).1) =
      if e = e' then 1 else 0

structure KerTies.Lift {D : D7} {Gt : GatTies D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime] {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {T : Formalism.MainNotions.TaylorLogMetric.Tor D} {e : Formalism.MainNotions.TaylorLogMetric.FamE D} {X : Sys (D.what₂.places.resChar w)} {Y : Pend X}
    (K : KerTies D Gt Tw u w h T e X Y) where
  O : Formalism.MainNotions.GL3Theta.LiftObj D (D.chTw u (D.what₂.muAt w))
  rank_eq : ∀ j, (X.Pj j).m + 1 = D.R.N j
  p_notin : D.what₂.places.resChar w ∉ O.S
  lat_glob : ∀ j, j ≤ D.R.m → ∀ La ∈ Y.Rep j, ∀ x : Fin (D.R.N j) → D.host.E,
    x ∈ (O.lat j (K.cls j La)).1 ↔ (fun i => x (Fin.cast (rank_eq j) i)) ∈ K.glob j La
  F_Th : ∀ j, j < D.R.m → ∀ La ∈ Y.Rep j, ∀ La' ∈ Y.Rep (j + 1),
    ∀ n : (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →₀ ℕ,
    MvPowerSeries.coeff n (K.F j La La') =
      MvPowerSeries.coeff (n.mapDomain fun k => (k.1, Fin.cast (rank_eq (j + 1)) k.2.1, Fin.cast (rank_eq j) k.2.2))
        (Formalism.MainNotions.TaylorLogMetric.pSer D K.lam (O.Th j (K.cls j La) (K.cls (j + 1) La')))
  toFr : ∀ j, MvPolynomial (Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v) × (Fin ((X.Pj j).m + 1) × Fin ((X.Pj j).m + 1))) ℂ
    →ₗ[ℂ] MvPolynomial (Formalism.MainNotions.GL3Theta.FrV D (D.R.N j)) ℂ

  dt : ℕ → D.what₂.Tau → ℕ
  evC_frm : ∀ j, j ≤ D.R.m → ∀ P (y : (D.chTw u (D.what₂.muAt w)).Y j),
    K.evC j P y * ∏ τ, (Matrix.det (O.frm j y τ)) ^ (dt j τ) = Formalism.MainNotions.GL3Theta.evFr D (toFr j P) (O.frm j y)

structure KerTies.Agrees {D : D7} {Gt : GatTies D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime] {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {T : Formalism.MainNotions.TaylorLogMetric.Tor D} {e : Formalism.MainNotions.TaylorLogMetric.FamE D} {X : Sys (D.what₂.places.resChar w)} {Y : Pend X}
    (K : KerTies D Gt Tw u w h T e X Y) {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} {Ch : Chain Lv}
    {c : LatCmp D} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) : Prop where
  fl : HEq X.Fl Fl
  lv : HEq X.Lv Lv
  ch : HEq X.Ch Ch
  lam : K.lam = Kp.lam
  iLL : HEq K.iLL (c.embW u w h)
  glob : HEq K.glob (fun j (La : Lv.comp j × (Fl.Pj j).Tup) => Kp.glob j La.1 La.2)
  F : HEq K.F Kp.Th
  cmp : HEq K.cmp Kp.cmp
  cls : HEq K.cls (fun j (La : Lv.comp j × (Fl.Pj j).Tup) => Kp.cls j La.1 La.2)

end Formalism.MainNotions.FormalGroupSystem
