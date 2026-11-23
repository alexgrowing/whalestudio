import Formalism.LocalRingCardinality.DataGatTies
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.SharpRestriction.GrowthBounds.DataGChain

open Formalism.MainNotions.G NumberField

noncomputable section

namespace Formalism.BasicNotions

structure TwForms (D : D7) where
  A : ∀ u μ, ColumnsAtT D.R (D.chTw u μ)
  A_T : ∀ u μ, (A u μ).T = (D.mem u).A.T
  fm : ∀ u μ, MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) (D.chTw u μ) (A u μ) (D.PTw u μ)

  e0 : ∀ u μ, ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] ((fm u μ).lat 0).V
  twist_preserves_base_lattice : ∀ u μ (x : ((D.fm u).lat 0).V), x ∈ ((D.fm u).lat 0).L ↔ e0 u μ x ∈ ((fm u μ).lat 0).L
  embed_mul_block_embedding : ∀ u μ (x : ((D.fm u).lat 0).V), (fm u μ).emb 0 (e0 u μ x) = D.e0Tw u μ ((D.fm u).emb 0 x)

  eMu0 : ∀ u j, j ≤ D.R.m → (((D.fm u).lat j).V ≃ₗ[D.what₂.LL] ((fm u D.what₂.mu0).lat j).V)
  eMu0_lat : ∀ u j (hj : j ≤ D.R.m) (x : ((D.fm u).lat j).V),
    x ∈ ((D.fm u).lat j).L ↔ eMu0 u j hj x ∈ ((fm u D.what₂.mu0).lat j).L
  eMu0_emb : ∀ u j (hj : j ≤ D.R.m) (x : ((D.fm u).lat j).V),
    HEq ((fm u D.what₂.mu0).emb j (eMu0 u j hj x)) ((D.fm u).emb j x)

structure LocalToGlobal₂ (D : D7) (Gt : GatTies D) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    [Fact (D.what₂.places.resChar w).Prime]
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    (Ch : Chain Lv) where

  fl_t : Fl.t = D.R.t
  fl_m : Fl.mm = D.R.m

  lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]

  iK : (D.gat u w h).Kf →+* ℂ_[D.what₂.places.resChar w]
  iLL_lam : ∀ (x : D.what₂.LL) (hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ),
    iK (c.embW u w h x) = lam ⟨D.what₂.embLL x, hx⟩

  iw : ∀ j (v : Fin (Fl.Pj j).nV), D.host.E →+* (Fl.Pj j).Qq v

  glob : ∀ j, Lv.comp j → (Fl.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((Fl.Pj j).m + 1) → D.host.E)

  glob_loc : ∀ j, j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L → ∀ v,
    L v = Submodule.span ((Fl.Pj j).W v) {y | ∃ x ∈ glob j a L, y = fun i => iw j v (x i)}

  cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u (D.what₂.muAt w)).cls j

  cls_iff : ∀ j, j ≤ D.R.m → ∀ (a a' : Lv.comp j) (L L' : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    (Fl.Pj j).IsLatTup L' →
    (cls j a L = cls j a' L' ↔ a = a' ∧ ∃ γ : (Lv.lev j a).Γ, L' = (Lv.lev j a).smul γ L)
  cls_surj : ∀ j, j ≤ D.R.m → ∀ x : (D.chTw u (D.what₂.muAt w)).cls j, ∃ a L, (Fl.Pj j).IsLatTup L ∧ cls j a L = x

  Th : ∀ j, Lv.comp j × (Fl.Pj j).Tup → Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup →
    MvPowerSeries (D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w]

  cmp : ∀ j, ((Tw.fm u (D.what₂.muAt w)).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j
  cmp_inj : ∀ j, j ≤ D.R.m → Function.Injective (cmp j)

  cmp_zero : ∀ x : ((D.fm u).lat 0).V, cmp 0 (Tw.e0 u (D.what₂.muAt w) x) = c.cmp u w h x

  cmp_int : Submodule.span (D.gat u w h).O
    (cmp 0 '' (((Tw.fm u (D.what₂.muAt w)).lat 0).L : Set ((Tw.fm u (D.what₂.muAt w)).lat 0).V)) = Lv.Int 0

  cmp_K : ∀ j, j < D.R.m → ∀ (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) (y : ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V),
    (Tw.fm u (D.what₂.muAt w)).emb (j + 1) y = (D.chTw u (D.what₂.muAt w)).K j ((Tw.fm u (D.what₂.muAt w)).emb j x) →
    cmp (j + 1) y = Ch.Kz j (cmp j x)

def LocalToGlobal₂.CmpIntAll {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word}
    {w : D.what₂.places.Pl} [Fact (D.what₂.places.resChar w).Prime]
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    {Ch : Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) : Prop :=
  ∀ j, j ≤ D.R.m → Submodule.span (D.gat u w h).O
    (Kp.cmp j '' (((Tw.fm u (D.what₂.muAt w)).lat j).L : Set ((Tw.fm u (D.what₂.muAt w)).lat j).V)) = Lv.Int j

theorem LocalToGlobal₂.cmp_KL {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word}
    {w : D.what₂.places.Pl} [Fact (D.what₂.places.resChar w).Prime]
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    {Ch : Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) (j : ℕ) (hj : j < D.R.m)
    (hK : (Tw.fm u (D.what₂.muAt w)).KRat j) (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) :
    Kp.cmp (j + 1) ((Tw.fm u (D.what₂.muAt w)).KL j hK x) = Ch.Kz j (Kp.cmp j x) :=
  Kp.cmp_K j hj x _ ((Tw.fm u (D.what₂.muAt w)).KL_spec j hK x)

end Formalism.BasicNotions
