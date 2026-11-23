import Formalism.SharpRestriction.SmoothDesignExistence.SumOverPrimesHypotheses

noncomputable section

namespace Formalism.MainNotions.G.TwTie

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions

structure KerAtMu (D : D7) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    (Ch : Chain Lv) where

  fl_t : Fl.t = D.R.t
  fl_m : Fl.mm = D.R.m

  cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j

  cls_iff : ∀ j, j ≤ D.R.m → ∀ (a a' : Lv.comp j) (L L' : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    (Fl.Pj j).IsLatTup L' →
    (cls j a L = cls j a' L' ↔ a = a' ∧ ∃ γ : (Lv.lev j a).Γ, L' = (Lv.lev j a).smul γ L)
  cls_surj : ∀ j, j ≤ D.R.m → ∀ x : (D.chTw u μ).cls j, ∃ a L, (Fl.Pj j).IsLatTup L ∧ cls j a L = x

  stab_zero : ∀ (a : Lv.comp 0) (L : (Fl.Pj 0).Tup), (Fl.Pj 0).IsLatTup L →
    Nat.card {γ : (Lv.lev 0 a).Γ // (Lv.lev 0 a).smul γ L = L} = 1

  stab_dvd : ∀ j, j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    0 < Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L} ∧
      Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L} ∣ (D.mem u).C.DGam

  cmp : ∀ j, ((Tw.fm u μ).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j
  cmp_inj : ∀ j, j ≤ D.R.m → Function.Injective (cmp j)

  cmp_zero : ∀ x : ((D.fm u).lat 0).V, cmp 0 (Tw.e0 u μ x) = c.cmp u w h x

  cmp_int : ∀ j, j ≤ D.R.m → Submodule.span (D.gat u w h).O
    (cmp j '' (((Tw.fm u μ).lat j).L : Set ((Tw.fm u μ).lat j).V)) = Lv.Int j

  cmp_K : ∀ j, j < D.R.m → ∀ (x : ((Tw.fm u μ).lat j).V) (y : ((Tw.fm u μ).lat (j + 1)).V),
    (Tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((Tw.fm u μ).emb j x) →
    cmp (j + 1) y = Ch.Kz j (cmp j x)

  rat : ∀ j, j < D.R.m → (Tw.fm u μ).KRat j

  val : ∀ (y : ((Tw.fm u μ).lat D.R.m).V) (s : ℝ),
    vGeLat (D.gat u w h) (Lv.Int D.R.m) (cmp D.R.m y) s → WeilJacquetShalikaLaw.VGe D w ((Tw.fm u μ).lat D.R.m).L y s

structure TwistedUnitaryExtraData {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts}
    {Dx : DivX D} {cX : ExtraC} (E : Extra D L hT Gi Gl K Dx cX) where
  LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    Σ Lv : Levels (Gl.Fl u w hg), Chain Lv
  ker : ∀ (μ : D.what₂.Tup), DV.Used D μ → ∀ u (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.places.resChar w ∉ Dx.Qp μ → KerAtMu D E.cmp E.tw u μ w h (((Pk.reW Gl LC).Yt μ).Ch u w h)

  twisted_e0_at_mu0_eq_eMu0 : ∀ u, E.tw.e0 u D.what₂.mu0 = E.tw.eMu0 u 0 (Nat.zero_le _)

def TwistedUnitaryFamilyCondition {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), Nonempty (TwistedUnitaryExtraData (Fm.ex x hx i))

def TwistedUnitaryFamilyClosed (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), ∃ T : TwistedUnitaryExtraData (Fm.ex x hx i),
    Pk.SysTw (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK (Fm.X x i) (Pk.reW (Fm.Gy x i) T.LC) (Fm.ex x hx i).lev
      (Fm.ex x hx i).errX Fm.cX.err 1

def LatticeMultiplicityComparison : Prop :=
  ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Dx : DivX D}
    {cX : ExtraC} (E : Extra D L hT Gi Gl K Dx cX) (T : TwistedUnitaryExtraData E), WeilJacquetShalikaLaw.CmpV E.cmp Dx E.tw (Pk.reW Gl T.LC)

theorem twU_of_tied (𝒞 : FamClass) (hV : LatticeMultiplicityComparison) (h : TwistedUnitaryFamilyClosed 𝒞) :
    Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ∃ LC, WeilJacquetShalikaLaw.CmpV (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw (Pk.reW (Fm.Gy x i) LC) ∧ Pk.SysTw (Fm.D x i) (Fm.L x i)
        (Fm.Gx x i) Fm.GK (Fm.X x i) (Pk.reW (Fm.Gy x i) LC) (Fm.ex x hx i).lev (Fm.ex x hx i).errX Fm.cX.err 1 := by
  obtain ⟨a, ha, hP⟩ := h
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := hP e he hle
  refine ⟨K, fun Fm CH hcl hL => ?_⟩
  obtain ⟨x0, h0⟩ := hK Fm CH hcl hL
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  obtain ⟨T, hT⟩ := h0 x hx hx1 i
  exact ⟨T.LC, hV _ T, hT⟩

theorem mm_of_latTied {D : D7} {L : SizeData₂ D} (hT : GatTies D) (X : G.Inst D L) (Y : G.LatInst D) (h : G.LatTied hT X Y)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (Y.Fl u w hg).mm = D.R.m := (h u w hg).1

end Formalism.MainNotions.G.TwTie
