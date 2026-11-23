import Mathlib
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.LocalRingCardinality.Lemmas

noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

namespace GlobalTheory.Proof.LatticeValuationBound

section Chain

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}

def StepCmp (M : MemberForms LL embLL Pl Tau hc C A P) {p : ℕ} {G : GAtP p} {Fl : Fills G} {Lv : Levels Fl}
    (Ch : Chain Lv) (σ : LL →+* G.Kf) (start : (M.lat 0).V → Lv.Fm 0) : Prop :=
  ∃ cmp : ∀ j, (M.lat j).V →ₛₗ[σ] Lv.Fm j,
    (∀ x, cmp 0 x = start x) ∧
    (∀ j, j < R.m → ∀ (x : (M.lat j).V) (y : (M.lat (j + 1)).V),
      M.emb (j + 1) y = C.K j (M.emb j x) → cmp (j + 1) y = Ch.Kz j (cmp j x)) ∧
    (LinearIndependent G.Kf fun a => cmp R.m ((M.lat R.m).b a)) ∧
    Lv.Int R.m ≤ Submodule.span G.O (cmp R.m '' ((M.lat R.m).L : Set (M.lat R.m).V))

theorem exists_chain (M : MemberForms LL embLL Pl Tau hc C A P) {p : ℕ} {G : GAtP p} {Fl : Fills G} {Lv : Levels Fl}
    (Ch : Chain Lv) (σ : LL →+* G.Kf) (cmp : ∀ j, (M.lat j).V →ₛₗ[σ] Lv.Fm j)
    (hK : ∀ j, j < R.m → ∀ (x : (M.lat j).V) (y : (M.lat (j + 1)).V),
      M.emb (j + 1) y = C.K j (M.emb j x) → cmp (j + 1) y = Ch.Kz j (cmp j x))
    (hrat : ∀ j, j < R.m → M.KRat j) (x : (M.lat 0).V) (j : ℕ) (hj : j ≤ R.m) :
    ∃ y : (M.lat j).V, M.emb j y = Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap j (M.emb 0 x) ∧ cmp j y = Ch.chainK j (cmp 0 x) := by
  induction j with
  | zero => exact ⟨x, rfl, rfl⟩
  | succ j ih =>
    obtain ⟨y, hy, hy'⟩ := ih (by omega)
    obtain ⟨z, hz⟩ := hrat j (by omega) y
    refine ⟨z, ?_, ?_⟩
    · rw [hz, hy]; rfl
    · rw [hK j (by omega) y z hz, hy']; rfl

end Chain

variable {D : D7}

def CmpRef (c : LatCmp D) (Dx : DivX D) {Y : LatInst D} (W : TwLoc D Y) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.places.resChar w ∉ Dx.Qp D.what₂.mu0 →
    StepCmp (D.fm u) (W.LC D.what₂.mu0 u w hg).2 (c.embW u w hg) (fun x => c.cmp u w hg x)

def CmpTwAt (c : LatCmp D) (T : TwForms D) {Y : LatInst D} (W : TwLoc D Y) (μ : D.what₂.Tup) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Prop :=
  StepCmp (T.fm u μ) (W.LC μ u w hg).2 (c.embW u w hg) (fun x => c.cmp u w hg ((T.e0 u μ).symm x))

def CmpTw (c : LatCmp D) (Dx : DivX D) (T : TwForms D) {Y : LatInst D} (W : TwLoc D Y) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) μ,
    DV.Used D μ → μ ≠ D.what₂.mu0 → D.what₂.places.resChar w ∉ Dx.Qp μ → CmpTwAt c T W μ u w hg

def RatRef (D : D7) : Prop := ∀ u, ∀ i < D.R.m, (D.fm u).KRat i

def RatTw (T : TwForms D) : Prop :=
  ∀ u μ, DV.Used D μ → μ ≠ D.what₂.mu0 → ∀ i < D.R.m, (T.fm u μ).KRat i

def StepZeroRef (D : D7) : Prop := ∀ u φ, HEq (D.e0Tw u D.what₂.mu0 φ) φ

theorem col_heq {R : Ranks} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C C' : ColumnChain R Tau hc}
    (h : C = C') {φ : C.cls 0 → C.Y 0 → ℂ} {φ' : C'.cls 0 → C'.Y 0 → ℂ} (hφ : HEq φ φ') :
    HEq (C.col φ) (C'.col φ') := by
  subst h
  rw [eq_of_heq hφ]

theorem VGe_symm {w : D.what₂.places.Pl} (A B : HLat D.what₂.LL) (e : A.V ≃ₗ[D.what₂.LL] B.V)
    (he : ∀ x, x ∈ A.L ↔ e x ∈ B.L) {y : B.V} {s : ℝ} (h : VGe D w B.L y s) : VGe D w A.L (e.symm y) s := by
  obtain ⟨a, z, hz, rfl, ha⟩ := h
  refine ⟨a, e.symm z, ?_, map_smul _ _ _, ha⟩
  obtain ⟨t, ht, hz⟩ := (D.mem_locW_iff w _ _).1 hz
  refine (D.mem_locW_iff w _ _).2 ⟨t, ht, (he _).2 ?_⟩
  rw [← algebraMap_smul D.what₂.LL t, map_smul, LinearEquiv.apply_symm_apply, algebraMap_smul]
  exact hz

theorem colGe0_of_colGeTw (T : TwForms D) (h0 : StepZeroRef D) {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {x : ((D.fm u).lat 0).V} {s : ℝ} (h : ColGeTw T u D.what₂.mu0 w x s) : ColGe0 D u w x s := by
  obtain ⟨y, hy, hv⟩ := h
  refine ⟨(T.eMu0 u D.R.m le_rfl).symm y, ?_, VGe_symm _ _ _ (T.eMu0_lat u D.R.m le_rfl) hv⟩
  have h1 := T.eMu0_emb u D.R.m le_rfl ((T.eMu0 u D.R.m le_rfl).symm y)
  rw [LinearEquiv.apply_symm_apply, hy] at h1
  exact eq_of_heq (h1.symm.trans (col_heq (D.memberColumns_twistedChain_base u) (h0 u _)))

def CmpTwAll (c : LatCmp D) (Dx : DivX D) (T : TwForms D) {Y : LatInst D} (W : TwLoc D Y) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) μ,
    DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → CmpTwAt c T W μ u w hg

def RatTwAll (T : TwForms D) : Prop := ∀ u μ, DV.Used D μ → ∀ i < D.R.m, (T.fm u μ).KRat i

end GlobalTheory.Proof.LatticeValuationBound

end
