import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.OrbitOfPts

noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p} (S : StepIn M i hi G)

structure ChX : Prop where
  hypC : ∀ β, LocHypC (S.K β).lev (S.loc β)
  inj : ∀ β a, Function.Injective ((S.loc β).gamI a)
  onto : ∀ β a, GamOnto (S.K β).lev (S.loc β) a
  cinj : ∀ β, CompInj (S.K β).lev (S.loc β)

def IsCG (a : G.comp) (L : G.P.Tup) (c : C.cls i) (γ₀ : GL (Fin (D.R.N i)) D.host.E) : Prop :=
  ∃ (β : S.Ch) (a0 : S.cmpt β) (hc : S.chOf c = β) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (κ₀ : (S.K β).lev.U),
    S.eC ⟨β, a0⟩ = a ∧
    (∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) ∧
    γ₀ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) ∧
    (S.loc β).IsPt a0 g
      (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ₀ * ((S.K β).y ⟨c, hc⟩).1 * κ₀.1)

variable {S} {e : D.what₂.LL →+* G.Kf}

theorem exists_isCG_bases (H : ∀ β, S.Core e β) (a : G.comp) (L : G.P.Tup) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) :
    ∃ c γ₀, IsCG S a L c γ₀ := by
  obtain ⟨⟨β, a0⟩, rfl⟩ := S.eC.surjective a
  obtain ⟨c, γ₀, κ₀, hγ₀, hpt⟩ := ptEx_of (H β).good (S.K β).lev (S.K β).y (S.K β).y_bij.2 a0 g
  exact ⟨c.1, γ₀, β, a0, c.2, g, κ₀, rfl, hL, hγ₀, hpt⟩

theorem exists_bases (L : G.P.Tup) (hL : G.P.IsLatTup L) : ∃ g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v),
    ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
  choose g hg using fun v => (isLattice_iff _ (L v)).1 (hL v)
  exact ⟨g, fun v => by rw [hg v, colSpan_eq]⟩

theorem isLatTup_of_bases (L : G.P.Tup) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) : G.P.IsLatTup L :=
  fun v => (isLattice_iff _ (L v)).2 ⟨g v, by rw [hL v, colSpan_eq]⟩

theorem exists_isCG (H : ∀ β, S.Core e β) (a : G.comp) (L : G.P.Tup) (hL : G.P.IsLatTup L) : ∃ c γ₀, IsCG S a L c γ₀ := by
  obtain ⟨g, hg⟩ := exists_bases L hL
  exact exists_isCG_bases H a L g hg

theorem IsCG.cls_eq (H : ∀ β, S.Core e β) {a : G.comp} {L : G.P.Tup} {c c' : C.cls i} {γ₀ γ₁ : GL (Fin (D.R.N i)) D.host.E}
    (h : IsCG S a L c γ₀) (h' : IsCG S a L c' γ₁) : c = c' := by
  obtain ⟨β, a0, hc, g, κ₀, rfl, hL, hγ, hpt⟩ := h
  obtain ⟨β', a0', hc', g', κ₁, ha', hL', hγ', hpt'⟩ := h'
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.1 (S.eC.injective ha')
  obtain rfl := eq_of_heq hh
  exact congrArg Subtype.val (cls_unique (H β').good (H β').int (H β').hypP (H β').bad_p (S.K β').y (S.K β').y_bij.1 a0' L g g' hL hL'
    ⟨c, hc⟩ ⟨c', hc'⟩ γ₀ γ₁ hγ hγ' κ₀ κ₁ hpt hpt')

theorem IsCG.chart {a : G.comp} {L : G.P.Tup} {c : C.cls i} {γ₀ : GL (Fin (D.R.N i)) D.host.E} (h : IsCG S a L c γ₀) :
    S.chOf c = (S.eC.symm a).1 := by
  obtain ⟨β, a0, hc, g, κ₀, rfl, -⟩ := h
  rw [Equiv.symm_apply_apply]
  exact hc

theorem IsCG.mem {a : G.comp} {L : G.P.Tup} {c : C.cls i} {γ₀ : GL (Fin (D.R.N i)) D.host.E} (h : IsCG S a L c γ₀) :
    γ₀ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) := by
  obtain ⟨β, a0, hc, g, κ₀, -, -, hγ, -⟩ := h
  exact hγ

theorem IsCG.smul (H : ∀ β, S.Core e β) {β : S.Ch} {a0 : S.cmpt β} {L : G.P.Tup} {c : C.cls i}
    {γ₀ : GL (Fin (D.R.N i)) D.host.E} (h : IsCG S (S.eC ⟨β, a0⟩) L c γ₀) (γ : (G.lev (S.eC ⟨β, a0⟩)).Γ) :
    IsCG S (S.eC ⟨β, a0⟩) ((G.lev (S.eC ⟨β, a0⟩)).smul γ L) c ((S.loc β).gamI a0 γ * γ₀) := by
  obtain ⟨β', a0', hc, g, κ₀, ha', hL, hγ, hpt⟩ := h
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.1 (S.eC.injective ha')
  obtain rfl := eq_of_heq hh
  obtain ⟨κ₁, h1⟩ := pt_smul (H β').good (H β').actB (H β').gam a0' g _ γ₀ κ₀ hpt γ
  exact ⟨β', a0', hc, _, κ₁, rfl, fun v => smul_colSpan (G := S.charts.gat β') a0' γ L g hL v,
    Subgroup.mul_mem _ ((H β').gamU a0' γ) hγ, h1⟩

theorem IsCG.orbit (H : ∀ β, S.Core e β) (X : ChX S) {a a' : G.comp} {L L' : G.P.Tup} {c : C.cls i}
    {γ₀ γ₁ : GL (Fin (D.R.N i)) D.host.E} (h : IsCG S a L c γ₀) (h' : IsCG S a' L' c γ₁) :
    a = a' ∧ ∃ γ : (G.lev a).Γ, L' = (G.lev a).smul γ L := by
  obtain ⟨β, a0, hc, g, κ₀, rfl, hL, hγ, hpt⟩ := h
  obtain ⟨β', a0', hc', g', κ₁, rfl, hL', hγ', hpt'⟩ := h'
  obtain rfl : β = β' := hc.symm.trans hc'
  obtain ⟨rfl, γ, -, hγL⟩ := orbit_of_pts (H β).good (H β).int (X.hypC β) (H β).actB (H β).gam (X.cinj β) (X.onto β) a0 a0' L L' g g'
    hL hL' _ γ₀ γ₁ hγ hγ' κ₀ κ₁ hpt hpt'
  exact ⟨rfl, γ, hγL⟩

theorem IsCG.pt (H : ∀ β, S.Core e β) {β : S.Ch} {a0 : S.cmpt β} {L : G.P.Tup} {c : C.cls i}
    {γ₀ : GL (Fin (D.R.N i)) D.host.E} (h : IsCG S (S.eC ⟨β, a0⟩) L c γ₀) (hc : S.chOf c = β)
    (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (hx : (S.loc β).IsPt a0 g x.1) :
    ∃ κ : (S.K β).lev.U, x.1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ₀ * ((S.K β).y ⟨c, hc⟩).1 * κ.1 := by
  obtain ⟨β', a0', hc', g', κ₀, ha', hL', hγ, hpt⟩ := h
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.1 (S.eC.injective ha')
  obtain rfl := eq_of_heq hh
  obtain ⟨κ, e1, -⟩ := ptOne_of (S.K β').lev (H β').int (H β').hypP (H β').bad_p a0' L g' g
    ⟨_, Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem hγ) ((S.K β').y ⟨c, hc'⟩).2) (U_le κ₀.2)⟩ x hL' hL hpt hx
  refine ⟨κ₀ * κ, ?_⟩
  rw [e1]
  show _ * _ * _ * _ = _ * _ * (κ₀.1 * κ.1)
  group

theorem exists_of_cls (H : ∀ β, S.Core e β) (c : C.cls i) : ∃ a L γ₀, G.P.IsLatTup L ∧ IsCG S a L c γ₀ := by
  obtain ⟨a0, g, γ, κ, hγ, hpt⟩ := ptAll_of (H (S.chOf c)).good (S.K (S.chOf c)).lev (S.K (S.chOf c)).y (H (S.chOf c)).comp ⟨c, rfl⟩
  refine ⟨S.eC ⟨S.chOf c, a0⟩, fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)), γ,
    isLatTup_of_bases _ g fun _ => rfl, S.chOf c, a0, rfl, g, κ, rfl, fun _ => rfl, hγ, hpt⟩

theorem IsCG.card (H : ∀ β, S.Core e β) (X : ChX S) {a : G.comp} {L : G.P.Tup} {c : C.cls i}
    {γ₀ : GL (Fin (D.R.N i)) D.host.E} (h : IsCG S a L c γ₀) :
    Nat.card (C.stab i c) = Nat.card {γ : (G.lev a).Γ // (G.lev a).smul γ L = L} := by
  obtain ⟨β, a0, hc, g, κ₀, rfl, hL, hγ, hpt⟩ := h
  exact card_eq (H β).good (H β).int (H β).hypP (X.hypC β) (H β).bad_p (H β).actB (H β).gam (H β).gamU a0 (X.inj β a0) (X.onto β a0) L g hL
    (S.K β).y (S.K β).stabI (S.K β).stabI_inj (S.K β).stabI_range ⟨c, hc⟩ γ₀ hγ κ₀ hpt

theorem cls_nonempty (H : ∀ β, S.Core e β) (a : G.comp) : Nonempty (C.cls i) := by
  obtain ⟨c, -, -⟩ := exists_isCG_bases H a (fun v => colSpan (G.P.W v) ((1 : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
    Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) (fun _ => 1) fun _ => rfl
  exact ⟨c⟩

def cg (H : ∀ β, S.Core e β) (a : G.comp) (L : G.P.Tup) : C.cls i × GL (Fin (D.R.N i)) D.host.E :=
  @Classical.epsilon _ ((cls_nonempty H a).map fun c => (c, 1)) fun q => IsCG S a L q.1 q.2

def clsOf (H : ∀ β, S.Core e β) (a : G.comp) (L : G.P.Tup) : C.cls i := (cg H a L).1

def gam0 (H : ∀ β, S.Core e β) (a : G.comp) (L : G.P.Tup) : GL (Fin (D.R.N i)) D.host.E := (cg H a L).2

theorem cg_spec (H : ∀ β, S.Core e β) (a : G.comp) (L : G.P.Tup) (hL : G.P.IsLatTup L) :
    IsCG S a L (clsOf H a L) (gam0 H a L) := by
  obtain ⟨c, γ₀, h⟩ := exists_isCG H a L hL
  exact @Classical.epsilon_spec _ (fun q : C.cls i × GL (Fin (D.R.N i)) D.host.E => IsCG S a L q.1 q.2) ⟨(c, γ₀), h⟩

theorem clsOf_eq (H : ∀ β, S.Core e β) {a : G.comp} {L : G.P.Tup} {c : C.cls i} {γ₀ : GL (Fin (D.R.N i)) D.host.E}
    (h : IsCG S a L c γ₀) : clsOf H a L = c := by
  obtain ⟨β, a0, hc, g, κ₀, ha, hL, hγ, hpt⟩ := id h
  exact (cg_spec H a L (isLatTup_of_bases L g hL)).cls_eq H h

theorem clsOf_iff (H : ∀ β, S.Core e β) (X : ChX S) (a a' : G.comp) (L L' : G.P.Tup) (hL : G.P.IsLatTup L) (hL' : G.P.IsLatTup L') :
    clsOf H a L = clsOf H a' L' ↔ a = a' ∧ ∃ γ : (G.lev a).Γ, L' = (G.lev a).smul γ L := by
  constructor
  · intro h
    have h1 := cg_spec H a L hL
    have h2 := cg_spec H a' L' hL'
    rw [← h] at h2
    exact h1.orbit H X h2
  · rintro ⟨rfl, γ, rfl⟩
    obtain ⟨⟨β, a0⟩, rfl⟩ := S.eC.surjective a
    exact (clsOf_eq H ((cg_spec H _ L hL).smul H γ)).symm

theorem clsOf_surj (H : ∀ β, S.Core e β) (c : C.cls i) : ∃ a L, G.P.IsLatTup L ∧ clsOf H a L = c := by
  obtain ⟨a, L, γ₀, hL, h⟩ := exists_of_cls H c
  exact ⟨a, L, hL, clsOf_eq H h⟩

theorem clsOf_chart (H : ∀ β, S.Core e β) (a : G.comp) (L : G.P.Tup) (hL : G.P.IsLatTup L) :
    S.chOf (clsOf H a L) = (S.eC.symm a).1 := (cg_spec H a L hL).chart

theorem clsOf_card (H : ∀ β, S.Core e β) (X : ChX S) (a : G.comp) (L : G.P.Tup) (hL : G.P.IsLatTup L) :
    Nat.card (C.stab i (clsOf H a L)) = Nat.card {γ : (G.lev a).Γ // (G.lev a).smul γ L = L} := (cg_spec H a L hL).card H X

end Formalism.MainNotions.G.KAat

end
