import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.OrbitOfPts
import Formalism.LocalToGlobal.GroupLattices.ClassLocalOfEq

noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

section One

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {p : ℕ} {G : GAtP p} {cl : Type}

structure OneHyp (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)) : Prop where
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls S))
  good : LocGood σ J A
  int : LocInt A
  hypP : LocHyp S A
  hypC : LocHypC S A
  bad_p : ∀ w ∈ bad, ((p : ℕ) : 𝓞 F) ∉ w.asIdeal
  actB : A.ActB
  comp : ∀ x : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ (i : G.comp) (γ : GL (Fin n) E)
      (a : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), γ ∈ UJ (σ : E →+* E) J ∧ a ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * A.yG i * a ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) a ∈ S.Uloc w
  gam : ∀ i (γ : (G.lev i).Γ), (A.yG i)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * A.yG i ∈
        UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w)
        ((A.yG i)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * A.yG i) ∈ S.Uloc w
  gamU : ∀ i (γ : (G.lev i).Γ), A.gamI i γ ∈ UJ (σ : E →+* E) J
  inj : ∀ i, Function.Injective (A.gamI i)
  onto : ∀ i, GamOnto S A i
  cinj : CompInj S A

def IsCG1 (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (i : G.comp) (L : G.P.Tup) (c : cl) (γ₀ : GL (Fin n) E) : Prop :=
  ∃ (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (κ₀ : S.U),
    (∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) ∧
    γ₀ ∈ UJ (σ : E →+* E) J ∧ A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * (y c).1 * κ₀.1)

variable {S : StepLevel F E σ J T f bad} {A : LocAt F E n G} {y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)}

theorem exists_bases1 (L : G.P.Tup) (hL : G.P.IsLatTup L) : ∃ g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v),
    ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
  choose g hg using fun v => (isLattice_iff _ (L v)).1 (hL v)
  exact ⟨g, fun v => by rw [hg v, colSpan_eq]⟩

theorem isLatTup_of_bases1 (L : G.P.Tup) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) : G.P.IsLatTup L :=
  fun v => (isLattice_iff _ (L v)).2 ⟨g v, by rw [hL v, colSpan_eq]⟩

theorem exists_isCG1_bases (H : OneHyp S A y) (i : G.comp) (L : G.P.Tup) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) :
    ∃ c γ₀, IsCG1 S A y i L c γ₀ := by
  obtain ⟨c, γ₀, κ₀, hγ₀, hpt⟩ := ptEx_of H.good S y H.y_bij.2 i g
  exact ⟨c, γ₀, g, κ₀, hL, hγ₀, hpt⟩

theorem exists_isCG1 (H : OneHyp S A y) (i : G.comp) (L : G.P.Tup) (hL : G.P.IsLatTup L) : ∃ c γ₀, IsCG1 S A y i L c γ₀ := by
  obtain ⟨g, hg⟩ := exists_bases1 L hL
  exact exists_isCG1_bases H i L g hg

theorem IsCG1.cls_eq (H : OneHyp S A y) {i : G.comp} {L : G.P.Tup} {c c' : cl} {γ₀ γ₁ : GL (Fin n) E}
    (h : IsCG1 S A y i L c γ₀) (h' : IsCG1 S A y i L c' γ₁) : c = c' := by
  obtain ⟨g, κ₀, hL, hγ, hpt⟩ := h
  obtain ⟨g', κ₁, hL', hγ', hpt'⟩ := h'
  exact cls_unique H.good H.int H.hypP H.bad_p y H.y_bij.1 i L g g' hL hL' c c' γ₀ γ₁ hγ hγ' κ₀ κ₁ hpt hpt'

theorem IsCG1.mem {i : G.comp} {L : G.P.Tup} {c : cl} {γ₀ : GL (Fin n) E} (h : IsCG1 S A y i L c γ₀) :
    γ₀ ∈ UJ (σ : E →+* E) J := by
  obtain ⟨g, κ₀, -, hγ, -⟩ := h
  exact hγ

theorem IsCG1.smul (H : OneHyp S A y) {i : G.comp} {L : G.P.Tup} {c : cl} {γ₀ : GL (Fin n) E}
    (h : IsCG1 S A y i L c γ₀) (γ : (G.lev i).Γ) : IsCG1 S A y i ((G.lev i).smul γ L) c (A.gamI i γ * γ₀) := by
  obtain ⟨g, κ₀, hL, hγ, hpt⟩ := h
  obtain ⟨κ₁, h1⟩ := pt_smul H.good H.actB H.gam i g _ γ₀ κ₀ hpt γ
  exact ⟨_, κ₁, fun v => smul_colSpan i γ L g hL v, Subgroup.mul_mem _ (H.gamU i γ) hγ, h1⟩

theorem IsCG1.orbit (H : OneHyp S A y) {i i' : G.comp} {L L' : G.P.Tup} {c : cl} {γ₀ γ₁ : GL (Fin n) E}
    (h : IsCG1 S A y i L c γ₀) (h' : IsCG1 S A y i' L' c γ₁) : i = i' ∧ ∃ γ : (G.lev i).Γ, L' = (G.lev i).smul γ L := by
  obtain ⟨g, κ₀, hL, hγ, hpt⟩ := h
  obtain ⟨g', κ₁, hL', hγ', hpt'⟩ := h'
  obtain ⟨rfl, γ, -, hγL⟩ := orbit_of_pts H.good H.int H.hypC H.actB H.gam H.cinj H.onto i i' L L' g g' hL hL' _ γ₀ γ₁ hγ hγ' κ₀ κ₁
    hpt hpt'
  exact ⟨rfl, γ, hγL⟩

theorem IsCG1.pt (H : OneHyp S A y) {i : G.comp} {L : G.P.Tup} {c : cl} {γ₀ : GL (Fin n) E} (h : IsCG1 S A y i L c γ₀)
    (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hx : A.IsPt i g x.1) :
    ∃ κ : S.U, x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * (y c).1 * κ.1 := by
  obtain ⟨g', κ₀, hL', hγ, hpt⟩ := h
  obtain ⟨κ, e1, -⟩ := ptOne_of S H.int H.hypP H.bad_p i L g' g
    ⟨_, Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem hγ) (y c).2) (U_le κ₀.2)⟩ x hL' hL hpt hx
  refine ⟨κ₀ * κ, ?_⟩
  rw [e1]
  show _ * _ * _ * _ = _ * _ * (κ₀.1 * κ.1)
  group

theorem exists_isCG1_of_oneHyp (H : OneHyp S A y) (c : cl) : ∃ i L γ₀, G.P.IsLatTup L ∧ IsCG1 S A y i L c γ₀ := by
  obtain ⟨i, g, γ, κ, hγ, hpt⟩ := ptAll_of H.good S y H.comp c
  exact ⟨i, fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)), γ,
    isLatTup_of_bases1 _ g fun _ => rfl, g, κ, fun _ => rfl, hγ, hpt⟩

theorem IsCG1.card (H : OneHyp S A y) {stab : cl → Type} [∀ c, Group (stab c)]
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J) (hsinj : ∀ c, Function.Injective (stabI c))
    (hrange : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ S.U.map (MulAut.conj (y c).1).toMonoidHom)
    {i : G.comp} {L : G.P.Tup} {c : cl} {γ₀ : GL (Fin n) E} (h : IsCG1 S A y i L c γ₀) :
    Nat.card (stab c) = Nat.card {γ : (G.lev i).Γ // (G.lev i).smul γ L = L} := by
  obtain ⟨g, κ₀, hL, hγ, hpt⟩ := h
  exact card_eq H.good H.int H.hypP H.hypC H.bad_p H.actB H.gam H.gamU i (H.inj i) (H.onto i) L g hL y stabI hsinj hrange c γ₀ hγ κ₀ hpt

theorem cl_nonempty (H : OneHyp S A y) (i : G.comp) : Nonempty cl := by
  obtain ⟨c, -, -⟩ := exists_isCG1_bases H i (fun v => colSpan (G.P.W v) ((1 : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
    Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) (fun _ => 1) fun _ => rfl
  exact ⟨c⟩

def cg1 (H : OneHyp S A y) (i : G.comp) (L : G.P.Tup) : cl × GL (Fin n) E :=
  @Classical.epsilon _ ((cl_nonempty H i).map fun c => (c, 1)) fun q => IsCG1 S A y i L q.1 q.2

theorem class_map_spec (H : OneHyp S A y) (i : G.comp) (L : G.P.Tup) (hL : G.P.IsLatTup L) :
    IsCG1 S A y i L (cg1 H i L).1 (cg1 H i L).2 := by
  obtain ⟨c, γ₀, h⟩ := exists_isCG1 H i L hL
  exact @Classical.epsilon_spec _ (fun q : cl × GL (Fin n) E => IsCG1 S A y i L q.1 q.2) ⟨(c, γ₀), h⟩

theorem class_map_fst_eq (H : OneHyp S A y) {i : G.comp} {L : G.P.Tup} {c : cl} {γ₀ : GL (Fin n) E} (h : IsCG1 S A y i L c γ₀) :
    (cg1 H i L).1 = c := by
  obtain ⟨g, κ₀, hL, hγ, hpt⟩ := id h
  exact (class_map_spec H i L (isLatTup_of_bases1 L g hL)).cls_eq H h

def localClassDataOfTrivialStabilizers (H : OneHyp S A y) {X : Type} (e : cl ≃ X) {stab : cl → Type} [∀ c, Group (stab c)]
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J) (hsinj : ∀ c, Function.Injective (stabI c))
    (hrange : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ S.U.map (MulAut.conj (y c).1).toMonoidHom)
    (htriv : ∀ c, Nat.card (stab c) = 1) : Formalism.L2.G.TwTie0.LocalClassData G X where
  cls := fun i L => e (cg1 H i L).1
  cls_iff := fun i i' L L' hL hL' => by
    rw [e.injective.eq_iff]
    constructor
    · intro h
      have h1 := class_map_spec H i L hL
      have h2 := class_map_spec H i' L' hL'
      rw [← h] at h2
      exact h1.orbit H h2
    · rintro ⟨rfl, γ, rfl⟩
      exact (class_map_fst_eq H ((class_map_spec H i L hL).smul H γ)).symm
  cls_surj := fun x => by
    obtain ⟨i, L, γ₀, hL, h⟩ := exists_isCG1_of_oneHyp H (e.symm x)
    exact ⟨i, L, hL, by rw [class_map_fst_eq H h, Equiv.apply_symm_apply]⟩
  stab_zero := fun i L hL => by
    rw [← (class_map_spec H i L hL).card H stabI hsinj hrange]
    exact htriv _

end One

section Lev0

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
  {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)}
  {K0 : LevelChart D T bad 0 (Nat.zero_le _) stab lat} {A0 : LocAt D.host.F D.host.E (D.R.N 0) (D.gat u w h)}

def rationalElementZero (H : OneHyp K0.lev A0 K0.y) (a : (D.gat u w h).comp) (L : (D.gat u w h).P.Tup) : GL (Fin (D.R.N 0)) D.host.E :=
  (cg1 H a L).2

def levelZeroClass (H : OneHyp K0.lev A0 K0.y) (a : (D.gat u w h).comp) (L : (D.gat u w h).P.Tup) : cl := (cg1 H a L).1

def clsAt0Of (H : OneHyp K0.lev A0 K0.y) (e : cl ≃ (D.chTw u μ).cls 0) (htriv : ∀ c, Nat.card (stab c) = 1)
    {Fl : Fills (D.gat u w h)} (Lv : Levels Fl) : Formalism.L2.G.TwTie0.ClsAt0 D u μ w h Lv :=
  (localClassDataOfTrivialStabilizers H e K0.stabI K0.stabI_inj K0.stabI_range htriv).toAt0 Lv

theorem pt00 (H : OneHyp K0.lev A0 K0.y) (a : (D.gat u w h).comp) (L : (D.gat u w h).P.Tup)
    (g : ∀ v, GL (Fin ((D.gat u w h).P.m + 1)) ((D.gat u w h).P.Qq v))
    (hL : ∀ v, L v = colSpan ((D.gat u w h).P.W v) (g v : Matrix (Fin ((D.gat u w h).P.m + 1)) (Fin ((D.gat u w h).P.m + 1))
      ((D.gat u w h).P.Qq v)))
    (x : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (hx : A0.IsPt a g x.1) :
    rationalElementZero H a L ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ∧
    ∃ κ : K0.lev.U, x.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (rationalElementZero H a L) *
      (K0.y (levelZeroClass H a L)).1 * κ.1 :=
  ⟨(class_map_spec H a L (isLatTup_of_bases1 L g hL)).mem, (class_map_spec H a L (isLatTup_of_bases1 L g hL)).pt H g hL x hx⟩

end Lev0

end Formalism.MainNotions.G.KAat

end
