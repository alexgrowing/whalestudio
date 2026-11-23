import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypCard
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.CompInjLocJ

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PRankGe

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Module Formalism.MainNotions.G.CmpJ.PCard
open scoped TensorProduct

theorem finrank_le_span {O Kf W : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    [IsFractionRing O Kf] [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W] (M : Submodule O W)
    [FiniteDimensional Kf (Submodule.span Kf (M : Set W))] :
    finrank O M ≤ finrank Kf (Submodule.span Kf (M : Set W)) := by
  have hr : Module.rank O M ≤ (finrank Kf (Submodule.span Kf (M : Set W)) : Cardinal) := by
    refine rank_le fun s hs => ?_
    have h2 : LinearIndependent Kf fun k : s => ((k : M) : W) :=
      (LinearIndependent.iff_fractionRing O Kf).1 (hs.map' M.subtype M.ker_subtype)
    have h3 : LinearIndependent Kf fun k : s =>
        (⟨((k : M) : W), Submodule.subset_span (k : M).2⟩ : Submodule.span Kf (M : Set W)) :=
      LinearIndependent.of_comp (Submodule.span Kf (M : Set W)).subtype h2
    simpa using h3.fintype_card_le_finrank
  have h := Cardinal.toNat_le_toNat hr (Cardinal.natCast_lt_aleph0)
  rw [Cardinal.toNat_natCast] at h
  exact h

section Gen

variable {p : ℕ} (H : GAtP p)

def InvK (a : H.comp) (L : H.P.Tup) : Submodule H.Kf H.P.Xsp where
  carrier := {X | X ∈ Submodule.span H.Kf (H.P.HtupW L : Set H.P.Xsp) ∧
    ∀ γ : (H.lev a).Γ, (H.lev a).smul γ L = L → ((H.lev a).χ γ : H.O) • (H.lev a).actX γ X = X}
  zero_mem' := ⟨Submodule.zero_mem _, fun γ _ => by rw [map_zero, smul_zero]⟩
  add_mem' := fun {x y} hx hy => ⟨Submodule.add_mem _ hx.1 hy.1, fun γ hγ => by
    rw [map_add, smul_add, hx.2 γ hγ, hy.2 γ hγ]⟩
  smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, fun γ hγ => by
    rw [map_smul, ← algebraMap_smul H.Kf, smul_smul, mul_comm, ← smul_smul, algebraMap_smul, hx.2 γ hγ]⟩

def Eqv : Submodule H.Kf H.Fn where
  carrier := {F | ∀ a, (∀ L, H.P.IsLatTup L → F a L ∈ Submodule.span H.Kf (H.P.HtupW L : Set H.P.Xsp)) ∧
    (∀ L, ¬ H.P.IsLatTup L → F a L = 0) ∧
    ∀ (γ : (H.lev a).Γ) L, F a ((H.lev a).smul γ L) = ((H.lev a).χ γ : H.O) • (H.lev a).actX γ (F a L)}
  zero_mem' := fun a => ⟨fun L _ => Submodule.zero_mem _, fun _ _ => rfl, fun γ L => by
    simp only [Pi.zero_apply, map_zero, smul_zero]⟩
  add_mem' := fun {F F'} hF hF' a => ⟨fun L hL => Submodule.add_mem _ ((hF a).1 L hL) ((hF' a).1 L hL),
    fun L hL => by
      show F a L + F' a L = 0
      rw [(hF a).2.1 L hL, (hF' a).2.1 L hL, add_zero],
    fun γ L => by
      show F a _ + F' a _ = _
      rw [(hF a).2.2 γ L, (hF' a).2.2 γ L]
      show _ = ((H.lev a).χ γ : H.O) • (H.lev a).actX γ (F a L + F' a L)
      rw [map_add, smul_add]⟩
  smul_mem' := fun c F hF a => ⟨fun L hL => Submodule.smul_mem _ c ((hF a).1 L hL),
    fun L hL => by
      show c • F a L = 0
      rw [(hF a).2.1 L hL, smul_zero],
    fun γ L => by
      show c • F a _ = _
      rw [(hF a).2.2 γ L]
      show _ = ((H.lev a).χ γ : H.O) • (H.lev a).actX γ (c • F a L)
      rw [map_smul, ← algebraMap_smul H.Kf ((H.lev a).χ γ : H.O), ← algebraMap_smul H.Kf ((H.lev a).χ γ : H.O), smul_smul, smul_smul,
        mul_comm]⟩

theorem M_le_Eqv : (H.M : Set H.Fn) ⊆ Eqv H := by
  intro F hF a
  have h := (PCard.mem_M H).1 hF a
  simp only [Level.funMod, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun L hL => Submodule.subset_span (h1 L hL), fun L hL => h2 L hL, fun γ L => ?_⟩
  have := h3 γ L
  rw [LinearMap.sub_apply, sub_eq_zero] at this
  exact this

theorem span_le_Eqv : Submodule.span H.Kf (H.M : Set H.Fn) ≤ Eqv H :=
  Submodule.span_le.2 (M_le_Eqv H)

variable {Cl : Type} [Fintype Cl]

def Cover (rep : Cl → H.comp × H.P.Tup) : Prop :=
  ∀ a L, H.P.IsLatTup L → ∃ (c : Cl) (γ : (H.lev (rep c).1).Γ), (rep c).1 = a ∧ L = (H.lev (rep c).1).smul γ (rep c).2

theorem eqv_eq_zero {rep : Cl → H.comp × H.P.Tup} (hc : Cover H rep) {F : H.Fn} (hF : F ∈ Eqv H)
    (h0 : ∀ c, F (rep c).1 (rep c).2 = 0) : F = 0 := by
  funext a L
  by_cases hL : H.P.IsLatTup L
  · obtain ⟨c, γ, rfl, rfl⟩ := hc a L hL
    rw [(hF _).2.2 γ _, h0 c, map_zero, smul_zero]
    rfl
  · exact (hF a).2.1 L hL

theorem eqv_mem_InvK {F : H.Fn} (hF : F ∈ Eqv H) (a : H.comp) (L : H.P.Tup) : F a L ∈ InvK H a L := by
  by_cases hL : H.P.IsLatTup L
  · refine ⟨(hF a).1 L hL, fun γ hγ => ?_⟩
    have := (hF a).2.2 γ L
    rw [hγ] at this
    exact this.symm
  · rw [(hF a).2.1 L hL]
    exact Submodule.zero_mem _

def evR (rep : Cl → H.comp × H.P.Tup) :
    Submodule.span H.Kf (H.M : Set H.Fn) →ₗ[H.Kf] ((c : Cl) → InvK H (rep c).1 (rep c).2) where
  toFun F c := ⟨F.1 (rep c).1 (rep c).2, eqv_mem_InvK H (span_le_Eqv H F.2) _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evR_inj {rep : Cl → H.comp × H.P.Tup} (hc : Cover H rep) : Function.Injective (evR H rep) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  apply Subtype.ext
  exact eqv_eq_zero H hc (span_le_Eqv H F.2) fun c => congrArg Subtype.val (congrFun hF c)

theorem finrank_le_of_cover [IsFractionRing H.O H.Kf] {rep : Cl → H.comp × H.P.Tup} (hc : Cover H rep)
    (hfin : ∀ c, FiniteDimensional H.Kf (InvK H (rep c).1 (rep c).2)) :
    finrank H.O H.M ≤ ∑ c, finrank H.Kf (InvK H (rep c).1 (rep c).2) := by
  have : FiniteDimensional H.Kf (Submodule.span H.Kf (H.M : Set H.Fn)) := Module.Finite.of_injective (evR H rep) (evR_inj H hc)
  calc finrank H.O H.M ≤ finrank H.Kf (Submodule.span H.Kf (H.M : Set H.Fn)) := finrank_le_span H.M
    _ ≤ finrank H.Kf ((c : Cl) → InvK H (rep c).1 (rep c).2) := LinearMap.finrank_le_finrank_of_injective (evR_inj H hc)
    _ = ∑ c, finrank H.Kf (InvK H (rep c).1 (rep c).2) := Module.finrank_pi_fintype H.Kf

end Gen

section Forms

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

open Classical

abbrev Hc (S : StepIn M i hi G) (β : S.Ch) : GAtP p := gatCh G fun a : S.cmpt β => S.eC ⟨β, a⟩

def projC {Cl X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ (Cl → X)) (c : Cl) : Submodule ℂ X :=
  V.map (LinearMap.proj (R := ℂ) (φ := fun _ : Cl => X) c)

def IsPiSub {Cl X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ (Cl → X)) : Prop :=
  ∀ f : Cl → X, (∀ c, f c ∈ projC V c) → f ∈ V

abbrev FiBc (S : StepIn M i hi G) (β : S.Ch) (c : {c // S.chOf c = β}) := projC (FiB S β) c

def FiBPi (S : StepIn M i hi G) (β : S.Ch) : Prop := IsPiSub (FiB S β)

theorem finDim_FiB (S : StepIn M i hi G) (β : S.Ch) (hβ : β ∈ chs S) : FiniteDimensional ℂ (FiB S β) := by
  classical
  have := fin_Fi M i
  have : Module.Finite ℂ ((β : chs S) → FiB S β.1) := Module.Finite.equiv (eF S)
  exact fin_fac (R := ℂ) (φ := fun β : chs S => FiB S β.1) ⟨β, hβ⟩

theorem sum_le_finrank_FiB (S : StepIn M i hi G) (β : S.Ch) (hπ : FiBPi S β) :
    ∑ c, finrank ℂ (FiBc S β c) ≤ finrank ℂ (FiB S β) := by
  rcases isEmpty_or_nonempty {c // S.chOf c = β} with he | hne
  · simp [Finset.univ_eq_empty]
  · obtain ⟨c₀⟩ := hne
    have : FiniteDimensional ℂ (FiB S β) := finDim_FiB S β (c₀.2 ▸ chOf_mem S c₀.1)
    have : ∀ c, FiniteDimensional ℂ (FiBc S β c) := fun c => Module.Finite.map _ _
    let ψ : ((c : {c // S.chOf c = β}) → FiBc S β c) →ₗ[ℂ] FiB S β :=
      { toFun := fun g => ⟨fun c => (g c).1, hπ _ fun c => (g c).2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hψ : Function.Injective ψ := by
      intro g g' h
      funext c
      exact Subtype.ext (congrFun (congrArg Subtype.val h) c)
    rw [← Module.finrank_pi_fintype ℂ]
    exact LinearMap.finrank_le_finrank_of_injective hψ

def RankTie (S : StepIn M i hi G) (β : S.Ch) : Prop :=
  KAat.CompInj (S.K β).lev (S.loc β) ∧ (∀ a, PStabEq.GamOnto (S.K β).lev (S.loc β) a) ∧ PStabEq.LocHypC (S.K β).lev (S.loc β)

def RepOk (S : StepIn M i hi G) (β : S.Ch) (rep : {c // S.chOf c = β} → S.cmpt β × (Hc S β).P.Tup) : Prop :=
  ∀ c, ∃ (g : ∀ v, GL (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v)) (γ₀ : GL (Fin (D.R.N i)) D.host.E) (κ₀ : (S.K β).lev.U),
    γ₀ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) ∧
    (∀ v, (rep c).2 v = colSpan ((Hc S β).P.W v) (g v : Matrix (Fin ((Hc S β).P.m + 1)) (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v))) ∧
    (S.loc β).IsPt (rep c).1 g (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ₀ * ((S.K β).y c).1 * κ₀.1)

theorem rankTie_of_chX {S : StepIn M i hi G} (X : KAat.ChX S) (β : S.Ch) : RankTie S β :=
  ⟨X.cinj β, X.onto β, X.hypC β⟩

theorem coverOf {S : StepIn M i hi G} {e : D.what₂.LL →+* G.Kf} (H : ∀ β, S.Core e β) (X : KAat.ChX S) (β : S.Ch) :
    ∃ rep, RepOk S β rep ∧ Cover (Hc S β) rep := by
  have hex : ∀ c : {c // S.chOf c = β}, ∃ (a0 : S.cmpt β) (L : G.P.Tup) (γ₀ : GL (Fin (D.R.N i)) D.host.E),
      G.P.IsLatTup L ∧ KAat.IsCG S (S.eC ⟨β, a0⟩) L c.1 γ₀ := by
    rintro ⟨c0, hc0⟩
    subst hc0
    obtain ⟨a, L, γ₀, hL, hcg⟩ := KAat.exists_of_cls H c0
    obtain ⟨β', a0, hc, g, κ₀, ha, hrest⟩ := id hcg
    subst hc
    exact ⟨a0, L, γ₀, hL, ha ▸ hcg⟩
  choose a0 L γ₀ hL hcg using hex
  refine ⟨fun c => (a0 c, L c), fun c => ?_, fun a L' hL' => ?_⟩
  · obtain ⟨β', a0', hc, g, κ₀, ha, hLg, hγ, hpt⟩ := hcg c
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 (S.eC.injective ha)
    cases eq_of_heq h
    exact ⟨g, γ₀ c, κ₀, hγ, hLg, hpt⟩
  · obtain ⟨c1, γ1, h1⟩ := KAat.exists_isCG H (S.eC ⟨β, a⟩) L' hL'
    have hc1 : S.chOf c1 = β := by rw [KAat.IsCG.chart h1, Equiv.symm_apply_apply]
    obtain ⟨ha, γ, hγ⟩ := KAat.IsCG.orbit H X (hcg ⟨c1, hc1⟩) h1
    obtain ⟨-, h⟩ := Sigma.mk.inj_iff.1 (S.eC.injective ha)
    exact ⟨⟨c1, hc1⟩, γ, eq_of_heq h, hγ⟩

def InvLeOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c,
    FiniteDimensional G.Kf (InvK (Hc S β) (rep c).1 (rep c).2) ∧
      finrank G.Kf (InvK (Hc S β) (rep c).1 (rep c).2) ≤ finrank ℂ (FiBc S β c)

def FiBPiAll (S : StepIn M i hi G) : Prop := ∀ β, FiBPi S β

theorem mk_eq_of (S : StepIn M i hi G) (β : S.Ch) {γ : GL (Fin (D.R.N i)) D.host.E}
    (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    {x x' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)} {κ : (S.K β).lev.U}
    (hx : x'.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * x.1 * κ.1) :
    (Quotient.mk'' x' : Cls (S.K β).lev) = Quotient.mk'' x := by
  symm
  refine (DoubleCoset.eq _ _ _ _).2 ⟨⟨_, PStabEq.bc_mem hγ⟩, Subgroup.mem_subgroupOf.2 ⟨γ, hγ, rfl⟩, ⟨_, PStabEq.U_le κ.2⟩,
    Subgroup.mem_subgroupOf.2 κ.2, Subtype.ext ?_⟩
  exact hx

set_option maxHeartbeats 1000000 in

theorem fiBPi (S : StepIn M i hi G) (β : S.Ch) : FiBPi S β := by
  intro f hf
  have hφ : ∀ c, ∃ φ ∈ AdForms (S.K β).lev (embT D) (lamTG M i), φ ((S.K β).y c) = f c := by
    intro c
    obtain ⟨φ', hφ', e⟩ := Submodule.mem_map.1 (hf c)
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 hφ'
    exact ⟨φ, hφ, e⟩
  choose φ hφA hφy using hφ
  let g := fun (c : {c // S.chOf c = β}) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =>
    if (Quotient.mk'' x : Cls (S.K β).lev) = Quotient.mk'' ((S.K β).y c) then φ c x else 0
  have hg : ∀ c, g c ∈ AdForms (S.K β).lev (embT D) (lamTG M i) := by
    intro c
    have h2 := hφA c
    unfold AdForms at h2 ⊢
    rw [Submodule.mem_inf] at h2 ⊢
    obtain ⟨hA, hV⟩ := h2
    refine ⟨?_, ?_⟩
    · intro γ hγ x x' κ hx y y' hy
      have h1 := hA γ hγ x x' κ hx y y' hy
      have hq := mk_eq_of S β hγ hx
      by_cases hxc : (Quotient.mk'' x : Cls (S.K β).lev) = Quotient.mk'' ((S.K β).y c)
      · have hxc' : (Quotient.mk'' x' : Cls (S.K β).lev) = Quotient.mk'' ((S.K β).y c) := hq.trans hxc
        simp only [g, if_pos hxc, if_pos hxc']
        exact h1
      · have hxc' : ¬ (Quotient.mk'' x' : Cls (S.K β).lev) = Quotient.mk'' ((S.K β).y c) := fun h => hxc (hq.symm.trans h)
        simp only [g, if_neg hxc, if_neg hxc', Pi.zero_apply, mul_zero]
    · refine Submodule.mem_pi.2 fun x _ => ?_
      by_cases hxc : (Quotient.mk'' x : Cls (S.K β).lev) = Quotient.mk'' ((S.K β).y c)
      · simp only [g, if_pos hxc]
        exact Submodule.mem_pi.1 hV x (Set.mem_univ x)
      · simp only [g, if_neg hxc]
        exact Submodule.zero_mem _
  have hsum : f = ∑ c, res (embT D) (S.K β).y (g c) := by
    funext c' z
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single c']
    · show f c' z = g c' ((S.K β).y c') z
      simp only [g, if_pos rfl]
      rw [hφy]
    · intro c _ hc
      show g c ((S.K β).y c') z = 0
      have hne : ¬ (Quotient.mk'' ((S.K β).y c') : Cls (S.K β).lev) = Quotient.mk'' ((S.K β).y c) :=
        fun h => hc ((S.K β).y_bij.1 h).symm
      simp only [g, if_neg hne, Pi.zero_apply]
    · intro h
      exact absurd (Finset.mem_univ c') h
  rw [hsum]
  exact Submodule.sum_mem _ fun c _ => Submodule.mem_map_of_mem (hg c)

theorem fiBPiAll (S : StepIn M i hi G) : FiBPiAll S := fun β => fiBPi S β

theorem chartRankGe_of [IsFractionRing G.O G.Kf] (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β)
    (hS : BlockRationalityField) (X : KAat.ChX S) (hI : InvLeOf S e) : ChartRankGe S := by
  intro β
  obtain ⟨rep, hok, hcov⟩ := coverOf H X β
  have hI' := hI hS H X β rep hok
  have : ∀ c, FiniteDimensional (Hc S β).Kf (InvK (Hc S β) (rep c).1 (rep c).2) := fun c => (hI' c).1
  calc finrank G.O (Hc S β).M ≤ ∑ c, finrank G.Kf (InvK (Hc S β) (rep c).1 (rep c).2) := finrank_le_of_cover (Hc S β) hcov this
    _ ≤ ∑ c, finrank ℂ (FiBc S β c) := Finset.sum_le_sum fun c _ => (hI' c).2
    _ ≤ finrank ℂ (FiB S β) := sum_le_finrank_FiB S β (fiBPi S β)

end Forms

section LocJ

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  (hi : i + 1 ≤ D.R.m) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

theorem chartRankGe_stepInOf [IsFractionRing (gatJ Lv (i + 1)).O (gatJ Lv (i + 1)).Kf] (Fo : FormsIn M (i + 1) hi)
    (Lc : LocIn X u w hg Lv i Fo.Ch) (pos : (Σ v : Fin (Fl.Pj (i + 1)).nV, Fin ((Fl.Pj (i + 1)).n' v)) ≃ D.what₂.Tau)
    (hU : ∀ β, SameUlocJ hi (Fo.K β).lev (Lc.Uloc β)) (hB : ∀ β, FrRatJ (Lc.t β) Lc.B) (hTc : ∀ β, PStabEq.HypTJC (Lc.t β))
    (e : D.what₂.LL →+* (gatJ Lv (i + 1)).Kf) (H : ∀ β, (stepInOf hi Fo Lc pos).Core e β) (hS : BlockRationalityField)
    (hI : InvLeOf (stepInOf hi Fo Lc pos) e) : ChartRankGe (stepInOf hi Fo Lc pos) :=
  chartRankGe_of _ e H hS (KAat.chX_stepInOf hi Fo Lc pos hU hB hTc) hI

end LocJ

end Formalism.MainNotions.G.CmpJ.PRankGe
