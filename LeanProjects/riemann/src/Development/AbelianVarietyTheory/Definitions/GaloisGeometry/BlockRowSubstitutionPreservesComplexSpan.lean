import Mathlib
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypCard
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.CompInjLocJ
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfRatInv
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LowestInvariantLeDelta
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ProdMemSpan
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CastGLSymmBc
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR
import Formalism.LocalToGlobal.GlobalTheory.GL6.ValuationClassTranslateMem
import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescentHolds
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LiMap
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.PStabEq
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypVin
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocCore
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypTwA
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ExistsIsCGBases
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLat
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypChi
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TiedCls
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocTiesOf
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt

noncomputable section

section

namespace GlobalTheory.HP
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ

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

end LocJ

end GlobalTheory.HP
end

section

namespace GlobalTheory.HP
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms NumberField Module Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard
  GlobalTheory.HP

section Gen

variable {LL K C Y WK V : Type} [Field LL] [Field K] [Field C] (e : LL →+* K)
  [AddCommGroup Y] [Module LL Y] [AddCommGroup WK] [Module K WK] [AddCommGroup V] [Module C V]

theorem finrank_le_transfer (φK : Y →+ WK) (hK : ∀ (a : LL) y, φK (a • y) = e a • φK y)
    (φC : Y →+ V) [FiniteDimensional C V]
    (hind : ∀ (k : ℕ) (y : Fin k → Y), LinearIndependent LL y → LinearIndependent C (φC ∘ y))
    (N : Submodule K WK) (hN : N ≤ Submodule.span K (Set.range φK)) :
    FiniteDimensional K N ∧ finrank K N ≤ finrank C V := by
  have hr : Module.rank LL Y ≤ (finrank C V : Cardinal) := by
    refine rank_le fun s hs => ?_
    have h := hind s.card (fun j => ((s.equivFin.symm j : s) : Y)) (hs.comp _ s.equivFin.symm.injective)
    simpa using h.fintype_card_le_finrank
  have : FiniteDimensional LL Y := Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt hr Cardinal.natCast_lt_aleph0)
  let b := Module.finBasis LL Y
  have hsp : Submodule.span K (Set.range φK) ≤ Submodule.span K (Set.range fun j => φK (b j)) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [← b.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [hK]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hle := hN.trans hsp
  have : FiniteDimensional K (Submodule.span K (Set.range fun j => φK (b j))) :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  have : FiniteDimensional K N := Submodule.finiteDimensional_of_le hle
  refine ⟨this, ?_⟩
  calc finrank K N ≤ finrank K (Submodule.span K (Set.range fun j => φK (b j))) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (finrank LL Y)) := finrank_range_le_card _
    _ = finrank LL Y := Fintype.card_fin _
    _ ≤ finrank C V := by
      have h := hind _ (fun j => b j) b.linearIndependent
      simpa using h.fintype_card_le_finrank

end Gen

section RatPts

variable {LL Kf : Type} [Field LL] [Field Kf] (e : LL →+* Kf)

theorem mapE_smul {σ : Type} (r : LL) (Q : MvPolynomial σ LL) :
    MvPolynomial.map e (r • Q) = e r • MvPolynomial.map e Q := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

theorem ker_desc {σ τ : Type} (Ts : Set (MvPolynomial σ Kf →ₗ[Kf] MvPolynomial τ Kf))
    (hT : ∀ T ∈ Ts, ∀ Q : MvPolynomial σ LL, ∃ Q' : MvPolynomial τ LL, MvPolynomial.map e Q' = T (MvPolynomial.map e Q))
    {ξ : MvPolynomial σ Kf} (hξ : ∀ T ∈ Ts, T ξ = 0) :
    ξ ∈ Submodule.span Kf (MvPolynomial.map e '' {Q | ∀ T ∈ Ts, T (MvPolynomial.map e Q) = 0}) := by
  let φ : MvPolynomial σ LL × MvPolynomial τ LL →+ MvPolynomial σ Kf × MvPolynomial τ Kf :=
    AddMonoidHom.prodMap (MvPolynomial.map e).toAddMonoidHom (MvPolynomial.map e).toAddMonoidHom
  let ev : (σ →₀ ℕ) ⊕ (τ →₀ ℕ) → (MvPolynomial σ Kf × MvPolynomial τ Kf) →ₗ[Kf] Kf :=
    Sum.elim (fun m => (MvPolynomial.lcoeff Kf m).comp (LinearMap.fst Kf _ _))
      (fun m => (MvPolynomial.lcoeff Kf m).comp (LinearMap.snd Kf _ _))
  have hsep : ∀ F, (∀ t, ev t F = 0) → F = 0 := by
    intro F h
    refine Prod.ext (MvPolynomial.ext _ _ fun m => ?_) (MvPolynomial.ext _ _ fun m => ?_)
    · simpa [ev] using h (Sum.inl m)
    · simpa [ev] using h (Sum.inr m)
  have hsm : ∀ (a : LL) x, φ (a • x) = e a • φ x := fun a x =>
    Prod.ext (mapE_smul e a x.1) (mapE_smul e a x.2)
  have hval : ∀ x, IsRat e ev (φ x) := by
    rintro x (m | m)
    · exact ⟨MvPolynomial.coeff m x.1, by simp [ev, φ, MvPolynomial.coeff_map]⟩
    · exact ⟨MvPolynomial.coeff m x.2, by simp [ev, φ, MvPolynomial.coeff_map]⟩
  let S : Set ((MvPolynomial σ Kf × MvPolynomial τ Kf) →ₗ[Kf] (MvPolynomial σ Kf × MvPolynomial τ Kf)) :=
    {Tm | ∃ T ∈ Ts, Tm = LinearMap.id + (LinearMap.inr Kf _ _).comp (T.comp (LinearMap.fst Kf _ _))}
  have hS : ∀ Tm ∈ S, ∀ x, ∃ y, φ y = Tm (φ x) := by
    rintro Tm ⟨T, hT', rfl⟩ x
    obtain ⟨Q', hQ'⟩ := hT T hT' x.1
    refine ⟨(x.1, x.2 + Q'), Prod.ext ?_ ?_⟩ <;> simp [φ, hQ']
  have key : ∀ p : MvPolynomial σ Kf, (p, (0 : MvPolynomial τ Kf)) ∈ Submodule.span Kf (Set.range φ) := by
    intro p
    refine MvPolynomial.induction_on' p (fun m c => ?_) (fun p q hp hq => ?_)
    · have h1 : (MvPolynomial.monomial m c, (0 : MvPolynomial τ Kf)) = c • φ (MvPolynomial.monomial m 1, 0) := by
        simp [φ, MvPolynomial.smul_monomial]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · have h2 : (p + q, (0 : MvPolynomial τ Kf)) = (p, 0) + (q, 0) := by simp
      rw [h2]
      exact Submodule.add_mem _ hp hq
  have hinv : ∀ Tm ∈ S, Tm (ξ, 0) = (ξ, 0) := by
    rintro Tm ⟨T, hT', rfl⟩
    simp [hξ T hT']
  have h := span_inv e ev φ hsep hsm hval S hS (key ξ) hinv
  have h' := Submodule.mem_map_of_mem (f := LinearMap.fst Kf (MvPolynomial σ Kf) (MvPolynomial τ Kf)) h
  rw [Submodule.map_span] at h'
  refine Submodule.span_mono ?_ h'
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨x.1, fun T hT' => ?_, rfl⟩
  have := congrArg Prod.snd (hx _ ⟨T, hT', rfl⟩)
  simpa [φ] using this

theorem whc_map {σ M : Type} [AddCommMonoid M] [DecidableEq M] (w : σ → M) (n : M) (Q : MvPolynomial σ LL) :
    MvPolynomial.map e (MvPolynomial.weightedHomogeneousComponent w n Q) =
      MvPolynomial.weightedHomogeneousComponent w n (MvPolynomial.map e Q) := by
  ext d
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem isWH_iff {σ M R : Type} [CommSemiring R] [AddCommMonoid M] [DecidableEq M] (w : σ → M) (n : M) (f : MvPolynomial σ R) :
    MvPolynomial.IsWeightedHomogeneous w f n ↔ MvPolynomial.weightedHomogeneousComponent w n f = f := by
  constructor
  · intro h
    ext d
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    split_ifs with hd
    · rfl
    · by_contra hc
      exact hd (h (Ne.symm hc))
  · intro h d hd
    rw [← h, MvPolynomial.coeff_weightedHomogeneousComponent] at hd
    by_contra hc
    exact hd (if_neg hc)

theorem colAddGen_map {r n : ℕ} (l j : Fin n) (Q : MvPolynomial (Fin r × Fin n) LL) :
    MvPolynomial.map e (Formalism.GradedWeylDivisibility.colAddGen LL l j Q) = Formalism.GradedWeylDivisibility.colAddGen Kf l j (MvPolynomial.map e Q) := by
  induction Q using MvPolynomial.induction_on
  · rename_i a
    simp [Formalism.GradedWeylDivisibility.colAddGen]
  · rename_i p q hp hq
    simp only [map_add, hp, hq]
  · rename_i p v hp
    simp only [map_mul]
    rw [hp, MvPolynomial.map_X]
    congr 1
    simp only [Formalism.GradedWeylDivisibility.colAddGen, MvPolynomial.aeval_X]
    split_ifs <;> simp

theorem dualWeyl_desc {r n : ℕ} (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl Kf r n ν ≤
      Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈ Formalism.GradedWeylDivisibility.dualWeyl Kf r n ν}) := by
  let Ts : Set (MvPolynomial (Fin r × Fin n) Kf →ₗ[Kf] MvPolynomial (Option (Fin r × Fin n)) Kf) :=
    {T | T = (MvPolynomial.rename some).toLinearMap.comp
        (LinearMap.id - MvPolynomial.weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.colW r n) ν)} ∪
      {T | ∃ l j : Fin n, l < j ∧ T = (Formalism.GradedWeylDivisibility.colAddGen Kf l j).toLinearMap - (MvPolynomial.rename some).toLinearMap}
  have hiff : ∀ f, f ∈ Formalism.GradedWeylDivisibility.dualWeyl Kf r n ν ↔ ∀ T ∈ Ts, T f = 0 := by
    intro f
    rw [Formalism.GradedWeylDivisibility.mem_dualWeyl_iff, isWH_iff]
    constructor
    · rintro ⟨h1, h2⟩ T (hT | ⟨l, j, hlj, hT⟩)
      · rw [hT]
        simp [h1]
      · rw [hT]
        simp [h2 l j hlj]
    · intro h
      refine ⟨?_, fun l j hlj => ?_⟩
      · have := h _ (Or.inl rfl)
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply] at this
        have h0 := MvPolynomial.rename_injective some (Option.some_injective _) (this.trans (map_zero _).symm)
        exact (sub_eq_zero.1 h0).symm
      · have := h _ (Or.inr ⟨l, j, hlj, rfl⟩)
        simpa [sub_eq_zero] using this
  have hT : ∀ T ∈ Ts, ∀ Q : MvPolynomial (Fin r × Fin n) LL, ∃ Q' : MvPolynomial (Option (Fin r × Fin n)) LL,
      MvPolynomial.map e Q' = T (MvPolynomial.map e Q) := by
    rintro T (hT | ⟨l, j, hlj, hT⟩) Q <;> rw [hT]
    · exact ⟨MvPolynomial.rename some (Q - MvPolynomial.weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.colW r n) ν Q), by
        simp [MvPolynomial.map_rename, whc_map]⟩
    · exact ⟨Formalism.GradedWeylDivisibility.colAddGen LL l j Q - MvPolynomial.rename some Q, by
        simp [MvPolynomial.map_rename, colAddGen_map]⟩
  intro ξ hξ
  refine Submodule.span_mono ?_ (ker_desc e Ts hT ((hiff ξ).1 hξ))
  rintro _ ⟨Q, hQ, rfl⟩
  exact ⟨Q, (hiff _).2 hQ, rfl⟩

theorem prod_desc {S : Type} [Fintype S] {σ : S → Type} {τ : Type} (f : ∀ s, σ s → τ)
    (Ms : ∀ s, Submodule Kf (MvPolynomial (σ s) Kf))
    (hM : ∀ s, Ms s ≤ Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈ Ms s})) :
    Submodule.span Kf {Z | ∃ F : ∀ s, MvPolynomial (σ s) Kf, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} ≤
      Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈ Submodule.span Kf
        {Z | ∃ F : ∀ s, MvPolynomial (σ s) Kf, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)}}) := by
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  let A : S → Set (MvPolynomial τ Kf) := fun s =>
    {y | ∃ Q : MvPolynomial (σ s) LL, MvPolynomial.map e Q ∈ Ms s ∧ y = MvPolynomial.rename (f s) (MvPolynomial.map e Q)}
  have hx : ∀ s ∈ Finset.univ, MvPolynomial.rename (f s) (F s) ∈ Submodule.span Kf (A s) := by
    intro s _
    have h1 := Submodule.mem_map_of_mem (f := (MvPolynomial.rename (R := Kf) (f s)).toLinearMap) (hM s (hF s))
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨Q, hQ, rfl⟩, rfl⟩
    exact ⟨Q, hQ, rfl⟩
  have h := prod_mem_span Finset.univ A _ hx
  refine Submodule.span_mono ?_ h
  rintro _ ⟨a, ha, rfl⟩
  choose Q hQ hQe using fun s => ha s (Finset.mem_univ s)
  refine ⟨∏ s, MvPolynomial.rename (f s) (Q s), ?_, ?_⟩
  · change MvPolynomial.map e (∏ s, MvPolynomial.rename (f s) (Q s)) ∈ Submodule.span Kf
      {Z | ∃ F : ∀ s, MvPolynomial (σ s) Kf, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)}
    rw [map_prod]
    refine Submodule.subset_span ⟨fun s => MvPolynomial.map e (Q s), hQ, ?_⟩
    simp [MvPolynomial.map_rename]
  · rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hQe s, MvPolynomial.map_rename]

theorem vsp_desc {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    Vsp Kf lam0 ≤ Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈ Vsp Kf lam0}) := by
  have hM : ∀ s : Fin n', (if Antitone (lamAt lam0 s) then Formalism.GradedWeylDivisibility.dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥) ≤
      Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈
        (if Antitone (lamAt lam0 s) then Formalism.GradedWeylDivisibility.dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥)}) := by
    intro s
    split_ifs
    · exact dualWeyl_desc e _
    · exact bot_le
  exact prod_desc e (σ := fun _ => Fin (m + 1) × Fin (m + 1)) (fun s v => (s, v)) _ hM

end RatPts

section Inv

variable {p : ℕ} (H : GAtP p) {LL : Type} [Field LL] (e : LL →+* H.Kf)

abbrev YR (H : GAtP p) (LL : Type) [Field LL] : Type :=
  MvPolynomial (Σ v : Fin H.P.nV, Fin (H.P.n' v) × (Fin (H.P.m + 1) × Fin (H.P.m + 1))) LL

theorem map_smul_e (r : LL) (Q : YR H LL) : MvPolynomial.map e (r • Q) = e r • MvPolynomial.map e Q := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

def YInv (a : H.comp) (L : H.P.Tup) : Submodule LL (YR H LL) where
  carrier := {Q | MvPolynomial.map e Q ∈ H.P.Vtup ∧ ∀ γ : (H.lev a).Γ, (H.lev a).smul γ L = L →
    ((H.lev a).χ γ : H.O) • (H.lev a).actX γ (MvPolynomial.map e Q) = MvPolynomial.map e Q}
  add_mem' := fun {Q Q'} h h' => by
    simp only [Set.mem_ofPred_eq, map_add] at h h' ⊢
    exact ⟨Submodule.add_mem _ h.1 h'.1, fun γ hγ => by rw [smul_add, h.2 γ hγ, h'.2 γ hγ]⟩
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact ⟨Submodule.zero_mem _, fun γ _ => by rw [smul_zero]⟩
  smul_mem' := fun r Q h => by
    simp only [Set.mem_ofPred_eq] at h ⊢
    rw [map_smul_e]
    refine ⟨Submodule.smul_mem _ _ h.1, fun γ hγ => ?_⟩
    rw [map_smul, ← algebraMap_smul H.Kf, smul_smul, mul_comm, ← smul_smul, algebraMap_smul, h.2 γ hγ]

def SpanRat : Prop :=
  H.P.Vtup ≤ Submodule.span H.Kf (MvPolynomial.map e '' {Q : YR H LL | MvPolynomial.map e Q ∈ H.P.Vtup})

def ActRat (a : H.comp) (L : H.P.Tup) : Prop :=
  ∀ γ : (H.lev a).Γ, (H.lev a).smul γ L = L → ∀ Q : YR H LL, MvPolynomial.map e Q ∈ H.P.Vtup →
    ∃ Q' : YR H LL, MvPolynomial.map e Q' ∈ H.P.Vtup ∧
      MvPolynomial.map e Q' = ((H.lev a).χ γ : H.O) • (H.lev a).actX γ (MvPolynomial.map e Q)

theorem spanRat_holds : SpanRat H e :=
  prod_desc e (σ := fun v => Fin (H.P.n' v) × (Fin (H.P.m + 1) × Fin (H.P.m + 1)))
    (fun v x => (⟨v, x⟩ : Σ v : Fin H.P.nV, Fin (H.P.n' v) × (Fin (H.P.m + 1) × Fin (H.P.m + 1))))
    (fun v => Vsp H.Kf (H.P.lam0 v)) (fun v => vsp_desc e (H.P.lam0 v))

theorem span_HtupW_le {L : H.P.Tup} (hL : H.P.IsLatTup L) :
    Submodule.span H.Kf (H.P.HtupW L : Set H.P.Xsp) ≤ H.P.Vtup :=
  Submodule.span_le.2 fun z hz => Formalism.MainNotions.FormalGroupSystem.Pf.vt_HtupW_le H.P L hL z hz

theorem inv_le_span {a : H.comp} {L : H.P.Tup} (hL : H.P.IsLatTup L) (h1 : SpanRat H e) (h2 : ActRat H e a L) :
    InvK H a L ≤ Submodule.span H.Kf (MvPolynomial.map e '' (YInv H e a L : Set (YR H LL))) := by
  intro ξ hξ
  let Vr : Submodule LL (YR H LL) :=
    { carrier := {Q | MvPolynomial.map e Q ∈ H.P.Vtup}
      add_mem' := fun {Q Q'} h h' => by
        simp only [Set.mem_ofPred_eq, map_add] at h h' ⊢
        exact Submodule.add_mem _ h h'
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        exact Submodule.zero_mem _
      smul_mem' := fun r Q h => by
        simp only [Set.mem_ofPred_eq] at h ⊢
        rw [map_smul_e]
        exact Submodule.smul_mem _ _ h }
  let φ : Vr →+ H.P.Xsp := (MvPolynomial.map e).toAddMonoidHom.comp Vr.subtype.toAddMonoidHom
  let Sx : Set (H.P.Xsp →ₗ[H.Kf] H.P.Xsp) :=
    {Tm | ∃ γ : (H.lev a).Γ, (H.lev a).smul γ L = L ∧ Tm = algebraMap H.O H.Kf ((H.lev a).χ γ : H.O) • (H.lev a).actX γ}
  have hsm : ∀ (r : LL) (x : Vr), φ (r • x) = e r • φ x := fun r x => map_smul_e H e r x.1
  have hval : ∀ x : Vr, IsRat e (evX H) (φ x) := fun x m =>
    ⟨MvPolynomial.coeff m x.1, by simp [φ, evX, MvPolynomial.lcoeff_apply, MvPolynomial.coeff_map]⟩
  have hT : ∀ Tm ∈ Sx, ∀ x : Vr, ∃ y : Vr, φ y = Tm (φ x) := by
    rintro Tm ⟨γ, hγ, rfl⟩ x
    obtain ⟨Q', hQ', e'⟩ := h2 γ hγ x.1 x.2
    refine ⟨⟨Q', hQ'⟩, ?_⟩
    simp only [φ, LinearMap.smul_apply, algebraMap_smul]
    exact e'
  have hξs : ξ ∈ Submodule.span H.Kf (Set.range φ) := by
    refine Submodule.span_mono ?_ (h1 (span_HtupW_le H hL hξ.1))
    rintro _ ⟨Q, hQ, rfl⟩
    exact ⟨⟨Q, hQ⟩, rfl⟩
  have hinv : ∀ Tm ∈ Sx, Tm ξ = ξ := by
    rintro Tm ⟨γ, hγ, rfl⟩
    simp only [LinearMap.smul_apply, algebraMap_smul]
    exact hξ.2 γ hγ
  have h := span_inv e (evX H) φ (evX_sep H) hsm hval Sx hT hξs hinv
  refine Submodule.span_mono ?_ h
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x.1, ⟨x.2, fun γ hγ => ?_⟩, rfl⟩
  have := hx _ ⟨γ, hγ, rfl⟩
  simp only [LinearMap.smul_apply, algebraMap_smul] at this
  exact this

end Inv

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem isLatTup_of_repOk {S : StepIn M i hi G} {β : S.Ch} {rep : {c // S.chOf c = β} → S.cmpt β × (Hc S β).P.Tup}
    (hok : RepOk S β rep) (c : {c // S.chOf c = β}) : (Hc S β).P.IsLatTup (rep c).2 := by
  obtain ⟨g, -, -, -, hg, -⟩ := hok c
  intro v
  exact ⟨(g v : Matrix _ _ _), (Matrix.isUnit_iff_isUnit_det _).1 (g v).isUnit, hg v⟩

def ActRatOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c, ActRat (Hc S β) e (rep c).1 (rep c).2

theorem actRat_of_core {S : StepIn M i hi G} {e : D.what₂.LL →+* G.Kf} {β : S.Ch} (H : S.Core e β) (hS : BlockRationalityField)
    (a : S.cmpt β) (L : (Hc S β).P.Tup) : ActRat (Hc S β) e a L := by
  intro γ _ Q hQ
  obtain ⟨κ, hκ⟩ := (H.toHyp hS).away a γ
  obtain ⟨r, -, hr⟩ := H.chi a γ κ hκ
  have hχ : algebraMap G.O G.Kf (((Hc S β).lev a).χ γ : G.O) = e r⁻¹ := by
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hr
  refine ⟨r⁻¹ • natActR (Hc S β).P D.what₂.LL (blkLL (S.loc β) (sigD D) (tEL D) S.pos ((S.loc β).gamI a γ)) Q, ?_, ?_⟩
  · rw [mapE_smul, map_natActR]
    exact Submodule.smul_mem _ _ (natActR_VtupR (Hc S β).P G.Kf _ _ hQ)
  · rw [mapE_smul, ← actX_map (S.loc β) (tEL D) S.pos e H.actB H.pos_emb a γ Q, ← hχ, algebraMap_smul]

theorem actRatOf_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : ActRatOf S e :=
  fun hS H _ β rep _ c => actRat_of_core (H β) hS (rep c).1 (rep c).2

def ValLiftOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c,
    ∃ Φ : YInv (Hc S β) e (rep c).1 (rep c).2 →+ FiBc S β c,
      ∀ (k : ℕ) (Q : Fin k → YInv (Hc S β) e (rep c).1 (rep c).2), LinearIndependent D.what₂.LL Q → LinearIndependent ℂ (Φ ∘ Q)

theorem invLeOf_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hR : ActRatOf S e) (hV : ValLiftOf S e) : InvLeOf S e := by
  intro hS H X β rep hok c
  have h2 := hR hS H X β rep hok c
  obtain ⟨Φ, hΦ⟩ := hV hS H X β rep hok c
  have : FiniteDimensional ℂ (FiBc S β c) := by
    have := finDim_FiB S β (c.2 ▸ chOf_mem S c.1)
    exact Module.Finite.map _ _
  let Yc := YInv (Hc S β) e (rep c).1 (rep c).2
  refine finrank_le_transfer e ((MvPolynomial.map e).toAddMonoidHom.comp Yc.subtype.toAddMonoidHom)
    (fun r Q => map_smul_e (Hc S β) e r Q.1) Φ hΦ _ ?_
  refine (inv_le_span (Hc S β) e (isLatTup_of_repOk hok c) (spanRat_holds (Hc S β) e) h2).trans (Submodule.span_mono ?_)
  rintro _ ⟨Q, hQ, rfl⟩
  exact ⟨⟨Q, hQ⟩, rfl⟩

theorem invLeOf_of_lift (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ValLiftOf S e) : InvLeOf S e :=
  invLeOf_of S e (actRatOf_holds S e) hV

def InvVal (S : StepIn M i hi G) (β : S.Ch) (c : {c // S.chOf c = β}) : Set (Formalism.L2.Forms.Frames (gramC (gramN D i hi) (embT D)) → ℂ) :=
  {v | v ∈ ValC (gramC (gramN D i hi) (embT D)) (lamTG M i) ∧
    ∀ γ : GL (Fin (D.R.N i)) D.host.E, γ ∈ Formalism.UG.UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → ∀ κ : (S.K β).lev.U,
      ((S.K β).y c).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * ((S.K β).y c).1 * κ.1 →
      ∀ y y' : Formalism.L2.Forms.Frames (gramC (gramN D i hi) (embT D)), IsTr (atInf (embT D) γ) y' y → v y = ((S.K β).lev.chi κ : ℂ) * v y'}

def FormsOnClassOf (S : StepIn M i hi G) : Prop :=
  ∀ β (c : {c // S.chOf c = β}) v, v ∈ InvVal S β c → v ∈ FiBc S β c

def CmpLiftOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c,
    ∃ Φ : YInv (Hc S β) e (rep c).1 (rep c).2 →+ (Formalism.L2.Forms.Frames (gramC (gramN D i hi) (embT D)) → ℂ), (∀ Q, Φ Q ∈ InvVal S β c) ∧
      ∀ (k : ℕ) (Q : Fin k → YInv (Hc S β) e (rep c).1 (rep c).2), LinearIndependent D.what₂.LL Q → LinearIndependent ℂ (Φ ∘ Q)

theorem valLiftOf_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (h1 : FormsOnClassOf S) (h2 : CmpLiftOf S e) :
    ValLiftOf S e := by
  intro hS H X β rep hok c
  obtain ⟨Φ, hΦ, hind⟩ := h2 hS H X β rep hok c
  refine ⟨(Φ.codRestrict (FiBc S β c).toAddSubgroup fun Q => h1 β c _ (hΦ Q)), fun k Q hQ => ?_⟩
  exact LinearIndependent.of_comp (FiBc S β c).subtype (hind k Q hQ)

theorem chartRankGe_of_lift [IsFractionRing G.O G.Kf] (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β)
    (hS : BlockRationalityField) (X : KAat.ChX S) (hV : ValLiftOf S e) : ChartRankGe S :=
  chartRankGe_of S e H hS X (invLeOf_of_lift S e hV)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

theorem cmpJHyp_of_lift (c : LatCmp D) {I : CmpJIn Tw u μ w h Lv} (Gt : GatTies D) (hS : BlockRationalityField)
    (core : ∀ j hj β, (I.at' j hj).st.Core (c.embW u w h) β) (ok : ∀ j hj, (I.at' j hj).st.okW w)
    (twUnit : ∀ j hj β, (I.at' j hj).st.TwUnit w β) (valIntN : ∀ j hj, (I.at' j hj).st.ValIntN (c.embW u w h) w)
    (iwF : ∀ j hj β, (I.at' j hj).st.IwF β) (hfin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses)
    (X : ∀ j hj, KAat.ChX (I.at' j hj).st) (hV : ∀ j hj, ValLiftOf (I.at' j hj).st (c.embW u w h)) : CmpJHyp c I :=
  cmpJHyp_of_ge c Gt hS core ok twUnit valIntN iwF hfin fun j hj => by
    have : IsFractionRing (gatJ Lv (j + 1)).O (gatJ Lv (j + 1)).Kf := ((D.gat u w h).P.setting (plc Gt u w h)).frac_O
    exact chartRankGe_of_lift _ _ (core j hj) hS (X j hj) (hV j hj)

theorem cmpJHyp_of_two (c : LatCmp D) {I : CmpJIn Tw u μ w h Lv} (Gt : GatTies D) (hS : BlockRationalityField)
    (core : ∀ j hj β, (I.at' j hj).st.Core (c.embW u w h) β) (ok : ∀ j hj, (I.at' j hj).st.okW w)
    (twUnit : ∀ j hj β, (I.at' j hj).st.TwUnit w β) (valIntN : ∀ j hj, (I.at' j hj).st.ValIntN (c.embW u w h) w)
    (iwF : ∀ j hj β, (I.at' j hj).st.IwF β) (hfin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses)
    (X : ∀ j hj, KAat.ChX (I.at' j hj).st) (h1 : ∀ j hj, FormsOnClassOf (I.at' j hj).st)
    (h2 : ∀ j hj, CmpLiftOf (I.at' j hj).st (c.embW u w h)) : CmpJHyp c I :=
  cmpJHyp_of_lift c Gt hS core ok twUnit valIntN iwF hfin X fun j hj => valLiftOf_of _ _ (h1 j hj) (h2 j hj)

end Card

end GlobalTheory.HP
end

section

namespace GlobalTheory.HP
open Formalism Formalism.MainNotions Formalism.MainNotions.G

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem isTr_inv_mul (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (γ1 γ2 : GL (Fin n) E)
    (h1 : γ1 ∈ UJ (σ : E →+* E) J) (h2 : γ2 ∈ UJ (σ : E →+* E) J) (z : Formalism.L2.Forms.Frames (gramC J emb)) :
    IsTr (atInf emb ((γ1⁻¹ * γ2 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
      (frameTranslate emb hc γ2⁻¹ ((UJ _ _).inv_mem h2) z) (frameTranslate emb hc γ1⁻¹ ((UJ _ _).inv_mem h1) z) := by
  intro τ
  show atInf emb ((γ1⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ =
    atInf emb ((γ1⁻¹ * γ2 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ *
      (atInf emb ((γ2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ)
  rw [← Matrix.mul_assoc]
  congr 1
  simp only [atInf]
  rw [← Matrix.map_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]

def LawAt (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) : Prop :=
  ∀ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 →
    ∀ y y' : Formalism.L2.Forms.Frames (gramC J emb), IsTr (atInf emb γ) y' y → v y = (S.chi κ : ℂ) * v y'

theorem law_wd (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) (hv : LawAt S emb y0 v)
    (γ1 γ2 : GL (Fin n) E) (h1 : γ1 ∈ UJ (σ : E →+* E) J) (h2 : γ2 ∈ UJ (σ : E →+* E) J) (κ1 κ2 : S.U)
    (e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2 * y0.1 * κ2.1) (z : Formalism.L2.Forms.Frames (gramC J emb)) :
    (S.chi κ1 : ℂ) * v (frameTranslate emb hc γ1⁻¹ ((UJ _ _).inv_mem h1) z) =
      (S.chi κ2 : ℂ) * v (frameTranslate emb hc γ2⁻¹ ((UJ _ _).inv_mem h2) z) := by
  have e0 : y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ1⁻¹ * γ2) * y0.1 * (κ2 * κ1⁻¹ : S.U).1 := by
    have e' : y0.1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1)⁻¹ *
        (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1) * κ1.1⁻¹ := by group
    rw [e] at e'
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    calc y0.1 = _ := e'
      _ = _ := by group
  rw [hv (γ1⁻¹ * γ2) ((UJ _ _).mul_mem ((UJ _ _).inv_mem h1) h2) (κ2 * κ1⁻¹) e0 _ _ (isTr_inv_mul emb hc γ1 γ2 h1 h2 z),
    map_mul, map_inv, Units.val_mul, ← mul_assoc, ← mul_assoc, mul_comm (S.chi κ1 : ℂ), mul_assoc (S.chi κ2 : ℂ), mul_comm ((S.chi κ1 : ℂˣ) : ℂ),
    Units.inv_mul, mul_one]

open Classical in

theorem exists_form_of_law (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (lam : ι → DomWeight n) (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ)
    (hV : v ∈ ValC (gramC J emb) lam) (hv : LawAt S emb y0 v) : ∃ g ∈ AdForms S emb lam, g y0 = v := by
  let Pd : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Prop := fun x =>
    ∃ q : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U, x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) q.1.1 * y0.1 * q.2.1
  let g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Formalism.L2.Forms.Frames (gramC J emb) → ℂ := fun x y =>
    if h : Pd x then (S.chi h.choose.2 : ℂ) * v (frameTranslate emb hc h.choose.1.1⁻¹ ((UJ _ _).inv_mem h.choose.1.2) y) else 0
  have gval : ∀ x (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (κ : S.U),
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 → ∀ y,
      g x y = (S.chi κ : ℂ) * v (frameTranslate emb hc γ⁻¹ ((UJ _ _).inv_mem hγ) y) := by
    intro x γ hγ κ e y
    have h : Pd x := ⟨(⟨γ, hγ⟩, κ), e⟩
    show (if h : Pd x then (S.chi h.choose.2 : ℂ) * v (frameTranslate emb hc h.choose.1.1⁻¹ ((UJ _ _).inv_mem h.choose.1.2) y) else 0) = _
    rw [dif_pos h]
    exact law_wd S emb hc y0 v hv _ _ h.choose.1.2 hγ _ _ (h.choose_spec.symm.trans e) y
  have gzero : ∀ x, ¬ Pd x → ∀ y, g x y = 0 := by
    intro x h y
    show (if h : Pd x then (S.chi h.choose.2 : ℂ) * v (frameTranslate emb hc h.choose.1.1⁻¹ ((UJ _ _).inv_mem h.choose.1.2) y) else 0) = _
    rw [dif_neg h]
  refine ⟨g, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · intro γ' hγ' x x' κ' hx' y y' hy
    by_cases hP : Pd x
    · obtain ⟨⟨⟨γ, hγ⟩, κ⟩, e⟩ := hP
      have e' : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ' * γ) * y0.1 * (κ * κ' : S.U).1 := by
        rw [hx', e, map_mul, Subgroup.coe_mul]; group
      rw [gval x γ hγ κ e, gval x' (γ' * γ) ((UJ _ _).mul_mem hγ' hγ) (κ * κ') e']
      have hfr : frameTranslate emb hc (γ' * γ)⁻¹ ((UJ _ _).inv_mem ((UJ _ _).mul_mem hγ' hγ)) y =
          frameTranslate emb hc γ⁻¹ ((UJ _ _).inv_mem hγ) y' := by
        apply Subtype.ext
        funext τ
        show atInf emb (((γ' * γ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ =
          atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y'.1 τ
        rw [hy τ, _root_.mul_inv_rev]
        simp only [atInf, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
        congr 1
        rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
      rw [hfr, map_mul, Units.val_mul]
      ring
    · have hP' : ¬ Pd x' := by
        rintro ⟨⟨⟨γ, hγ⟩, κ⟩, e⟩
        refine hP ⟨(⟨γ'⁻¹ * γ, (UJ _ _).mul_mem ((UJ _ _).inv_mem hγ') hγ⟩, κ * κ'⁻¹), ?_⟩
        show x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ'⁻¹ * γ) * y0.1 * (κ * κ'⁻¹ : S.U).1
        have e1 : x.1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ')⁻¹ * x'.1 * κ'.1⁻¹ := by
          rw [hx']; group
        rw [e1, e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [gzero x hP, gzero x' hP', mul_zero]
  · refine Submodule.mem_pi.2 fun x _ => ?_
    by_cases hP : Pd x
    · obtain ⟨⟨⟨γ, hγ⟩, κ⟩, e⟩ := hP
      have : g x = (S.chi κ : ℂ) • fun y => v (frameTranslate emb hc γ⁻¹ ((UJ _ _).inv_mem hγ) y) := by
        funext y
        exact gval x γ hγ κ e y
      rw [this]
      exact Submodule.smul_mem _ _ (valuation_class_translate_mem emb hc lam _ _ hV)
    · have : g x = 0 := by
        funext y
        exact gzero x hP y
      rw [this]
      exact Submodule.zero_mem _
  · funext y
    rw [gval y0 1 (UJ _ _).one_mem 1 (by rw [map_one]; simp)]
    have hfr : frameTranslate emb hc (1 : GL (Fin n) E)⁻¹ ((UJ _ _).inv_mem (UJ (σ : E →+* E) J).one_mem) y = y := by
      apply Subtype.ext
      funext τ
      show atInf emb (((1 : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ = y.1 τ
      rw [inv_one]
      simp [atInf]
    rw [hfr, map_one, Units.val_one, one_mul]

end Gen

open Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard GlobalTheory.HP GlobalTheory.HP

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem formsOnClassOf (S : StepIn M i hi G) : FormsOnClassOf S := by
  intro β c v hv
  obtain ⟨g, hg, e⟩ := exists_form_of_law (S.K β).lev (embT D) (embedding_conj_compat D) (lamTG M i) ((S.K β).y c) v hv.1 hv.2
  exact Submodule.mem_map.2 ⟨res (embT D) (S.K β).y g, Submodule.mem_map.2 ⟨g, hg, rfl⟩, e⟩

end GlobalTheory.HP
end

section

namespace GlobalTheory.HP
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms MvPolynomial NumberField IsDedekindDomain

section Tr

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem foNat_anti (lam : DomWeight n) : Antitone lam.natW := by
  intro a b hab
  have := lam.anti hab
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by omega)

theorem foRow_delSq (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ) {q : MvPolynomial (Fin n × Fin n) ℂ}
    (hq : q ∈ delSq ℂ n lam) : Formalism.GradedWeylDivisibility.rowAct ℂ g q ∈ delSq ℂ n lam := by
  unfold delSq at hq ⊢
  rw [Formalism.L2.G.Model.sw_weyl_eq ℂ n n le_rfl _ (foNat_anti lam)] at hq ⊢
  exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ g q hq

def foTr {Gm : ι → Matrix (Fin n) (Fin n) ℂ} (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det)
    (y : Formalism.L2.Forms.Frames Gm) : Formalism.L2.Forms.Frames Gm :=
  (⟨fun τ => g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hg τ).mul (y.2 τ)⟩ :
    {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det})

def blockRowSubstitutionAlgHom (g : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  aeval fun x => ∑ c : Fin n, C (g x.1 x.2.1 c) * X (x.1, c, x.2.2)

theorem blockRowSubstitution_X (g : ι → Matrix (Fin n) (Fin n) ℂ) (x : ι × Fin n × Fin n) :
    blockRowSubstitutionAlgHom g (X x) = ∑ c : Fin n, C (g x.1 x.2.1 c) * X (x.1, c, x.2.2) := by
  simp only [blockRowSubstitutionAlgHom, aeval_X]

theorem eval_blockRowSubstitution (g : ι → Matrix (Fin n) (Fin n) ℂ) (z : ι × Fin n × Fin n → ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    eval z (blockRowSubstitutionAlgHom g P) = eval (fun x => ∑ c, g x.1 x.2.1 c * z (x.1, c, x.2.2)) P := by
  induction P using MvPolynomial.induction_on
  next a => simp [blockRowSubstitutionAlgHom]
  next p q hp hq => simp only [map_add, hp, hq]
  next p x hp => simp only [map_mul, hp, blockRowSubstitution_X, eval_X, map_sum, eval_C]

theorem blockRowSubstitution_rename (g : ι → Matrix (Fin n) (Fin n) ℂ) (τ : ι) (q : MvPolynomial (Fin n × Fin n) ℂ) :
    blockRowSubstitutionAlgHom g (rename (Prod.mk τ) q) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) q) := by
  have h : (blockRowSubstitutionAlgHom g).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (r := n) (n := n) (g τ)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [blockRowSubstitutionAlgHom, Formalism.GradedWeylDivisibility.rowAct, rename_X, map_sum]
  exact congrArg (fun φ => φ q) h

theorem blockRowSubstitution_tensor (g : ι → Matrix (Fin n) (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    blockRowSubstitutionAlgHom g (ten f) = ten fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) (f τ) := by
  simp only [ten, map_prod, blockRowSubstitution_rename]

theorem blockRowSubstitution_preserves_complexSpan (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) ℂ) {P : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hP : P ∈ CSpan lam) : blockRowSubstitutionAlgHom g P ∈ CSpan lam := by
  have h : CSpan lam ≤ (CSpan lam).comap (blockRowSubstitutionAlgHom g).toLinearMap := by
    unfold CSpan
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact Submodule.subset_span ⟨fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) (f τ), fun τ => foRow_delSq _ _ (hf τ), blockRowSubstitution_tensor g f⟩
  exact h hP

theorem foValC_tr {Gm : ι → Matrix (Fin n) (Fin n) ℂ} (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ τ, IsUnit (g τ).det) {v : Formalism.L2.Forms.Frames Gm → ℂ} (hv : v ∈ ValC Gm lam) :
    (fun y => v (foTr g hg y)) ∈ ValC Gm lam := by
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.1 hv
  have h : (fun y => fnOf Gm (shiftOf lam) 1 P (foTr g hg y)) =
      (∏ τ, (g τ).det ^ shiftOf lam τ) • fnOf Gm (shiftOf lam) 1 (blockRowSubstitutionAlgHom g P) := by
    funext y
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, foTr, Pi.one_apply, Matrix.one_mul, eval_blockRowSubstitution,
      Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
    simp only [Matrix.mul_apply]
    ring
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (blockRowSubstitution_preserves_complexSpan lam g hP))

end Tr

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T fT : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem foInf_unit (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) : IsUnit (atInf emb γ.1 τ).det := by
  have h := ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).map (emb τ)
  rwa [RingHom.map_det] at h

theorem foInf_mul (emb : ι → E →+* ℂ) (a b : Matrix (Fin n) (Fin n) E) (τ : ι) :
    atInf emb (a * b) τ = atInf emb a τ * atInf emb b τ := by
  simp [atInf, Matrix.map_mul]

theorem foInf_one (emb : ι → E →+* ℂ) (τ : ι) : atInf emb (1 : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp [atInf]

def foTrR (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (y : Formalism.L2.Forms.Frames (gramC J emb)) : Formalism.L2.Forms.Frames (gramC J emb) :=
  foTr (atInf emb γ.1) (foInf_unit emb γ) y

theorem foTrR_val (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (y : Formalism.L2.Forms.Frames (gramC J emb)) (τ : ι) :
    (foTrR emb γ y).1 τ = atInf emb γ.1 τ * y.1 τ := rfl

theorem foTrR_mul (emb : ι → E →+* ℂ) (γ δ : GL (Fin n) E) (y : Formalism.L2.Forms.Frames (gramC J emb)) :
    foTrR emb (γ * δ) y = foTrR emb γ (foTrR emb δ y) := by
  apply Subtype.ext
  funext τ
  show (foTrR emb (γ * δ) y).1 τ = (foTrR emb γ (foTrR emb δ y)).1 τ
  rw [foTrR_val, foTrR_val, foTrR_val, Units.val_mul, foInf_mul, Matrix.mul_assoc]

theorem foTrR_one (emb : ι → E →+* ℂ) (y : Formalism.L2.Forms.Frames (gramC J emb)) : foTrR emb 1 y = y := by
  apply Subtype.ext
  funext τ
  show (foTrR emb 1 y).1 τ = y.1 τ
  rw [foTrR_val, Units.val_one, foInf_one, Matrix.one_mul]

theorem foIsTr_iff (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (y' y : Formalism.L2.Forms.Frames (gramC J emb)) :
    IsTr (atInf emb γ) y' y ↔ y = foTrR emb γ y' := by
  constructor
  · intro h
    apply Subtype.ext
    funext τ
    exact h τ
  · intro h τ
    rw [h]
    rfl

def FoInv (S : StepLevel F E σ J T fT bad) (emb : ι → E →+* ℂ) (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) : Prop :=
  ∀ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 →
    ∀ y y' : Formalism.L2.Forms.Frames (gramC J emb), IsTr (atInf emb γ) y' y → v y = (S.chi κ : ℂ) * v y'

variable (S : StepLevel F E σ J T fT bad) (emb : ι → E →+* ℂ)

open Classical in

def foForm (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) :
    UPts σ J (FiniteAdeleRing (𝓞 F) F) → Formalism.L2.Forms.Frames (gramC J emb) → ℂ := fun x =>
  if h : ∃ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J ∧ ∃ κ : S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 then
    fun y => (S.chi h.choose_spec.2.choose : ℂ) * v (foTrR emb h.choose⁻¹ y)
  else 0

variable {S emb}

end Adelic

section Rec

open Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard GlobalTheory.HP GlobalTheory.HP

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

end Rec

section Card

open Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard GlobalTheory.HP GlobalTheory.HP

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end GlobalTheory.HP
end

section
open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms
namespace GlobalTheory.HP
open Formalism Formalism.L2 Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.G.RelativeIndexFlags.Core

theorem nuOf_anti_ev {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (nuOf lam) := by
  intro i j hij
  unfold nuOf
  exact Int.toNat_le_toNat (by have := h hij; omega)

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem vsp_le (v : Fin P.nV) :
    Vsp ℂ (P.lam0 v) ≤ Submodule.span ℂ {Y | ∃ f : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
      (∀ s, f s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
        Y = ∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f s))} := by
  let T : Fin (P.n' v) → Set (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℂ) := fun s =>
    (fun f => map (Int.castRingHom ℂ) f) '' (weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s)) :
      Set (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ))
  have hM : ∀ s F, F ∈ (if Antitone (lamAt (P.lam0 v) s) then
      dualWeyl ℂ (P.m + 1) (P.m + 1) (nuOf (lamAt (P.lam0 v) s)) else ⊥) → F ∈ Submodule.span ℂ (T s) := by
    intro s F hF
    have ha := lamAt_anti (P.lam0 v) (P.dom v) s
    rw [if_pos ha, ← Formalism.L2.G.Model.sw_weyl_eq ℂ (P.m + 1) (P.m + 1) le_rfl _ (nuOf_anti_ev ha),
      weyl_eq_span_int] at hF
    exact hF
  have hP := prodSpan (O := ℂ) (I := Fin (P.n' v)) (B := fun _ => MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℂ)
    (fun s => (blockEmb ℂ (S := Fin (P.n' v)) (k := P.m + 1) (n := P.m + 1) s).toLinearMap) T
  unfold Vsp tensorLat
  refine (Submodule.span_mono ?_).trans (hP.le.trans (Submodule.span_mono ?_))
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun s => hM s _ (hF s), rfl⟩
  · rintro _ ⟨F, hF, rfl⟩
    choose f hf hfe using fun s => (Set.mem_image _ _ _).1 (hF s)
    exact ⟨f, hf, Finset.prod_congr rfl fun s _ => by rw [← hfe s]; rfl⟩

theorem vtup_le : VtupR P ℂ ≤ Submodule.span ℂ {X | ∃ f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
    (∀ v s, f v s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
      X = ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f v s)))} := by
  let T : ∀ v : Fin P.nV, Set (MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) ℂ) := fun v =>
    {Y | ∃ f : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
      (∀ s, f s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
        Y = ∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f s))}
  have hP := prodSpan (O := ℂ) (I := Fin P.nV)
    (B := fun v => MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) ℂ)
    (fun v => (rename (R := ℂ) (fun x : Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1)) => (⟨v, x⟩ : Var P))).toLinearMap) T
  unfold VtupR
  refine (Submodule.span_mono ?_).trans (hP.le.trans (Submodule.span_mono ?_))
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun v => vsp_le P v (hF v), rfl⟩
  · rintro _ ⟨F, hF, rfl⟩
    have hF' : ∀ v, ∃ f : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
        (∀ s, f s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
          F v = ∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f s)) := hF
    choose f hf hfe using hF'
    exact ⟨f, hf, Finset.prod_congr rfl fun v _ => by rw [hfe v]; rfl⟩

variable {Tau : Type} [Fintype Tau] (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau)

theorem blockRowSubstitution_one (v : Fin P.nV) (s : Fin (P.n' v)) (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) :
    map (RingHom.id ℂ) (bl P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) v s f) = map (Int.castRingHom ℂ) f := by
  have hn : nAt P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) v s = 1 := by
    unfold nAt; split_ifs <;> simp
  have hi : niAt P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) v s = 1 := by
    unfold niAt; split_ifs <;> simp
  unfold bl
  rw [hn, hi, Matrix.det_one, _root_.one_zpow, one_smul, rowAct_one, MvPolynomial.map_id]

theorem gen_mem (G : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (M : Tau → GL (Fin (P.m + 1)) ℂ)
    (lam : Tau → DomWeight (P.m + 1)) (hw : WtTie P rfl pos lam)
    (f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ)
    (hf : ∀ v s, f v s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) :
    evC P rfl pos G (fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ))
      (∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f v s)))) ∈ ValC G lam := by
  choose ft hft hev using fun x : Σ v : Fin P.nV, Fin (P.n' v) =>
    (blk_ev P pos lam M (fun _ => 1) (RingHom.id ℂ) (fun m l _ => oddFact_pf ℤ m l) hw x).1 (f x.1 x.2) (hf x.1 x.2)
  have hX : (∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f v s)))) =
      map (RingHom.id ℂ) (gen P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) f) := by
    rw [map_gen]
    simp only [blockRowSubstitution_one]
  have hM : (fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)) = mcOf M (RingHom.id ℂ) := by
    funext τ; ext a b; rfl
  have key : evC P rfl pos G (mcOf M (RingHom.id ℂ)) (map (RingHom.id ℂ) (gen P rfl pos (fun _ => 1) f)) =
      fnOf G (shiftOf lam) (kcOf M (fun _ => 1) (RingHom.id ℂ))
        (ten fun τ => map (Int.castRingHom ℂ) (ft (pos.symm τ))) := by
    funext z
    refine evC_gen P pos lam M (fun _ => 1) (RingHom.id ℂ) G f (fun τ => ft (pos.symm τ)) (fun x => ?_) z
    show BlockRealisation P pos lam M (fun _ => 1) (RingHom.id ℂ) x (f x.1 x.2) (ft (pos.symm (pos x)))
    rw [pos.symm_apply_apply]
    exact hev x
  have hK : kcOf M (fun _ => 1) (RingHom.id ℂ) = fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) := by
    funext τ; ext a b; simp [kcOf]
  have hP : ten (fun τ => map (Int.castRingHom ℂ) (ft (pos.symm τ))) ∈ CSpan lam := by
    refine Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩
    have h1 := hft (pos.symm τ)
    rw [pos.apply_symm_apply] at h1
    unfold delSq at h1 ⊢
    exact map_mem_weyl le_rfl _ _ h1
  have h0 : fnOf G (shiftOf lam) 1 (ten fun τ => map (Int.castRingHom ℂ) (ft (pos.symm τ))) ∈ ValC G lam :=
    Submodule.mem_map_of_mem hP
  have hu : ∀ τ, IsUnit ((M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)).det := fun τ =>
    (Matrix.isUnit_iff_isUnit_det _).1 (M τ).isUnit
  have h1 := GlobalTheory.HP.foValC_tr lam (fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)) hu h0
  rw [hX, hM, key, hK]
  convert h1 using 1
  funext z
  simp only [fnOf, GlobalTheory.HP.foTr, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul]

end Gen

section Main

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ}

theorem evC_le (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (M : Tau → GL (Fin n) ℂ) (lam : Tau → DomWeight n) (hw : WtTie P h pos lam) :
    ∀ Q ∈ VtupR P ℂ, evC P h pos G (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) Q ∈ ValC G lam := by
  subst h
  intro Q hQ
  have hS := vtup_le P hQ
  clear hQ
  induction hS using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨f, hf, rfl⟩ := hX
    exact gen_mem P pos G M lam hw f hf
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end Main

end GlobalTheory.HP
end

section

namespace GlobalTheory.HP
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard GlobalTheory.HP GlobalTheory.HP GlobalTheory.HP

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

def trN (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (γ0 : GL (Fin (D.R.N i)) D.host.E) :
    (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) →ₗ[ℂ]
      (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) where
  toFun h := fun z => (detF (cTw D i) z)⁻¹ * h (foTrR (embT D) γ0 z)
  map_add' h h' := by funext z; simp only [Pi.add_apply]; ring
  map_smul' a h := by funext z; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem trN_inj (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (γ0 : GL (Fin (D.R.N i)) D.host.E) :
    LinearMap.ker (trN D i hi γ0) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun h hh => ?_
  funext z
  have h1 := congrFun hh (foTrR (embT D) γ0⁻¹ z)
  have h2 : foTrR (embT D) γ0 (foTrR (embT D) γ0⁻¹ z) = z := by
    rw [← foTrR_mul, mul_inv_cancel, foTrR_one]
  change (detF (cTw D i) _)⁻¹ * h (foTrR (embT D) γ0 (foTrR (embT D) γ0⁻¹ z)) = 0 at h1
  rw [h2] at h1
  exact (mul_eq_zero.1 h1).resolve_left (inv_ne_zero (detF_ne _ _))

def phiC (S : StepIn M i hi G) (β : S.Ch) (γ0 : GL (Fin (D.R.N i)) D.host.E) :
    XR (Hc S β).P ℂ →ₗ[ℂ] (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) :=
  (trN D i hi γ0).comp
    (evC (Hc S β).P (S.loc β).rk S.pos (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B))

theorem ker_phiC (S : StepIn M i hi G) (β : S.Ch) (γ0 : GL (Fin (D.R.N i)) D.host.E) : LinearMap.ker (phiC S β γ0) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun Q hQ => ?_
  have h1 : evC (Hc S β).P (S.loc β).rk S.pos (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B) Q = 0 :=
    LinearMap.ker_eq_bot'.1 (trN_inj D i hi γ0) _ hQ
  exact evInj_pf (J := gramN D i hi) (embT D) (Hc S β) (S.loc β) S.pos Q h1

def VtupDesc (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  ∀ β (Q : YR (Hc S β) D.what₂.LL), MvPolynomial.map e Q ∈ (Hc S β).P.Vtup → MvPolynomial.map D.what₂.embLL Q ∈ VtupR (Hc S β).P ℂ

def EvValLe (S : StepIn M i hi G) (β : S.Ch) : Prop :=
  ∀ Q ∈ VtupR (Hc S β).P ℂ,
    evC (Hc S β).P (S.loc β).rk S.pos (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B) Q ∈
      Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (M.lam i)

def CmpInvOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c
    (g : ∀ v, GL (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v)) (γ0 : GL (Fin (D.R.N i)) D.host.E) (κ0 : (S.K β).lev.U),
    γ0 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
    (∀ v, (rep c).2 v = colSpan ((Hc S β).P.W v) (g v : Matrix (Fin ((Hc S β).P.m + 1)) (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v))) →
    (S.loc β).IsPt (rep c).1 g (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * ((S.K β).y c).1 * κ0.1) →
    ∀ Q ∈ YInv (Hc S β) e (rep c).1 (rep c).2,
      FoInv (S.K β).lev (embT D) ((S.K β).y c) (phiC S β γ0 (MvPolynomial.map D.what₂.embLL Q))

theorem phiC_mem_ValC (S : StepIn M i hi G) (β : S.Ch) (hV : EvValLe S β) (γ0 : GL (Fin (D.R.N i)) D.host.E)
    {Q : XR (Hc S β).P ℂ} (hQ : Q ∈ VtupR (Hc S β).P ℂ) :
    phiC S β γ0 Q ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (lamTG M i) := by
  have h1 := foValC_tr (M.lam i) (Formalism.L2.Forms.atInf (embT D) γ0.1) (foInf_unit (embT D) γ0) (hV Q hQ)
  have h2 := (mem_ValC_shW (D.R.N_pos i) (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (M.lam i) (cTw D i) 1 one_ne_zero
    (phiC S β γ0 Q)).2
  refine h2 ?_
  convert h1 using 1
  funext z
  change 1 * detF (cTw D i) z * ((detF (cTw D i) z)⁻¹ * _) = _
  rw [one_mul, ← mul_assoc, mul_inv_cancel₀ (detF_ne _ _), one_mul]
  rfl

theorem cmpLiftOf_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hD : VtupDesc S e) (hV : ∀ β, EvValLe S β)
    (hI : CmpInvOf S e) : CmpLiftOf S e := by
  intro hS H X β rep hok c
  obtain ⟨g, γ0, κ0, hγ0, hL, hpt⟩ := hok c
  let Y := YInv (Hc S β) e (rep c).1 (rep c).2
  let Φ : Y →+ (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) :=
    (phiC S β γ0).toAddMonoidHom.comp ((MvPolynomial.map D.what₂.embLL).toAddMonoidHom.comp Y.subtype.toAddMonoidHom)
  refine ⟨Φ, fun Q => ⟨?_, ?_⟩, fun k Q hQ => ?_⟩
  · exact phiC_mem_ValC S β (hV β) γ0 (hD β Q.1 Q.2.1)
  · exact hI hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q.1 Q.2
  · have a : LinearIndependent D.what₂.LL (fun j => (Q j : YR (Hc S β) D.what₂.LL)) :=
      hQ.map' Y.subtype (Submodule.ker_subtype _)
    have b := Formalism.MainNotions.G.SymmetricFormBlocks.li_map D.what₂.embLL _ a
    exact b.map' (phiC S β γ0) (ker_phiC S β γ0)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end GlobalTheory.HP
end

section

namespace GlobalTheory.HP
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard GlobalTheory.HP GlobalTheory.HP GlobalTheory.HP GlobalTheory.HP

section Desc

variable {LL K : Type} [Field LL] [Field K] (e : LL →+* K)

theorem lin_ext_map {σ : Type} (φ : MvPolynomial σ LL →ₗ[LL] LL) (P : MvPolynomial σ LL) :
    (MvPolynomial.basisMonomials σ K).constr K (fun m : σ →₀ ℕ => e (φ (MvPolynomial.monomial m 1)))
      (MvPolynomial.map e P) = e (φ P) := by
  induction P using MvPolynomial.induction_on'
  next u a =>
    have h1 : MvPolynomial.map e (MvPolynomial.monomial u a) = e a • MvPolynomial.basisMonomials σ K u := by
      simp only [MvPolynomial.map_monomial, MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have h2 : MvPolynomial.monomial u a = a • MvPolynomial.monomial u (1 : LL) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [h1, map_smul, Basis.constr_basis, h2, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  next p q hp hq =>
    simp only [map_add, hp, hq]

theorem desc_span {σ : Type} (V : Submodule LL (MvPolynomial σ LL)) {Q : MvPolynomial σ LL}
    (hQ : MvPolynomial.map e Q ∈ Submodule.span K (MvPolynomial.map e '' (V : Set (MvPolynomial σ LL)))) : Q ∈ V := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  let φK : MvPolynomial σ K →ₗ[K] K :=
    (MvPolynomial.basisMonomials σ K).constr K (fun m : σ →₀ ℕ => e (φ (MvPolynomial.monomial m 1)))
  have h1 : Submodule.span K (MvPolynomial.map e '' (V : Set (MvPolynomial σ LL))) ≤ LinearMap.ker φK := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    change φK (MvPolynomial.map e v) = 0
    rw [lin_ext_map e φ v, (Submodule.mem_dualAnnihilator φ).1 hφ v hv, map_zero]
  have h2 : φK (MvPolynomial.map e Q) = 0 := h1 hQ
  rw [lin_ext_map e φ Q] at h2
  exact (map_eq_zero_iff e e.injective).1 h2

theorem dw_desc {r n : ℕ} (ν : Fin n → ℕ) {f : MvPolynomial (Fin r × Fin n) LL}
    (h : MvPolynomial.map e f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r n ν) : f ∈ Formalism.GradedWeylDivisibility.dualWeyl LL r n ν := by
  rw [Formalism.GradedWeylDivisibility.mem_dualWeyl_iff, isWH_iff] at h ⊢
  refine ⟨MvPolynomial.map_injective e e.injective ?_, fun l j hlj => MvPolynomial.map_injective e e.injective ?_⟩
  · rw [whc_map, h.1]
  · rw [colAddGen_map, MvPolynomial.map_rename, h.2 l j hlj]

theorem dw_span {r n : ℕ} (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl K r n ν ≤
      Submodule.span K (MvPolynomial.map e '' (Formalism.GradedWeylDivisibility.dualWeyl LL r n ν : Set (MvPolynomial (Fin r × Fin n) LL))) := by
  refine (dualWeyl_desc e ν).trans (Submodule.span_mono ?_)
  rintro _ ⟨Q, hQ, rfl⟩
  exact ⟨Q, dw_desc e ν hQ, rfl⟩

theorem span_prod_le {S : Type} [Fintype S] {σ : S → Type} {τ : Type} (f : ∀ s, σ s → τ)
    (Ms : ∀ s, Submodule K (MvPolynomial (σ s) K)) (Ns : ∀ s, Submodule LL (MvPolynomial (σ s) LL))
    (hM : ∀ s, Ms s ≤ Submodule.span K (MvPolynomial.map e '' (Ns s : Set (MvPolynomial (σ s) LL)))) :
    Submodule.span K {Z | ∃ F : ∀ s, MvPolynomial (σ s) K, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} ≤
      Submodule.span K (MvPolynomial.map e '' (Submodule.span LL
        {Z | ∃ F : ∀ s, MvPolynomial (σ s) LL, (∀ s, F s ∈ Ns s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} :
          Set (MvPolynomial τ LL))) := by
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  let A : S → Set (MvPolynomial τ K) := fun s =>
    {y | ∃ Q : MvPolynomial (σ s) LL, Q ∈ Ns s ∧ y = MvPolynomial.rename (f s) (MvPolynomial.map e Q)}
  have hx : ∀ s ∈ Finset.univ, MvPolynomial.rename (f s) (F s) ∈ Submodule.span K (A s) := by
    intro s _
    have h1 := Submodule.mem_map_of_mem (f := (MvPolynomial.rename (R := K) (f s)).toLinearMap) (hM s (hF s))
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨Q, hQ, rfl⟩, rfl⟩
    exact ⟨Q, hQ, rfl⟩
  have h := prod_mem_span Finset.univ A _ hx
  refine Submodule.span_mono ?_ h
  rintro _ ⟨a, ha, rfl⟩
  choose Q hQ hQe using fun s => ha s (Finset.mem_univ s)
  refine ⟨∏ s, MvPolynomial.rename (f s) (Q s), Submodule.subset_span ⟨Q, hQ, rfl⟩, ?_⟩
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hQe s, MvPolynomial.map_rename]

theorem vsp_span {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    Vsp K lam0 ≤ Submodule.span K (MvPolynomial.map e '' (Vsp LL lam0 : Set (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) LL))) := by
  have hM : ∀ s : Fin n', (if Antitone (lamAt lam0 s) then Formalism.GradedWeylDivisibility.dualWeyl K (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥) ≤
      Submodule.span K (MvPolynomial.map e '' (((if Antitone (lamAt lam0 s) then
        Formalism.GradedWeylDivisibility.dualWeyl LL (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥ : Submodule LL _)) : Set (MvPolynomial (Fin (m + 1) × Fin (m + 1)) LL))) := by
    intro s
    split_ifs
    · exact dw_span e _
    · exact bot_le
  exact span_prod_le e (σ := fun _ => Fin (m + 1) × Fin (m + 1)) (fun s v => (s, v)) _ _ hM

theorem vtup_span {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) : VtupR P K ≤ Submodule.span K (MvPolynomial.map e '' (VtupR P LL : Set (XR P LL))) :=
  span_prod_le e (σ := fun v => Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) (fun v x => (⟨v, x⟩ : Var P)) _ _
    fun v => vsp_span e (P.lam0 v)

theorem span_prod_map {S : Type} [Fintype S] {σ : S → Type} {τ : Type} (f : ∀ s, σ s → τ)
    (Ns : ∀ s, Submodule LL (MvPolynomial (σ s) LL)) (Ms : ∀ s, Submodule K (MvPolynomial (σ s) K))
    (h : ∀ s, ∀ x ∈ Ns s, MvPolynomial.map e x ∈ Ms s) {Z : MvPolynomial τ LL}
    (hZ : Z ∈ Submodule.span LL {Z | ∃ F : ∀ s, MvPolynomial (σ s) LL, (∀ s, F s ∈ Ns s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)}) :
    MvPolynomial.map e Z ∈
      Submodule.span K {Z | ∃ F : ∀ s, MvPolynomial (σ s) K, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} := by
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun s => MvPolynomial.map e (F s), fun s => h s _ (hF s), ?_⟩
    simp only [map_prod, MvPolynomial.map_rename]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mapE_smul]; exact Submodule.smul_mem _ _ hx

theorem vsp_map {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) {x : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) LL}
    (hx : x ∈ Vsp LL lam0) : MvPolynomial.map e x ∈ Vsp K lam0 := by
  refine span_prod_map e (σ := fun _ => Fin (m + 1) × Fin (m + 1)) (fun s v => (s, v)) _ _ (fun s y hy => ?_) hx
  split_ifs at hy ⊢
  · exact Formalism.GradedWeylDivisibility.dualWeylMap LL K e _ _ _ y hy
  · rw [(Submodule.mem_bot _).1 hy, map_zero]
    exact Submodule.zero_mem _

theorem vtup_map {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {Q : XR P LL} (hQ : Q ∈ VtupR P LL) : MvPolynomial.map e Q ∈ VtupR P K :=
  span_prod_map e (σ := fun v => Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) (fun v x => (⟨v, x⟩ : Var P)) _ _
    (fun v _ hy => vsp_map e (P.lam0 v) hy) hQ

end Desc

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem vtupDesc_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : VtupDesc S e := by
  intro β Q hQ
  exact vtup_map D.what₂.embLL _ (desc_span e (VtupR (Hc S β).P D.what₂.LL) (vtup_span e (Hc S β).P hQ))

theorem cmpLiftOf_of_two (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) (hI : CmpInvOf S e) :
    CmpLiftOf S e :=
  cmpLiftOf_of S e (vtupDesc_holds S e) hV hI

end Rec

end GlobalTheory.HP
end

section

namespace GlobalTheory.HP
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard GlobalTheory.HP GlobalTheory.HP GlobalTheory.HP GlobalTheory.HP
  GlobalTheory.HP

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T fT : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {S : StepLevel F E σ J T fT bad} {emb : Tau → E →+* ℂ} {c : ℤ}

theorem tw_triv (X : DetTw S emb c) {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {γ : GL (Fin n) E}
    (hγ : γ ∈ UJ (σ : E →+* E) J) {κ : S.U}
    (h : y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1) :
    ∏ τ, (emb τ (γ : Matrix (Fin n) (Fin n) E).det) ^ c = 1 := by
  let xg : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ, ratInU γ hγ⟩
  let xk : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩
  have e1 : xg * y0 * xk = y0 := Subtype.ext h.symm
  have e2 : X.ch xg = 1 := by
    have h3 := congrArg X.ch e1
    rw [map_mul, map_mul, X.ch_U xk κ.2, mul_one] at h3
    exact mul_right_cancel (h3.trans (one_mul _).symm)
  have h4 := X.ch_rat γ hγ xg rfl
  rwa [e2, Units.val_one, one_mul] at h4

theorem detF_tr (γ : GL (Fin n) E) {y y' : Formalism.L2.Forms.Frames (gramC J emb)} (hy : IsTr (atInf emb γ) y' y) :
    detF c y = (∏ τ, (emb τ (γ : Matrix (Fin n) (Fin n) E).det) ^ c) * detF c y' := by
  unfold detF
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hy τ, Matrix.det_mul, mul_zpow]
  congr 2
  simp [atInf, RingHom.map_det]

theorem foInv_twist (X : DetTw S emb c) {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {h : Formalism.L2.Forms.Frames (gramC J emb) → ℂ}
    (hh : FoInv S emb y0 h) : FoInv S emb y0 (fun z => (detF c z)⁻¹ * h z) := by
  intro γ hγ κ hy0 y y' hy
  simp only
  rw [hh γ hγ κ hy0 y y' hy, detF_tr γ hy, tw_triv X hγ hy0, one_mul]
  ring

end Gen

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

def CmpInvRawOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c
    (g : ∀ v, GL (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v)) (γ0 : GL (Fin (D.R.N i)) D.host.E) (κ0 : (S.K β).lev.U),
    γ0 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
    (∀ v, (rep c).2 v = colSpan ((Hc S β).P.W v) (g v : Matrix (Fin ((Hc S β).P.m + 1)) (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v))) →
    (S.loc β).IsPt (rep c).1 g (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * ((S.K β).y c).1 * κ0.1) →
    ∀ Q ∈ YInv (Hc S β) e (rep c).1 (rep c).2,
      FoInv (S.K β).lev (embT D) ((S.K β).y c) (fun z =>
        evC (Hc S β).P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B)
          (MvPolynomial.map D.what₂.embLL Q) (foTrR (embT D) γ0 z))

theorem cmpInvOf_of_raw (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hR : CmpInvRawOf S e) : CmpInvOf S e := by
  intro hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ
  exact foInv_twist (S.tw β) (hR hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ)

theorem cmpLiftOf_of_raw (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) (hR : CmpInvRawOf S e) :
    CmpLiftOf S e :=
  cmpLiftOf_of_two S e hV (cmpInvOf_of_raw S e hR)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end GlobalTheory.HP
end

section

namespace GlobalTheory.HP
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard GlobalTheory.HP GlobalTheory.HP GlobalTheory.HP GlobalTheory.HP
  GlobalTheory.HP GlobalTheory.HP

theorem grp2 {Γ : Type} [Group Γ] (b y k : Γ) (h : y = b * y * k) : b = y * k⁻¹ * y⁻¹ := by
  rw [show y * k⁻¹ * y⁻¹ = (b * y * k) * k⁻¹ * y⁻¹ by rw [← h]]
  group

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

set_option maxHeartbeats 4000000 in

theorem cmpInvRaw_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : CmpInvRawOf S e := by
  intro hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ γ hγ κ hyc y y' hy
  have Hb := H β
  obtain ⟨x, hx⟩ : ∃ x, x = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * ((S.K β).y c).1 * κ0.1 :=
    ⟨_, rfl⟩
  rw [← hx] at hpt
  have hxU : x ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (PStabEq.bc_mem hγ0) ((S.K β).y c).2) (PStabEq.U_le κ0.2)
  have hb : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ =
      ((S.K β).y c).1 * κ.1⁻¹ * ((S.K β).y c).1⁻¹ := grp2 _ _ _ hyc
  have hyU : ((S.K β).y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * ((S.K β).y c).1 ∈
      (S.K β).lev.U := by
    rw [hb, show ((S.K β).y c).1⁻¹ * (((S.K β).y c).1 * κ.1⁻¹ * ((S.K β).y c).1⁻¹) * ((S.K β).y c).1 = κ.1⁻¹ by group]
    exact (S.K β).lev.U.inv_mem κ.2
  have hδU : γ0 * γ * γ0⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ0 hγ) (Subgroup.inv_mem _ hγ0)
  have hδx : x⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ0 * γ * γ0⁻¹) * x ∈ (S.K β).lev.U :=
    PStabEq.conj_mem' x ((S.K β).y c).1 γ0 γ κ0 hx hyU
  obtain ⟨⟨γ', hfix⟩, hγ'⟩ := (PStabEq.stab_bij Hb.good Hb.int Hb.hypP (X.hypC β) Hb.bad_p Hb.actB Hb.gam Hb.gamU (rep c).1
    (X.inj β _) (X.onto β _) (rep c).2 g hL ⟨x, hxU⟩ hpt).2 ⟨γ0 * γ * γ0⁻¹, hδU, hδx⟩
  have hgam : (S.loc β).gamI (rep c).1 γ' = γ0 * γ * γ0⁻¹ := congrArg Subtype.val hγ'
  obtain ⟨κa, hκa⟩ := awayEx_of Hb.good (S.K β).lev Hb.gam (rep c).1 γ'
  obtain ⟨r, hr, hr1⟩ := Hb.chi (rep c).1 γ' κa hκa

  have hN : natActR (Hc S β).P D.what₂.LL (blkLL (S.loc β) (sigD D) (tEL D) S.pos ((S.loc β).gamI (rep c).1 γ')) Q = r • Q := by
    apply MvPolynomial.map_injective e e.injective
    have h1 := hQ.2 γ' hfix
    rw [actX_map (S.loc β) (tEL D) S.pos e Hb.actB Hb.pos_emb (rep c).1 γ' Q] at h1
    have hr1' : algebraMap G.O G.Kf (((Hc S β).lev (rep c).1).χ γ' : G.O) * e r = 1 := hr1
    rw [mapE_smul e r Q, ← h1, ← algebraMap_smul G.Kf (((Hc S β).lev (rep c).1).χ γ' : G.O), smul_smul, mul_comm (e r), hr1',
      one_smul]

  have e1 : x⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ0 * γ * γ0⁻¹) * x =
      κ0.1⁻¹ * κ.1⁻¹ * κ0.1 := by
    rw [hx, map_mul, map_mul, map_inv, hb]
    group
  have ht : ∀ v ∈ S.bad, bc (prV (E := D.host.E) v) (κa * (κ0⁻¹ * κ * κ0)).1 = 1 := by
    intro v hv
    have hvp := Hb.bad_p v hv
    have a1 := hκa.2 v hvp
    have a2 : bc (prV (E := D.host.E) v) ((S.loc β).yG (rep c).1) = bc (prV (E := D.host.E) v) x := (hpt.1 v hvp).symm
    have key : bc (prV (E := D.host.E) v) κa.1 =
        bc (prV (E := D.host.E) v) (x⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ0 * γ * γ0⁻¹) * x) := by
      rw [a1, hgam]
      simp only [map_mul, map_inv, a2]
    have e2 : (κa * (κ0⁻¹ * κ * κ0)).1 = κa.1 * (κ0.1⁻¹ * κ.1 * κ0.1) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e2, map_mul, key, ← map_mul, e1,
      show κ0.1⁻¹ * κ.1⁻¹ * κ0.1 * (κ0.1⁻¹ * κ.1 * κ0.1) = 1 by group, map_one]
  have hc : ((S.K β).lev.chi κa : ℂ) * ((S.K β).lev.chi κ : ℂ) = 1 := by
    have h0 := congrArg (fun w : ℂˣ => (w : ℂ)) ((S.K β).lev.chi_triv _ ht)
    simp only [map_mul, map_inv, Units.val_mul, Units.val_one, Units.val_inv_eq_inv_val] at h0
    have hne : ((S.K β).lev.chi κ0 : ℂ) ≠ 0 := Units.ne_zero _
    field_simp at h0
    linear_combination h0

  have hz : IsTr (atInf (embT D) ((S.loc β).gamI (rep c).1 γ').1) (foTrR (embT D) γ0 y') (foTrR (embT D) γ0 y) := by
    rw [foIsTr_iff, hgam, (foIsTr_iff (embT D) γ y' y).1 hy, ← foTrR_mul, ← foTrR_mul]
    congr 1
    group
  have hE := evC_blk (S.loc β) (tEL D) S.pos (embT D) D.what₂.embLL (tEL_emb D) ((S.loc β).gamI (rep c).1 γ')
    (unit_of_std (S.loc β).B _ Hb.std (Hb.gamU _ γ')) (gramC (gramN D i hi) (embT D)) _ _ hz Q
  rw [hN, Formalism.L2.G.Cmp.map_smul', map_smul, Pi.smul_apply, smul_eq_mul, hr] at hE
  show _ = ((S.K β).lev.chi κ : ℂ) * _
  linear_combination (((S.K β).lev.chi κ : ℂ)) * hE - (evC (Hc S β).P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D))
    (crdB (embT D) (S.loc β).B) (MvPolynomial.map D.what₂.embLL Q) (foTrR (embT D) γ0 y)) * hc

theorem cmpLiftOf_of_evVal (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) : CmpLiftOf S e :=
  cmpLiftOf_of_raw S e hV (cmpInvRaw_holds S e)

def EvValCAt (S : StepIn M i hi G) (β : S.Ch) : Prop :=
  EvValC (Hc S β).P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D)) (atInfGL (embT D) (S.loc β).B⁻¹) (M.lam i)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end GlobalTheory.HP
end

section

namespace GlobalTheory.HP
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard GlobalTheory.HP GlobalTheory.HP GlobalTheory.HP GlobalTheory.HP
  GlobalTheory.HP GlobalTheory.HP GlobalTheory.HP

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem evValLe_of_wt (S : StepIn M i hi G) (β : S.Ch) (hw : WtTie (Hc S β).P (S.loc β).rk S.pos (M.lam i)) :
    EvValLe S β := by
  intro Q hQ
  exact GlobalTheory.HP.evC_le (Hc S β).P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D))
    (atInfGL (embT D) (S.loc β).B⁻¹) (M.lam i) hw Q hQ

theorem cmpLiftOf_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : CmpLiftOf S e := by
  intro hS H X
  exact cmpLiftOf_of_evVal S e (fun β => evValLe_of_wt S β (H β).wt) hS H X

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end GlobalTheory.HP
end

section

namespace GlobalTheory.HP
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PValIntN

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {j : ℕ}
  (hj : j + 1 ≤ D.R.m) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

structure LatTies (w : D.what₂.places.Pl) (Fo : FormsIn M (j + 1) hj) (β : Fo.Ch)
    (Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (j + 1)).rank → D.host.E)) : Prop where
  siteGood_prime_torsion : ¬ D.what₂.places.resChar w ∣ Fo.T
  Lb_eq : (Fo.K β).lev.Lb = reL (rankN D (j + 1) hj) Lb
  lat : ∀ cl : {c // Fo.chOf c = β}, Submodule.IsLattice D.host.E (Fo.lat cl.1)
  chi : ∀ κ : (Fo.K β).lev.U, ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧
    D.what₂.embLL r = ((Fo.K β).lev.chi κ : ℂ)

set_option maxHeartbeats 8000000 in

theorem latIn_of {Fo : FormsIn M (j + 1) hj} {Lc : LocIn X u w hg Lv j Fo.Ch}
    {pos : (Σ v : Fin (Fl.Pj (j + 1)).nV, Fin ((Fl.Pj (j + 1)).n' v)) ≃ D.what₂.Tau} {β : Fo.Ch}
    (hfr : FrRatJ (Lc.t β) Lc.B) (H : LatTies hj w Fo β (Lc.Lb β)) : LatIn (stepInOf hj Fo Lc pos) w β where
  prime := hg.1
  resChar := rfl
  siteGood_prime_torsion := H.siteGood_prime_torsion
  alg := fun v a => (X.g u w hg).spl_alg _ ((X.g u w hg).pl v).2 a
  base := fun v t => frlat_re (rankN D (j + 1) hj) ((X.g u w hg).pl v).1 ((X.g u w hg).spl _ ((X.g u w hg).pl v).2) (Lc.Lb β)
    Lc.B ((Lc.t β).fr _ ((X.g u w hg).pl v).2) (hfr _ _) ((Lc.t β).fr_lat _ ((X.g u w hg).pl v).2) (Fo.K β).lev.Lb H.Lb_eq t
  lat := H.lat
  chi := H.chi

set_option maxHeartbeats 8000000 in

theorem valIntN_rec {Fo : FormsIn M (j + 1) hj} {Lc : LocIn X u w hg Lv j Fo.Ch}
    {pos : (Σ v : Fin (Fl.Pj (j + 1)).nV, Fin ((Fl.Pj (j + 1)).n' v)) ≃ D.what₂.Tau} (e : D.what₂.LL →+* (D.gat u w hg).Kf)
    (HT : ∀ β, LocTies hj Fo Lc pos e β) (hS : BlockRationalityField) (hfrac : IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf)
    (hR0 : ∀ x, x ∈ intW D.what₂.places w ↔ e x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf))
    (HL : ∀ β, LatTies hj w Fo β (Lc.Lb β)) : (stepInOf hj Fo Lc pos).ValIntN e w :=
  valIntN_of (stepInOf hj Fo Lc pos) e w (fun β => core_of hj (HT β)) hS hfrac hR0
    (fun β => latIn_of hj (HT β).frRat (HL β))

end GlobalTheory.HP
end

section

namespace GlobalTheory.HP
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PValIntN
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {p : ℕ} {G : GAtP p}

theorem epsU_val (B B' γ : GL (Fin n) E) (k : ℕ) :
    ((epsU B B' γ k : Eˣ) : E) = (B'.1.det * (B.1.det)⁻¹) ^ k * (γ.1.det)⁻¹ := by
  simp [epsU]

theorem det_cT (τ : E →+* E) (M : Matrix (Fin n) (Fin n) E) : (cT τ M).det = τ M.det := by
  unfold cT
  rw [Matrix.det_transpose]
  exact (RingHom.map_det τ M).symm

theorem epsU_conj (hJ : IsUnit J.det) (B B' γ : GL (Fin n) E) (k : ℕ) (hγ : γ ∈ UJ (σ : E →+* E) J)
    (hB : cT (σ : E →+* E) B.1 * J * B.1 = 1) :
    σ (epsU B B' γ k : Eˣ) * (epsU B B' γ k : Eˣ) = ((cT (σ : E →+* E) B'.1 * J * B'.1).det) ^ k := by
  have hJ0 : J.det ≠ 0 := hJ.ne_zero
  have h1 : σ γ.1.det * γ.1.det = 1 := by
    have h := congrArg Matrix.det (show cT (σ : E →+* E) γ.1 * J * γ.1 = J from hγ)
    rw [Matrix.det_mul, Matrix.det_mul, det_cT] at h
    have h' : (σ γ.1.det * γ.1.det) * J.det = 1 * J.det := by
      rw [one_mul]
      calc (σ γ.1.det * γ.1.det) * J.det = (σ : E →+* E) γ.1.det * J.det * γ.1.det := by
            show (σ γ.1.det * γ.1.det) * J.det = σ γ.1.det * J.det * γ.1.det
            ring
        _ = J.det := h
    exact mul_right_cancel₀ hJ0 h'
  have h2 : σ B.1.det * B.1.det = (J.det)⁻¹ := by
    have h := congrArg Matrix.det hB
    rw [Matrix.det_mul, Matrix.det_mul, det_cT, Matrix.det_one] at h
    refine eq_inv_of_mul_eq_one_left ?_
    calc σ B.1.det * B.1.det * J.det = (σ : E →+* E) B.1.det * J.det * B.1.det := by
          show σ B.1.det * B.1.det * J.det = σ B.1.det * J.det * B.1.det
          ring
      _ = 1 := h
  have h3 : (cT (σ : E →+* E) B'.1 * J * B'.1).det = σ B'.1.det * B'.1.det * J.det := by
    rw [Matrix.det_mul, Matrix.det_mul, det_cT]
    show σ B'.1.det * J.det * B'.1.det = _
    ring
  rw [epsU_val, h3]
  calc σ ((B'.1.det * (B.1.det)⁻¹) ^ k * (γ.1.det)⁻¹) * ((B'.1.det * (B.1.det)⁻¹) ^ k * (γ.1.det)⁻¹)
      = ((σ B'.1.det * B'.1.det) * (σ B.1.det * B.1.det)⁻¹) ^ k * (σ γ.1.det * γ.1.det)⁻¹ := by
        simp only [map_mul, map_pow, map_inv₀, mul_pow, mul_inv]
        ring
    _ = _ := by rw [h1, h2, inv_inv, inv_one, mul_one]

set_option maxHeartbeats 2000000 in

theorem epsU_iw (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (hW : LocInt A) (hp : p.Prime) (hT : ¬ p ∣ T)
    (halg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a))
    (hb : ∀ v (t : Fin n → (A.pl v).1.adicCompletion F),
      (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 S.Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
      ∀ a, (((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
        Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)).mulVec t a ∈ (A.pl v).1.adicCompletionIntegers F)
    (hJ : IsUnit J.det) (hB : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1)
    (Lc : Submodule (𝓞 E) (Fin n → E)) (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lc ↔
      ((y.1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F S.Lb)
    (hle : ∀ x ∈ Lc, x ∈ dualSet (σ : E →+* E) J Lc)
    (B' : GL (Fin n) E) (hB' : IsLocBasis p (dualSet (σ : E →+* E) J Lc) B')
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (κ : S.U) (b k : ℕ)
    (h : y.1 ^ (b + k) = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y.1 ^ b * κ.1) (v : Fin G.P.nV) :
    (A.iw v (epsU A.B B' γ k : Eˣ) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range ∧
      A.iw v (σ (epsU A.B B' γ k : Eˣ)) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range) ∧
    (A.iw v ((epsU A.B B' γ k : Eˣ) : E)⁻¹ ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range ∧
      A.iw v (σ ((epsU A.B B' γ k : Eˣ) : E)⁻¹) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range) := by
  have key : ∀ x : E, A.phE v x ∈ (A.pl v).1.adicCompletionIntegers F → A.iw v x ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
    intro x hx
    refine (hW v _).2 ?_
    have e : A.eQ v (A.iw v x) = A.phE v x := (A.eQ v).apply_symm_apply _
    rw [e]
    exact hx
  obtain ⟨h1, h2⟩ := epsU_ph S A hp hT halg hb Lc y hy hle B' hB' γ κ b k h v
  have e1 : A.iw v (epsU A.B B' γ k : Eˣ) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := key _ h1
  have e2 : A.iw v ((epsU A.B B' γ k : Eˣ) : E)⁻¹ ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
    refine key _ ?_
    rw [← map_inv, Units.coe_map] at h2
    rw [← Units.val_inv_eq_inv_val]
    exact h2
  have hg := gramW_gen S A hW hp hT halg hJ Lc y hy hle B' hB' v
  have g1 : A.iw v (cT (σ : E →+* E) B'.1 * J * B'.1).det ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
    rw [RingHom.map_det]
    exact det_mem_sub _ _ fun a b => (hg a b).1
  have g2 : A.iw v ((cT (σ : E →+* E) B'.1 * J * B'.1).det)⁻¹ ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
    have e : ((cT (σ : E →+* E) B'.1 * J * B'.1).det)⁻¹ = ((cT (σ : E →+* E) B'.1 * J * B'.1)⁻¹).det := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [e, RingHom.map_det]
    exact det_mem_sub _ _ fun a b => (hg a b).2
  have hc := epsU_conj hJ A.B B' γ k hγ hB
  have h0 : ((epsU A.B B' γ k : Eˣ) : E) ≠ 0 := Units.ne_zero _
  have c1 : σ (epsU A.B B' γ k : Eˣ) = ((cT (σ : E →+* E) B'.1 * J * B'.1).det) ^ k * ((epsU A.B B' γ k : Eˣ) : E)⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ h0).2 hc
  refine ⟨⟨e1, ?_⟩, e2, ?_⟩
  · rw [c1, map_mul, map_pow]
    exact Subring.mul_mem _ (Subring.pow_mem _ g1 k) e2
  · rw [map_inv₀, c1, mul_inv, inv_inv, ← inv_pow, map_mul, map_pow]
    exact Subring.mul_mem _ (Subring.pow_mem _ g2 k) e1

end Gen

theorem zpow_calc {K : Type} [Field K] (a b : K) (c : ℤ) (k : ℕ) :
    (a ^ (-c)) ^ k * ((b⁻¹) ^ (-c)) ^ k = ((b * a⁻¹) ^ k) ^ c := by
  rw [_root_.inv_zpow', neg_neg, _root_.zpow_neg, ← _root_.inv_zpow, ← mul_pow, ← mul_zpow, mul_comm a⁻¹ b, ← zpow_natCast, ← _root_.zpow_mul,
    mul_comm c, _root_.zpow_mul, zpow_natCast]

variable {D : D7}

theorem intW_of_pow (w : D.what₂.places.Pl) (r : D.what₂.LL) (k : ℕ) (hk : 0 < k) (h1 : r ^ k ∈ intW D.what₂.places w)
    (h2 : (r ^ k)⁻¹ ∈ intW D.what₂.places w) : r ∈ intW D.what₂.places w ∧ r⁻¹ ∈ intW D.what₂.places w := by
  by_cases hr0 : r = 0
  · subst hr0
    exact ⟨Subring.zero_mem _, by rw [_root_.inv_zero]; exact Subring.zero_mem _⟩
  have hd : r ∈ intW D.what₂.places w ∨ r⁻¹ ∈ intW D.what₂.places w := by
    by_contra hcon
    rw [not_or] at hcon
    have a1 : D.what₂.places.val w r < 0 := not_le.1 hcon.1
    have a2 : D.what₂.places.val w r⁻¹ < 0 := not_le.1 hcon.2
    have a3 : D.what₂.places.val w r + D.what₂.places.val w r⁻¹ < 0 := Left.add_neg_of_neg_of_nonpos a1 a2.le
    rw [← AddValuation.map_mul, mul_inv_cancel₀ hr0, AddValuation.map_one] at a3
    exact lt_irrefl _ a3
  have e1 : r⁻¹ = r ^ (k - 1) * (r ^ k)⁻¹ := by
    have : r ^ k = r ^ (k - 1) * r := pow_sub_one_mul hk.ne' r |>.symm
    rw [this, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr0), one_mul]
  have e2 : r = (r⁻¹) ^ (k - 1) * r ^ k := by
    have : r ^ k = r ^ (k - 1) * r := pow_sub_one_mul hk.ne' r |>.symm
    rw [this, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hr0), one_mul]
  rcases hd with h | h
  · exact ⟨h, by rw [e1]; exact Subring.mul_mem _ (Subring.pow_mem _ h _) h2⟩
  · exact ⟨by rw [e2]; exact Subring.mul_mem _ (Subring.pow_mem _ h _) h1, h⟩

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

set_option maxHeartbeats 4000000 in

theorem exists_pow (S : StepIn M i hi G) (β : S.Ch) (cl : {c // S.chOf c = β}) :
    ∃ (b k : ℕ), 0 < k ∧ ∃ (g κ : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) ∧
      g.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ ∧ κ.1 ∈ (S.K β).lev.U ∧
      (S.K β).y cl ^ (b + k) = g * (S.K β).y cl ^ b * κ := by
  have hfin : Finite (Cls (S.K β).lev) := Finite.of_surjective _ (S.K β).y_bij.2
  obtain ⟨a, b, hab, he⟩ := @Finite.exists_ne_map_eq_of_infinite ℕ (Cls (S.K β).lev) _ hfin
    (fun n : ℕ => (Quotient.mk'' ((S.K β).y cl ^ n) : Cls (S.K β).lev))
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm he.symm (by omega)
  obtain ⟨g, hg, κ, hκ, e⟩ := (DoubleCoset.eq _ _ ((S.K β).y cl ^ a) ((S.K β).y cl ^ b)).1 he
  obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_subgroupOf.1 hg
  refine ⟨a, b - a, by omega, g, κ, γ, hγ, hγe.symm, Subgroup.mem_subgroupOf.1 hκ, ?_⟩
  rw [show a + (b - a) = b by omega]
  exact e

set_option maxHeartbeats 4000000 in

theorem twUnit_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (w : D.what₂.places.Pl) (β : S.Ch) (H : S.Core e β)
    (hR0 : ∀ x, x ∈ intW D.what₂.places w ↔ e x ∈ Set.range (algebraMap G.O G.Kf)) (L : LatIn S w β) : S.TwUnit w β := by
  intro cl B' hB'
  have hpw := L.resChar
  subst hpw
  obtain ⟨b, k, hk, g, κ, γ, hγ, hg, hκ, hpow⟩ := exists_pow S β cl
  have hσσ : ∀ x : D.host.E, sigD D (sigD D x) = x := fun x => by
    rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.host_conj_involutive]
  have hpow' : ((S.K β).y cl).1 ^ (b + k) =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * ((S.K β).y cl).1 ^ b * (⟨κ.1, hκ⟩ : (S.K β).lev.U).1 := by
    have := congrArg Subtype.val hpow
    rw [← hg]
    exact this
  have hiw := epsU_iw (S.K β).lev (S.loc β) H.int L.prime L.siteGood_prime_torsion L.alg L.base (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) H.std
    (S.lat cl.1) ((S.K β).y cl) ((S.K β).y_lat cl) (le_dual_chart (S.K β) cl) B' hB' γ hγ ⟨κ.1, hκ⟩ b k hpow'
  set ε : D.host.E := ((epsU (S.loc β).B B' γ k : D.host.Eˣ) : D.host.E) with hε

  have hint : ∀ x : D.host.E, (∀ v, (S.loc β).iw v x ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range ∧
      (S.loc β).iw v (sigD D x) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range) → ∀ τ, tEL D τ x ∈ intW D.what₂.places w := by
    intro x hx τ
    obtain ⟨⟨v, s⟩, rfl⟩ := S.pos.surjective τ
    rw [hR0]
    by_cases hs : Even s.val
    · have h1 := H.pos_emb v s x
      rw [if_pos hs] at h1
      rw [h1]
      exact rho_int v s.val _ (hx v).1
    · have h1 := H.pos_emb v s (sigD D x)
      rw [if_neg hs, hσσ] at h1
      rw [h1]
      exact rho_int v s.val _ (hx v).2
  have i1 : ∀ τ, tEL D τ ε ∈ intW D.what₂.places w := hint ε fun v => (hiw v).1
  have i2 : ∀ τ, (tEL D τ ε)⁻¹ ∈ intW D.what₂.places w := fun τ => by
    rw [← map_inv₀]
    exact hint ε⁻¹ (fun v => (hiw v).2) τ
  have i3 : ∀ τ, D.what₂.embLL (tEL D τ ε) ∈ unitsW D w := fun τ => ⟨_, i1 τ, i2 τ, rfl⟩

  obtain ⟨rc, hrc⟩ := H.chRat cl
  set r : D.what₂.LL := (∏ τ, (tEL D τ (S.loc β).B.1.det) ^ (-(cTw D i))) * rc *
    ∏ τ, (tEL D τ ((B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1.det)) ^ (-(cTw D i)) with hr
  have hrs : D.what₂.embLL r = S.sTw β cl B' := by
    rw [hr, map_mul, map_mul, map_prod, map_prod, hrc]
    unfold StepIn.sTw StepIn.kTw
    congr 1
    · congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_zpow₀, tEL_emb]
    · refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_zpow₀, tEL_emb]
      congr 1
      exact RingHom.map_det (embT D τ) _

  have hch : (((S.tw β).ch ((S.K β).y cl) : ℂˣ) : ℂ) ^ k * ∏ τ, (embT D τ γ.1.det) ^ (cTw D i) = 1 := by
    have h1 := congrArg (S.tw β).ch hpow
    rw [map_mul, map_mul, map_pow, map_pow, (S.tw β).ch_U κ hκ, mul_one, pow_add, mul_comm] at h1
    have h2 : (S.tw β).ch ((S.K β).y cl) ^ k = (S.tw β).ch g := mul_right_cancel h1
    have h3 := (S.tw β).ch_rat γ hγ g hg
    rw [← h2, Units.val_pow_eq_pow_val] at h3
    exact h3
  have hdet : ((B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1.det) = (B'.1.det)⁻¹ := by
    have := congrArg Units.val (map_inv Matrix.GeneralLinearGroup.det B')
    rw [Units.val_inv_eq_inv_val] at this
    exact this
  have hpw : D.what₂.embLL (r ^ k) = ∏ τ, (D.what₂.embLL (tEL D τ ε)) ^ (cTw D i) := by
    have hP0 : (∏ τ, (embT D τ γ.1.det) ^ (cTw D i)) ≠ 0 := right_ne_zero_of_mul_eq_one hch
    have hchk : (((S.tw β).ch ((S.K β).y cl) : ℂˣ) : ℂ) ^ k = (∏ τ, (embT D τ γ.1.det) ^ (cTw D i))⁻¹ :=
      eq_inv_of_mul_eq_one_left hch
    rw [map_pow, hr, map_mul, map_mul, map_prod, map_prod, hrc, mul_pow, mul_pow, hchk, ← Finset.prod_pow, ← Finset.prod_pow,
      mul_right_comm, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, map_zpow₀, tEL_emb, tEL_emb, tEL_emb, hdet, map_inv₀, zpow_calc, hε, epsU_val, map_mul, map_pow, map_mul, map_inv₀,
      map_inv₀, mul_zpow, _root_.inv_zpow]
  have hU : D.what₂.embLL (r ^ k) ∈ unitsW D w := by
    rw [hpw]
    refine Submonoid.prod_mem _ fun τ _ => ?_
    rcases Int.eq_nat_or_neg (cTw D i) with ⟨m, hm | hm⟩
    · rw [hm, zpow_natCast]
      exact Submonoid.pow_mem _ (i3 τ) m
    · rw [hm, _root_.zpow_neg, zpow_natCast]
      exact unitsW_inv (Submonoid.pow_mem _ (i3 τ) m)
  obtain ⟨r', hr1, hr2, hr3⟩ := hU
  have hrr : r' = r ^ k := D.what₂.embLL.injective hr3
  rw [hrr] at hr1 hr2
  obtain ⟨a1, a2⟩ := intW_of_pow w r k hk hr1 hr2
  exact ⟨r, a1, a2, hrs⟩

end GlobalTheory.HP
end

section

namespace GlobalTheory.HP
open Formalism Formalism.MainNotions Formalism.MainNotions.G

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.KAat

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p} {S : StepIn M i hi G} {e : D.what₂.LL →+* G.Kf}

open Classical in

theorem finClasses_of (H : ∀ β, S.Core e β) (X : ChX S) : G.FinClasses := by
  intro a
  refine ⟨((Finset.univ : Finset (C.cls i)).filter fun c => ∃ L, G.P.IsLatTup L ∧ clsOf H a L = c).attach.image
    (fun c => ((Finset.mem_filter.1 c.2).2).choose), ?_, ?_⟩
  · intro L hL
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hL
    exact ((Finset.mem_filter.1 c.2).2).choose_spec.1
  · intro L hL
    have hc : clsOf H a L ∈ (Finset.univ : Finset (C.cls i)).filter fun c => ∃ L, G.P.IsLatTup L ∧ clsOf H a L = c :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, L, hL, rfl⟩
    refine ⟨_, Finset.mem_image.2 ⟨⟨clsOf H a L, hc⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have spec := ((Finset.mem_filter.1 hc).2).choose_spec
    obtain ⟨_, γ, hγ⟩ := (clsOf_iff H X a a _ L spec.1 hL).1 spec.2
    exact ⟨γ, hγ⟩

end GlobalTheory.HP
end

section

namespace GlobalTheory.HP
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ.PValIntN GlobalTheory.HP
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

section Step

variable {j : ℕ} (hj : j + 1 ≤ D.R.m) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

set_option maxHeartbeats 2000000 in

structure StepTies (Fo : FormsIn M (j + 1) hj) (Lc : LocIn X0 u w h Lv j Fo.Ch) (Gt : GatTies D) (c : LatCmp D) : Prop where

  frRat : ∀ β, FrRatJ (Lc.t β) Lc.B

  sameU : ∀ β, SameUlocJ hj (Fo.K β).lev (Lc.Uloc β)

  hypT : ∀ β, HypTJ (Lc.t β)

  bad_p : ∀ w' ∈ Fo.bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal

  std : cT (sigD D : D.host.E →+* D.host.E) (reGL (rankN D (j + 1) hj) D.host.E Lc.B).1 * gramN D (j + 1) hj *
    (reGL (rankN D (j + 1) hj) D.host.E Lc.B).1 = 1

  psi : ∀ β, UnitCharacterChartCompatibility hj (Fo.K β).lev (c.embW u w h) (Lc.ψ β)

  chRat : ∀ β cl, ∃ r : D.what₂.LL, D.what₂.embLL r = ((Fo.tw β).ch ((Fo.K β).y cl) : ℂ)

  hypC : ∀ β, HypTJC (Lc.t β)

  ok : Fo.okW w

  siteGood_prime_torsion : ¬ D.what₂.places.resChar w ∣ Fo.T

  Lb_eq : ∀ β, (Fo.K β).lev.Lb = reL (rankN D (j + 1) hj) (Lc.Lb β)

variable {hj} {Gt : GatTies D} {c : LatCmp D} {T : ∀ u : D.what₂.Word, Forms0 D u}
  {Fo : FormsIn M (j + 1) hj} {Lc : LocIn X0 u w h Lv j Fo.Ch}

theorem StepTies.chi (S : StepTies hj Fo Lc Gt c) (β : Fo.Ch) (κ : (Fo.K β).lev.U) :
    ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧ D.what₂.embLL r = ((Fo.K β).lev.chi κ : ℂ) :=
  chiUnit_of hj (Fo.K β).lev (S.sameU β) (c.embW u w h) (S.psi β) S.bad_p (fun x => c.embW_int u w h x) κ

set_option maxHeartbeats 4000000 in

theorem StepTies.ties (S : StepTies hj Fo Lc Gt c) (β : Fo.Ch) : LocTiesR hj Fo Lc (c.embW u w h) β where
  frRat := S.frRat β
  sameU := S.sameU β
  hypT := S.hypT β
  bad_p := S.bad_p
  std := S.std
  psi := S.psi β
  chiRat := fun κ => let ⟨r, _, _, hr⟩ := S.chi β κ; ⟨r, hr⟩
  chRat := S.chRat β

theorem StepTies.lat (S : StepTies hj Fo Lc Gt c) (β : Fo.Ch) : LatTies hj w Fo β (Lc.Lb β) where
  siteGood_prime_torsion := S.siteGood_prime_torsion
  Lb_eq := S.Lb_eq β
  lat := fun cl => isLattice_chart (Fo.K β) cl
  chi := S.chi β

theorem StepTies.core (S : StepTies hj Fo Lc Gt c) (K : CmpTied D X0 T Gt c) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w h Fl) (β : Fo.Ch) :
    (stepInOf hj Fo Lc (Gt.gat_pos u w h)).Core (c.embW u w h) β :=
  core_of_R hj K ht hF (S.ties β)

theorem StepTies.valIntN (S : StepTies hj Fo Lc Gt c) (K : CmpTied D X0 T Gt c) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w h Fl) :
    (stepInOf hj Fo Lc (Gt.gat_pos u w h)).ValIntN (c.embW u w h) w :=
  valIntN_rec hj (c.embW u w h) (fun β => locTies_of hj K ht hF (S.ties β)) Formalism.L2.G.RelativeIndexFlags.blockRationality_holds
    ((D.gat u w h).P.setting (plc Gt u w h)).frac_O (fun x => c.embW_int u w h x) S.lat

theorem StepTies.twUnit (S : StepTies hj Fo Lc Gt c) (K : CmpTied D X0 T Gt c) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w h Fl) (β : Fo.Ch) :
    (stepInOf hj Fo Lc (Gt.gat_pos u w h)).TwUnit w β :=
  twUnit_of (stepInOf hj Fo Lc (Gt.gat_pos u w h)) (c.embW u w h) w β (S.core K ht hF β) (fun x => c.embW_int u w h x) (latIn_of hj (S.ties β).frRat (S.lat β))

theorem StepTies.chX (S : StepTies hj Fo Lc Gt c) : ChX (stepInOf hj Fo Lc (Gt.gat_pos u w h)) :=
  chX_stepInOf hj Fo Lc (Gt.gat_pos u w h) (fun β => (S.ties β).sameU) (fun β => (S.ties β).frRat) S.hypC

end Step

structure HypTiesI (X0 : Formalism.L2.Herm.Herm0 D) (I : CmpJIn Tw u μ w h Lv) (Gt : GatTies D) (c : LatCmp D) : Prop where

  fl_t : Fl.t = D.R.t

  fill : FillTie Gt u w h Fl

  step : ∀ j hj, ∃ (Fo : FormsIn (I.at' j hj).M (j + 1) hj) (Lc : LocIn X0 u w h Lv j Fo.Ch),
    (I.at' j hj).st = stepInOf hj Fo Lc (Gt.gat_pos u w h) ∧ StepTies hj Fo Lc Gt c

variable {Gt : GatTies D} {c : LatCmp D} {T : ∀ u : D.what₂.Word, Forms0 D u}

theorem HypTiesI.chX {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) : ChX (I.at' j hj).st := by
  obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
  rw [e]
  exact S.chX

theorem HypTiesI.core {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (K : CmpTied D X0 T Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    ∀ β, (I.at' j hj).st.Core (c.embW u w h) β := by
  obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
  rw [e]
  exact S.core K A.fl_t A.fill

theorem HypTiesI.fin {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (K : CmpTied D X0 T Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    (gatJ Lv (j + 1)).FinClasses :=
  finClasses_of (S := (I.at' j hj).st) (A.core K j hj) (A.chX j hj)

theorem HypTiesI.hyp {I : CmpJIn Tw u μ w h Lv} (A : HypTiesI X0 I Gt c) (K : CmpTied D X0 T Gt c) : CmpJHyp c I :=
  cmpJHyp_of_two c Gt Formalism.L2.G.RelativeIndexFlags.blockRationality_holds
    (A.core K)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact S.ok)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact S.twUnit K A.fl_t A.fill)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact S.valIntN K A.fl_t A.fill)
    (fun j hj => by
      obtain ⟨Fo, Lc, e, S⟩ := A.step j hj
      rw [e]
      exact iwF_of hj Fo Lc (Gt.gat_pos u w h))
    (A.fin K) A.chX
    (fun j hj => formsOnClassOf _)
    (fun j hj => GlobalTheory.HP.cmpLiftOf_holds _ _)

end GlobalTheory.HP
end

end
