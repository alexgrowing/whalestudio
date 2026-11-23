import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
import Formalism.WachLatticeTwists.LatticeDualFibres.PropLocContOfLattices
import Formalism.WeaklyAdmissibleFiltrations.PhtGalois

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module
open Formalism.NG (KO annih)

namespace Formalism.MainNotions.BlochKatoDuality

namespace Br

section AlgDefs

variable {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL]

variable (O LL) in

abbrev OL : Submodule O LL := LinearMap.range (Algebra.linearMap O LL)

variable {V V' W W' : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
    [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
    [AddCommGroup W'] [Module LL W'] [Module O W'] [IsScalarTower O LL W']

def dualS (P : V →ₗ[LL] V' →ₗ[LL] LL) (T : Submodule O V) : Submodule O V' where
  carrier := {y | ∀ x ∈ T, ∃ a : O, P x y = algebraMap O LL a}
  add_mem' := by
    intro y z hy hz x hx
    obtain ⟨a, ha⟩ := hy x hx
    obtain ⟨b, hb⟩ := hz x hx
    exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  zero_mem' := fun x _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c y hy x hx
    obtain ⟨a, ha⟩ := hy x hx
    refine ⟨c * a, ?_⟩
    rw [← algebraMap_smul LL c y, map_smul, ha, map_mul, smul_eq_mul]

theorem mem_dualS (P : V →ₗ[LL] V' →ₗ[LL] LL) (T : Submodule O V) (y : V') :
    y ∈ dualS P T ↔ ∀ x ∈ T, ∃ a : O, P x y = algebraMap O LL a := by
  exact Iff.rfl

def shear (Y : Submodule O V) (T : Submodule O W) (ψ : V →ₗ[LL] W) : Submodule O (V × W) where
  carrier := {p | p.1 ∈ Y ∧ p.2 - ψ p.1 ∈ T}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Y.add_mem ha hb, ?_⟩
    have : (a + b).2 - ψ (a + b).1 = (a.2 - ψ a.1) + (b.2 - ψ b.1) := by
      simp only [Prod.snd_add, Prod.fst_add, map_add]; abel
    rw [this]; exact T.add_mem ha' hb'
  zero_mem' := ⟨Y.zero_mem, by simp⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨Y.smul_mem c ha, ?_⟩
    have : (c • a).2 - ψ (c • a).1 = c • (a.2 - ψ a.1) := by
      simp only [Prod.smul_snd, Prod.smul_fst, smul_sub]
      rw [← algebraMap_smul LL c a.1, map_smul, algebraMap_smul]
    rw [this]; exact T.smul_mem c ha'

end AlgDefs

section AlgA

variable {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL]

variable (O LL) in
theorem exists_quotKO : Nonempty ((LL ⧸ OL O LL) ≃ₗ[O] KO O) := by
  let e : LL ≃ₗ[O] FractionRing O := (FractionRing.algEquiv O LL).symm.toLinearEquiv
  refine ⟨Submodule.Quotient.equiv (OL O LL) (1 : Submodule O (FractionRing O)) e ?_⟩
  rw [Submodule.one_eq_range, ← LinearMap.range_comp]
  congr 1
  ext
  simp [e]

theorem length_quot_ne_top (a : O) (ha : a ≠ 0) :
    Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := by
  rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]
  intro h
  exact ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)

variable {V V' W W' : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
    [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
    [AddCommGroup W'] [Module LL W'] [Module O W'] [IsScalarTower O LL W']

theorem lat_free (T : Submodule O V) (hfg : T.FG) (hsp : Submodule.span LL (T : Set V) = ⊤) :
    Module.Free O T := by
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors O T := by
    refine ⟨fun {c x} h => ?_⟩
    have h' : c • (x : V) = 0 := by simpa using congrArg Subtype.val h
    rw [← algebraMap_smul LL c (x : V)] at h'
    rcases smul_eq_zero.mp h' with h1 | h1
    · left
      exact (IsFractionRing.injective O LL) (by rw [h1, map_zero])
    · right
      exact Subtype.ext h1
  exact Module.free_of_finite_type_torsion_free'

theorem finrank_lat (T : Submodule O V) (hfg : T.FG) (hsp : Submodule.span LL (T : Set V) = ⊤) :
    finrank O T = finrank LL V := by
  have : Submodule.IsLattice LL T := ⟨hfg, hsp⟩
  have : Module.Free O T := Submodule.IsLattice.free LL T
  let b := Module.Free.chooseBasis O T
  rw [Module.finrank_eq_nat_card_basis b, Module.finrank_eq_nat_card_basis (b.extendOfIsLattice LL)]

theorem exists_lin_lift (Y : Submodule O V) (hfg : Y.FG)
    (hsp : Submodule.span LL (Y : Set V) = ⊤) (T : Submodule O W) (φ : ↥Y →ₗ[O] (W ⧸ T)) :
    ∃ ψ : V →ₗ[LL] W, ∀ y : ↥Y, φ y = Submodule.Quotient.mk (ψ y) := by
  have : Submodule.IsLattice LL Y := ⟨hfg, hsp⟩
  have : Module.Free O Y := Submodule.IsLattice.free LL Y
  let b := Module.Free.chooseBasis O Y
  let bV := b.extendOfIsLattice LL
  have hb : ∀ i, bV i = (b i : V) := fun i => by simp [bV]
  choose x hx using fun i => Submodule.Quotient.mk_surjective T (φ (b i))
  let ψ : V →ₗ[LL] W := bV.constr LL x
  have hψ : ∀ i, ψ (b i : V) = x i := fun i => by rw [← hb]; exact bV.constr_basis LL x i
  have key : φ = T.mkQ ∘ₗ (ψ.restrictScalars O) ∘ₗ Y.subtype := by
    refine b.ext fun i => ?_
    show φ (b i) = Submodule.Quotient.mk (ψ (b i : V))
    rw [hψ, hx]
  exact ⟨ψ, fun y => by rw [key]; rfl⟩

theorem exists_quot_embed (T : Submodule O V) (hfg : T.FG)
    (hsp : Submodule.span LL (T : Set V) = ⊤) :
    ∃ E : V →ₗ[O] (Fin (finrank O T) → KO O), LinearMap.ker E = T := by
  have : Submodule.IsLattice LL T := ⟨hfg, hsp⟩
  have : Module.Free O T := Submodule.IsLattice.free LL T
  have : Module.Finite O T := Module.Finite.iff_fg.mpr hfg
  let b := Module.finBasis O T
  let bV := b.extendOfIsLattice LL
  have hb : ∀ i, bV i = (b i : V) := fun i => by simp [bV]
  obtain ⟨κ₀⟩ := exists_quotKO O LL
  let κ : LL →ₗ[O] KO O := κ₀.toLinearMap ∘ₗ (OL O LL).mkQ
  have hκ : ∀ a : LL, κ a = 0 ↔ a ∈ OL O LL := by
    intro a
    show κ₀ (Submodule.Quotient.mk a) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
  have hcoord : ∀ (i : Fin (finrank O T)) (t : ↥T),
      bV.coord i (t : V) = algebraMap O LL (b.coord i t) := by
    intro i
    have : ((bV.coord i).restrictScalars O) ∘ₗ T.subtype =
        (Algebra.linearMap O LL) ∘ₗ (b.coord i) := by
      refine b.ext fun j => ?_
      show bV.coord i (b j : V) = algebraMap O LL (b.coord i (b j))
      rw [← hb]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self]
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    exact fun t => LinearMap.congr_fun this t
  refine ⟨LinearMap.pi fun i => κ ∘ₗ (bV.coord i).restrictScalars O, ?_⟩
  ext x
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have h' : ∀ i, bV.coord i x ∈ OL O LL := fun i => (hκ _).mp (congrFun h i)
    choose a ha using h'
    have : x = ∑ i, a i • (b i : V) := by
      conv_lhs => rw [← bV.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb, ← algebraMap_smul LL (a i)]
      congr 1
      exact (ha i).symm
    rw [this]
    exact T.sum_mem fun i _ => T.smul_mem _ (b i).2
  · intro h
    funext i
    show κ (bV.coord i x) = 0
    rw [hκ, hcoord i ⟨x, h⟩]
    exact ⟨_, rfl⟩

end AlgA

section Part2a

variable {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL]

variable {V V' W W' : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
    [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
    [AddCommGroup W'] [Module LL W'] [Module O W'] [IsScalarTower O LL W']

def toDual_of_pairing [FiniteDimensional LL V] [FiniteDimensional LL V']
    (P : V →ₗ[LL] V' →ₗ[LL] LL) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0)
    (h3 : finrank LL V = finrank LL V') : V' ≃ₗ[LL] Module.Dual LL V :=
  LinearMap.linearEquivOfInjective P.flip
    (by
      rw [injective_iff_map_eq_zero]
      intro y hy
      exact h2 y fun x => by
        have := LinearMap.congr_fun hy x
        simpa using this)
    (by rw [Subspace.dual_finrank_eq, h3])

theorem toDual_apply_alt [FiniteDimensional LL V] [FiniteDimensional LL V']
    (P : V →ₗ[LL] V' →ₗ[LL] LL) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0)
    (h3 : finrank LL V = finrank LL V') (y : V') (x : V) : toDual_of_pairing P h2 h3 y x = P x y := rfl

theorem basis_repr_left_eq_pairing {ι : Type} [Fintype ι] [DecidableEq ι] (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (b : Basis ι LL V) (b' : Basis ι LL V') (hδ : ∀ i j, P (b i) (b' j) = if i = j then 1 else 0)
    (x : V) (i : ι) : b.repr x i = P x (b' i) := by
  have h : P x (b' i) = ∑ j, b.repr x j * P (b j) (b' i) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [h, Finset.sum_eq_single i]
  · rw [hδ, if_pos rfl, mul_one]
  · intro j _ hj
    rw [hδ, if_neg hj, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem basis_repr_right_eq_pairing {ι : Type} [Fintype ι] [DecidableEq ι] (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (b : Basis ι LL V) (b' : Basis ι LL V') (hδ : ∀ i j, P (b i) (b' j) = if i = j then 1 else 0)
    (y : V') (j : ι) : b'.repr y j = P (b j) y := by
  have h : P (b j) y = ∑ k, b'.repr y k * P (b j) (b' k) := by
    conv_lhs => rw [← b'.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [h, Finset.sum_eq_single j]
  · rw [hδ, if_pos rfl, mul_one]
  · intro k _ hk
    rw [hδ, if_neg (Ne.symm hk), mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem dualS_lattice [FiniteDimensional LL V] [FiniteDimensional LL V']
    (P : V →ₗ[LL] V' →ₗ[LL] LL) (_h1 : ∀ x, (∀ y, P x y = 0) → x = 0)
    (h2 : ∀ y, (∀ x, P x y = 0) → y = 0) (h3 : finrank LL V = finrank LL V')
    (T : Submodule O V) (hfg : T.FG) (hsp : Submodule.span LL (T : Set V) = ⊤) :
    (dualS P T).FG ∧ Submodule.span LL ((dualS P T : Submodule O V') : Set V') = ⊤ ∧
      dualS P.flip (dualS P T) = T := by
  classical
  have : Submodule.IsLattice LL T := ⟨hfg, hsp⟩
  have : Module.Free O T := lat_free T hfg hsp
  have : Module.Finite O T := Module.Finite.iff_fg.2 hfg
  let b := Module.Free.chooseBasis O T
  let bV := b.extendOfIsLattice LL
  have hbV : ∀ i, bV i = (b i : V) := fun i => by simp [bV]
  let bV' := bV.dualBasis.map (toDual_of_pairing P h2 h3).symm
  have hδ : ∀ i j, P (bV i) (bV' j) = if i = j then 1 else 0 := by
    intro i j
    rw [← toDual_apply_alt P h2 h3]
    simp [bV', Finsupp.single_apply]
  have hT : ∀ x ∈ T, ∀ i, ∃ a : O, bV.repr x i = algebraMap O LL a := by
    intro x hx i
    refine ⟨b.repr ⟨x, hx⟩ i, ?_⟩
    have hx' : x = ∑ k, algebraMap O LL (b.repr ⟨x, hx⟩ k) • bV k := by
      have := congrArg (Submodule.subtype T) (b.sum_repr ⟨x, hx⟩)
      simp only [map_sum, map_smul, Submodule.subtype_apply] at this
      refine this.symm.trans ?_
      exact Finset.sum_congr rfl fun k _ => by rw [hbV, algebraMap_smul]
    have h := congrFun (bV.repr_sum_self fun k => algebraMap O LL (b.repr ⟨x, hx⟩ k)) i
    rw [← hx'] at h
    exact h
  have hmemT : ∀ x : V, (∀ i, ∃ a : O, bV.repr x i = algebraMap O LL a) → x ∈ T := by
    intro x hx
    rw [← bV.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := hx i
    rw [ha, algebraMap_smul, hbV]
    exact T.smul_mem a (b i).2
  have hb' : ∀ j, bV' j ∈ dualS P T := by
    intro j x hx
    rw [← basis_repr_left_eq_pairing P bV bV' hδ]
    exact hT x hx j
  have heq : dualS P T = Submodule.span O (Set.range bV') := by
    apply le_antisymm
    · intro y hy
      rw [← bV'.sum_repr y]
      refine Submodule.sum_mem _ fun j _ => ?_
      obtain ⟨a, ha⟩ := hy (bV j) (by rw [hbV]; exact (b j).2)
      rw [basis_repr_right_eq_pairing P bV bV' hδ, ha, algebraMap_smul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hb' j
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact Submodule.fg_span (Set.finite_range _)
  · rw [eq_top_iff, ← bV'.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact hb' j
  · apply le_antisymm
    · intro x hx
      apply hmemT
      intro i
      rw [basis_repr_left_eq_pairing P bV bV' hδ]
      exact hx (bV' i) (hb' i)
    · intro x hx y hy
      exact hy x hx

theorem exists_transpose [FiniteDimensional LL V] [FiniteDimensional LL V']
    (P : V →ₗ[LL] V' →ₗ[LL] LL) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0)
    (h3 : finrank LL V = finrank LL V') (Q : W →ₗ[LL] W' →ₗ[LL] LL) (ψ : V →ₗ[LL] W) :
    ∃ ψt : W' →ₗ[LL] V', ∀ x f, P x (ψt f) = Q (ψ x) f := by
  refine ⟨(toDual_of_pairing P h2 h3).symm.toLinearMap ∘ₗ (LinearMap.lcomp LL LL ψ) ∘ₗ Q.flip, fun x f => ?_⟩
  rw [← toDual_apply_alt P h2 h3]
  simp

theorem shear_lattice (Y : Submodule O V) (hY : Y.FG) (hYs : Submodule.span LL (Y : Set V) = ⊤)
    (T : Submodule O W) (hT : T.FG) (hTs : Submodule.span LL (T : Set W) = ⊤) (ψ : V →ₗ[LL] W) :
    (shear Y T ψ).FG ∧ Submodule.span LL ((shear Y T ψ : Submodule O (V × W)) : Set (V × W)) = ⊤ := by
  constructor
  · have heq : shear Y T ψ = (Y.prod T).map (LinearMap.prod (LinearMap.fst O V W)
        (LinearMap.snd O V W + (ψ.restrictScalars O) ∘ₗ LinearMap.fst O V W)) := by
      ext ⟨v, w⟩
      constructor
      · rintro ⟨hv, hw⟩
        exact ⟨(v, w - ψ v), ⟨hv, hw⟩, by simp⟩
      · rintro ⟨⟨y, t⟩, ⟨hy, ht⟩, he⟩
        simp only [LinearMap.prod_apply, LinearMap.fst_apply, LinearMap.add_apply, LinearMap.snd_apply,
          LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨hy, ?_⟩
        show t + ψ y - ψ y ∈ T
        simpa using ht
    rw [heq]
    exact (hY.prod hT).map _
  · rw [eq_top_iff]
    rintro ⟨v, w⟩ -
    have h0 : ∀ w : W, ((0 : V), w) ∈ Submodule.span LL (shear Y T ψ : Set (V × W)) := by
      intro w
      have hw : w ∈ Submodule.span LL (T : Set W) := hTs ▸ Submodule.mem_top
      have hle : Submodule.map (LinearMap.inr LL V W) (Submodule.span LL (T : Set W)) ≤
          Submodule.span LL (shear Y T ψ : Set (V × W)) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨Y.zero_mem, by simpa using ht⟩
      exact hle ⟨w, hw, rfl⟩
    have h1 : ∀ v : V, (v, ψ v) ∈ Submodule.span LL (shear Y T ψ : Set (V × W)) := by
      intro v
      have hv : v ∈ Submodule.span LL (Y : Set V) := hYs ▸ Submodule.mem_top
      have hle : Submodule.map (LinearMap.prod LinearMap.id ψ) (Submodule.span LL (Y : Set V)) ≤
          Submodule.span LL (shear Y T ψ : Set (V × W)) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨hy, by simp⟩
      exact hle ⟨v, hv, rfl⟩
    have e : (v, w) = (v, ψ v) + ((0 : V), w - ψ v) := by simp
    rw [e]
    exact Submodule.add_mem _ (h1 v) (h0 (w - ψ v))

end Part2a

section Top

variable {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [FiniteDimensional LL V] [TopologicalSpace V] [IsModuleTopology LL V]

theorem lat_open (hopen : IsOpen (Set.range (algebraMap O LL))) (T : Submodule O V) (hfg : T.FG)
    (hsp : Submodule.span LL (T : Set V) = ⊤) : IsOpen (T : Set V) := by
  have : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup LL V
  have : Submodule.IsLattice LL T := ⟨hfg, hsp⟩
  have : Module.Free O T := lat_free T hfg hsp
  have : Module.Finite O T := Module.Finite.iff_fg.2 hfg
  let b := Module.Free.chooseBasis O T
  let bV := b.extendOfIsLattice LL
  let S : Set V := ⋂ i, (fun v => bV.coord i v) ⁻¹' (Set.range (algebraMap O LL))
  have hS : IsOpen S := by
    refine isOpen_iInter_of_finite fun i => hopen.preimage ?_
    exact IsModuleTopology.continuous_of_linearMap (bV.coord i)
  have h0 : (0 : V) ∈ S := by
    refine Set.mem_iInter.2 fun i => ⟨0, ?_⟩
    simp
  have hST : S ⊆ (T : Set V) := by
    intro v hv
    rw [Set.mem_iInter] at hv
    rw [← bV.sum_repr v]
    refine T.sum_mem fun i _ => ?_
    obtain ⟨a, ha⟩ := hv i
    have ha' : bV.repr v i = algebraMap O LL a := ha.symm
    rw [ha', algebraMap_smul, Module.Basis.extendOfIsLattice_apply]
    exact T.smul_mem a (b i).2
  have : (T.toAddSubgroup : Set V) ∈ nhds (0 : V) := Filter.mem_of_superset (hS.mem_nhds h0) hST
  exact AddSubgroup.isOpen_of_mem_nhds T.toAddSubgroup this

end Top

theorem locConst_mk {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] (T : Submodule O V) (hT : IsOpen (T : Set V)) {Z : Type}
    [TopologicalSpace Z] (f : Z → V) (hf : Continuous f) :
    IsLocallyConstant (fun z => (Submodule.Quotient.mk (f z) : V ⧸ T)) := by
  intro s
  have hset : (fun z => (Submodule.Quotient.mk (f z) : V ⧸ T)) ⁻¹' s =
      f ⁻¹' ⋃ v ∈ ((Submodule.Quotient.mk : V → V ⧸ T) ⁻¹' s), (fun w => v + w) '' (T : Set V) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · intro h
      exact ⟨f z, h, 0, T.zero_mem, add_zero _⟩
    · rintro ⟨v, hv, w, hw, hvw⟩
      have h1 : (Submodule.Quotient.mk (f z) : V ⧸ T) = Submodule.Quotient.mk v := by
        rw [← hvw, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero T).mpr hw, add_zero]
      rw [h1]
      exact hv
  rw [hset]
  exact hf.isOpen_preimage _ (isOpen_biUnion fun v _ => (Homeomorph.addLeft v).isOpenMap _ hT)

section Prod

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

def prodRep (A B : GRep G Qp LL O) : GRep G Qp LL O where
  V := A.V × B.V
  ρ := A.ρ.prod B.ρ
  cont := fun x => (A.cont x.1).prodMk (B.cont x.2)

end Prod

section Part2b

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]

variable (LL) in
include LL in

theorem p_ne_zero : ((PD.p : ℕ) : O) ≠ 0 := by
  intro h0
  have hQ : ((PD.p : ℕ) : Qp) ≠ 0 := by
    intro hq
    apply PD.not_mem_filtration_two
    have ht : PD.t = 0 := by
      apply PD.φ_inj
      rw [PD.t_φ, map_zero, hq, zero_smul]
    rw [ht, map_zero]
    exact (PD.Fil 2).zero_mem
  have hL : ((PD.p : ℕ) : LL) ≠ 0 := by
    rw [← map_natCast (algebraMap Qp LL)]
    exact (map_ne_zero _).mpr hQ
  apply hL
  rw [← map_natCast (algebraMap O LL), h0, map_zero]

theorem isDual1_flip {A A' : GRep G Qp LL O} {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL}
    (h : IsDual1 PD A.ρ A'.ρ P) : IsDual1 PD A'.ρ A.ρ P.flip := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun g x y => by simpa using h1 g y x, fun x hx => h3 x hx, fun y hy => h2 y hy, h4.symm⟩

theorem isDualLat1_flip {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ}
    {LA' : Lattice (O := O) A'.ρ} {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL}
    (h : IsDualLat1 PD LA LA' P) : IsDualLat1 PD LA' LA P.flip := by
  refine ⟨isDual1_flip PD h.1, fun y => ?_⟩
  obtain ⟨_, h1, h2, h3⟩ := h.1
  have hL' : LA'.T = dualS P LA.T := by
    ext z
    exact h.2 z
  have hdd := (dualS_lattice P h1 h2 h3 LA.T LA.fg LA.span).2.2
  show y ∈ LA.T ↔ y ∈ dualS P.flip LA'.T
  rw [hL', hdd]

end Part2b

section GalDefs

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]

def mkLat {A : GRep G Qp LL O} (T : Submodule O A.V) (st : ∀ g, ∀ x ∈ T, A.ρ g x ∈ T) (fg : T.FG)
    (sp : Submodule.span LL (T : Set A.V) = ⊤) : Lattice (O := O) A.ρ :=
  ⟨T, st, fg, lat_free T fg sp, sp⟩

theorem cobO_congr (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (z z' : G × G → LL)
    (h : ∀ x, (Submodule.Quotient.mk (z x) : LL ⧸ L1.T) = Submodule.Quotient.mk (z' x)) :
    CobO PD L1 z ↔ CobO PD L1 z' := by
  unfold CobO
  rw [show (fun x => (Submodule.Quotient.mk (z x) : LL ⧸ L1.T)) =
    fun x => (Submodule.Quotient.mk (z' x) : LL ⧸ L1.T) from funext h]

end GalDefs

section Gal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]

theorem cup_lift {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ}
    {LA' : Lattice (O := O) A'.ρ} {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' P)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL)
    (d : G → A.V) (c : G → A'.V ⧸ LA'.T) (g h : G) (hdg : d g ∈ LA.T) (v : A'.V)
    (hv : Submodule.Quotient.mk v = c h) :
    (Submodule.Quotient.mk (cupLD LA' P d c (g, h)) : LL ⧸ L1.T) =
      Submodule.Quotient.mk (P (d g) (A'.ρ g v)) := by
  rw [Submodule.Quotient.eq]
  show P (d g) (A'.ρ g (liftD LA' (c h))) - P (d g) (A'.ρ g v) ∈ L1.T
  have hl : liftD LA' (c h) - v ∈ LA'.T :=
    (Submodule.Quotient.eq LA'.T).mp
      ((Submodule.Quotient.mk_surjective LA'.T (c h)).choose_spec.trans hv.symm)
  have hm : A'.ρ g (liftD LA' (c h) - v) ∈ LA'.T := LA'.stable g _ hl
  obtain ⟨a, ha⟩ := (hd.2 _).mp hm (d g) hdg
  rw [← map_sub (P (d g)), ← map_sub (A'.ρ g), ha, hL1]
  exact ⟨a, rfl⟩

theorem red_cob (hopen : IsOpen (Set.range (algebraMap O LL)))
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL) (z : G × G → LL)
    (hz : CobL PD z) : CobO PD L1 z := by
  obtain ⟨f, hf, rfl⟩ := hz
  have hT : IsOpen (L1.T : Set LL) := by
    rw [hL1]
    exact hopen
  refine ⟨fun g => Submodule.Quotient.mk (f g), ⟨locConst_mk L1.T hT f hf, fun _ => trivial⟩, ?_⟩
  funext x
  rfl

theorem push_mem_Z1D (hopen : IsOpen (Set.range (algebraMap O LL))) {X U : GRep G Qp LL O}
    (LY : Lattice (O := O) X.ρ) (LT : Lattice (O := O) U.ρ) (φ : ↥LY.T →ₗ[O] (U.V ⧸ LT.T))
    (hφ : IsGMapD LY LT φ) (y : ↥(latticeCocycles LY)) : pushD LY LT φ y ∈ divisibleCocycles LT := by
  have : IsTopologicalAddGroup U.V := IsModuleTopology.topologicalAddGroup LL U.V
  obtain ⟨ψ, hψ⟩ := exists_lin_lift LY.T LY.fg LY.span LT.T φ
  refine ⟨?_, fun g h => ?_⟩
  · have hc : Continuous fun g => ψ ((y : G → X.V) g) :=
      (IsModuleTopology.continuous_of_linearMap ψ).comp y.2.1.1
    have h := locConst_mk LT.T (lat_open hopen LT.T LT.fg LT.span) _ hc
    have he : pushD LY LT φ y = fun g => (Submodule.Quotient.mk (ψ ((y : G → X.V) g)) : U.V ⧸ LT.T) := by
      funext g
      exact hψ (evT LY g y)
    rw [he]
    exact h
  · have he : evT LY (g * h) y = evT LY g y + actT LY g (evT LY h y) :=
      Subtype.ext (y.2.1.2 g h)
    show φ (evT LY (g * h) y) = φ (evT LY g y) + actD LT g (φ (evT LY h y))
    rw [he, map_add, hφ]
    rfl

end Gal

section Part4

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]

variable {A A' : GRep G Qp LL O}

def pairingModuloIntegers (LA : Lattice (O := O) A.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) : A'.V →ₗ[O] ↥LA.T →ₗ[O] (LL ⧸ L1.T) :=
  LinearMap.mk₂ O (fun v t => Submodule.Quotient.mk (P (t : A.V) v))
    (fun v v' t => by rw [map_add, Submodule.Quotient.mk_add])
    (fun c v t => by rw [LinearMap.map_smul_of_tower, Submodule.Quotient.mk_smul])
    (fun v t t' => by
      rw [Submodule.coe_add, map_add, LinearMap.add_apply, Submodule.Quotient.mk_add])
    (fun c v t => by
      rw [Submodule.coe_smul, ← algebraMap_smul LL c (t : A.V), map_smul, LinearMap.smul_apply,
        algebraMap_smul, Submodule.Quotient.mk_smul])

def torsionPairing {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' P)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL) :
    (A'.V ⧸ LA'.T) →ₗ[O] ↥LA.T →ₗ[O] (LL ⧸ L1.T) :=
  LA'.T.liftQ (pairingModuloIntegers PD LA P L1) (by
    intro v hv
    rw [LinearMap.mem_ker]
    ext t
    obtain ⟨a, ha⟩ := (hd.2 v).1 hv t t.2
    show (Submodule.Quotient.mk (P (t : A.V) v) : LL ⧸ L1.T) = 0
    rw [Submodule.Quotient.mk_eq_zero, hL1, ha]
    exact ⟨a, rfl⟩)

theorem torsionPairing_mk {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' P)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL) (v : A'.V) (t : ↥LA.T) :
    torsionPairing PD hd L1 hL1 (Submodule.Quotient.mk v) t = Submodule.Quotient.mk (P (t : A.V) v) := rfl

theorem torsionPairing_equivariant {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' P)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL) (g : G)
    (w : A'.V ⧸ LA'.T) (t : ↥LA.T) :
    torsionPairing PD hd L1 hL1 (repD LA' g w) (actT LA g t) = repD L1 g (torsionPairing PD hd L1 hL1 w t) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  show (Submodule.Quotient.mk (P (A.ρ g (t : A.V)) (A'.ρ g v)) : LL ⧸ L1.T) =
    repD L1 g (Submodule.Quotient.mk (P (t : A.V) v))
  rw [hd.1.1 g (t : A.V) v]
  rfl

section Fix

variable {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' P)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL)

def cupModuloIntegers : ↥(divisibleCocycles LA') →ₗ[O] ↥(latticeCocycles LA) →ₗ[O] (G × G → LL ⧸ L1.T) :=
  LinearMap.mk₂ O
    (fun c d x => torsionPairing PD hd L1 hL1 (repD LA' x.1 ((c : G → A'.V ⧸ LA'.T) x.2)) (evT LA x.1 d))
    (fun c c' d => by
      funext x
      simp only [Submodule.coe_add, Pi.add_apply, map_add, LinearMap.add_apply])
    (fun a c d => by
      funext x
      simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, LinearMap.smul_apply])
    (fun c d d' => by
      funext x
      simp only [Pi.add_apply, map_add])
    (fun a c d => by
      funext x
      simp only [Pi.smul_apply, map_smul])

theorem cup_apply_alt (c : ↥(divisibleCocycles LA')) (d : ↥(latticeCocycles LA)) (x : G × G) :
    cupModuloIntegers PD hd L1 hL1 c d x =
      torsionPairing PD hd L1 hL1 (repD LA' x.1 ((c : G → A'.V ⧸ LA'.T) x.2)) (evT LA x.1 d) := rfl

theorem cup_eq_pairing (c : ↥(divisibleCocycles LA')) (d : ↥(latticeCocycles LA)) :
    cupModuloIntegers PD hd L1 hL1 c d = fun x => (Submodule.Quotient.mk
      (cupLD LA' P (d : G → A.V) (c : G → A'.V ⧸ LA'.T) x) : LL ⧸ L1.T) := by
  funext x
  have hq : (c : G → A'.V ⧸ LA'.T) x.2 =
      Submodule.Quotient.mk (liftD LA' ((c : G → A'.V ⧸ LA'.T) x.2)) :=
    ((Submodule.Quotient.mk_surjective LA'.T _).choose_spec).symm
  show torsionPairing PD hd L1 hL1 (repD LA' x.1 ((c : G → A'.V ⧸ LA'.T) x.2)) (evT LA x.1 d) = _
  conv_lhs => rw [hq]
  rfl

theorem torsion_cocycle_mul (c : ↥(divisibleCocycles LA')) (g h : G) : (c : G → A'.V ⧸ LA'.T) (g * h) =
    (c : G → A'.V ⧸ LA'.T) g + repD LA' g ((c : G → A'.V ⧸ LA'.T) h) := by
  exact c.2.2 g h

theorem lattice_cocycle_mul (d : ↥(latticeCocycles LA)) (g h : G) :
    evT LA (g * h) d = evT LA g d + actT LA g (evT LA h d) := by
  exact Subtype.ext (d.2.1.2 g h)

theorem cup_differential_zero (c : ↥(divisibleCocycles LA')) (d : ↥(latticeCocycles LA)) :
    ReciprocityTheory.Def.d2 (repD L1) (cupModuloIntegers PD hd L1 hL1 c d) = 0 := by
  funext x
  obtain ⟨g, h, k⟩ := x
  show repD L1 g (cupModuloIntegers PD hd L1 hL1 c d (h, k)) - cupModuloIntegers PD hd L1 hL1 c d (g * h, k) +
    cupModuloIntegers PD hd L1 hL1 c d (g, h * k) - cupModuloIntegers PD hd L1 hL1 c d (g, h) = 0
  simp only [cup_apply_alt]
  rw [← torsionPairing_equivariant PD hd L1 hL1 g, lattice_cocycle_mul, torsion_cocycle_mul, map_mul (repD LA') g h,
    Module.End.mul_apply]
  simp only [map_add, LinearMap.add_apply]
  abel

end Fix

section Fix2

variable {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' P)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL)

include hL1 in
theorem integers_isOpen (hopen : IsOpen (Set.range (algebraMap O LL))) : IsOpen (L1.T : Set LL) := by
  rw [hL1]
  exact hopen

theorem cup_isLocallyConstant (hopen : IsOpen (Set.range (algebraMap O LL))) (c : ↥(divisibleCocycles LA'))
    (d : ↥(latticeCocycles LA)) : IsLocallyConstant (cupModuloIntegers PD hd L1 hL1 c d) := by
  rw [IsLocallyConstant.iff_exists_open]
  rintro ⟨g₀, h₀⟩
  obtain ⟨U₂, hU₂, hh₀, hc⟩ := (IsLocallyConstant.iff_exists_open _).1 c.2.1 h₀
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ ((c : G → A'.V ⧸ LA'.T) h₀)
  have hcont : Continuous fun g : G => P ((d : G → A.V) g) (A'.ρ g v) :=
    (IsModuleTopology.continuous_bilinear_of_finite_left P).comp
      (d.2.1.1.prodMk (A'.cont v))
  obtain ⟨U₁, hU₁, hg₀, hf⟩ := (IsLocallyConstant.iff_exists_open _).1
    (locConst_mk L1.T (integers_isOpen PD L1 hL1 hopen) _ hcont) g₀
  refine ⟨U₁ ×ˢ U₂, hU₁.prod hU₂, ⟨hg₀, hh₀⟩, ?_⟩
  rintro ⟨g, h⟩ ⟨hg, hh⟩
  have key : ∀ g' : G, torsionPairing PD hd L1 hL1 (repD LA' g' (Submodule.Quotient.mk v)) (evT LA g' d) =
      Submodule.Quotient.mk (P ((d : G → A.V) g') (A'.ρ g' v)) := fun _ => rfl
  rw [cup_apply_alt, cup_apply_alt]
  show torsionPairing PD hd L1 hL1 (repD LA' g ((c : G → A'.V ⧸ LA'.T) h)) (evT LA g d) =
    torsionPairing PD hd L1 hL1 (repD LA' g₀ ((c : G → A'.V ⧸ LA'.T) h₀)) (evT LA g₀ d)
  rw [hc h hh, ← hv, key, key]
  exact hf g hg

theorem cup_mem_cocycles (hopen : IsOpen (Set.range (algebraMap O LL))) (c : ↥(divisibleCocycles LA'))
    (d : ↥(latticeCocycles LA)) : cupModuloIntegers PD hd L1 hL1 c d ∈ ReciprocityTheory.Def.Z2 (repD L1) ⊤ :=
  ⟨⟨cup_isLocallyConstant PD hd L1 hL1 hopen c d, fun _ => Submodule.mem_top⟩,
    LinearMap.mem_ker.2 (cup_differential_zero PD hd L1 hL1 c d)⟩

theorem cup_mem_coboundaries (c : ↥(divisibleCocycles LA')) (d : ↥(latticeCocycles LA)) (hdB : (d : G → A.V) ∈ latticeCoboundaries LA) :
    cupModuloIntegers PD hd L1 hL1 c d ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ := by
  obtain ⟨t, ht, hdt⟩ := hdB
  refine ⟨fun h => torsionPairing PD hd L1 hL1 ((c : G → A'.V ⧸ LA'.T) h) ⟨t, ht⟩,
    ⟨c.2.1.comp (fun w => torsionPairing PD hd L1 hL1 w ⟨t, ht⟩), fun _ => Submodule.mem_top⟩, ?_⟩
  funext x
  obtain ⟨g, h⟩ := x
  have hev : evT LA g d = actT LA g ⟨t, ht⟩ - ⟨t, ht⟩ := by
    apply Subtype.ext
    show (d : G → A.V) g = A.ρ g t - t
    rw [← hdt]
    rfl
  show repD L1 g (torsionPairing PD hd L1 hL1 ((c : G → A'.V ⧸ LA'.T) h) ⟨t, ht⟩) -
      torsionPairing PD hd L1 hL1 ((c : G → A'.V ⧸ LA'.T) (g * h)) ⟨t, ht⟩ +
      torsionPairing PD hd L1 hL1 ((c : G → A'.V ⧸ LA'.T) g) ⟨t, ht⟩ = cupModuloIntegers PD hd L1 hL1 c d (g, h)
  rw [cup_apply_alt, hev, ← torsionPairing_equivariant PD hd L1 hL1 g, torsion_cocycle_mul]
  simp only [map_add, map_sub, LinearMap.add_apply]
  abel

end Fix2

theorem exists_pr (hopen : IsOpen (Set.range (algebraMap O LL))) {A A' : GRep G Qp LL O}
    {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ} {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL}
    (hd : IsDualLat1 PD LA LA' P) (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hL1 : L1.T = OL O LL) :
    ∃ pr : ↥(divisibleCocycles LA') →ₗ[O] LatticeCohomology LA →ₗ[O] ReciprocityTheory.Def.H2 (repD L1) ⊤,
      ∀ (c : ↥(divisibleCocycles LA')) (d : ↥(latticeCocycles LA)), pr c (Submodule.Quotient.mk d) = 0 ↔
        CobO PD L1 (cupLD LA' P (d : G → A.V) (c : G → A'.V ⧸ LA'.T)) := by
  let pr0 : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] ReciprocityTheory.Def.H2 (repD L1) ⊤ :=
    LinearMap.mk₂ O
      (fun d c => Submodule.Quotient.mk
        (⟨cupModuloIntegers PD hd L1 hL1 c d, cup_mem_cocycles PD hd L1 hL1 hopen c d⟩ :
          ↥(ReciprocityTheory.Def.Z2 (repD L1) ⊤)))
      (fun d d' c => by
        rw [← Submodule.Quotient.mk_add]
        exact congrArg _ (Subtype.ext (map_add _ _ _)))
      (fun a d c => by
        rw [← Submodule.Quotient.mk_smul]
        exact congrArg _ (Subtype.ext (map_smul _ _ _)))
      (fun d c c' => by
        rw [← Submodule.Quotient.mk_add]
        exact congrArg _ (Subtype.ext (by
          show cupModuloIntegers PD hd L1 hL1 (c + c') d = _
          rw [map_add]; rfl)))
      (fun a d c => by
        rw [← Submodule.Quotient.mk_smul]
        exact congrArg _ (Subtype.ext (by
          show cupModuloIntegers PD hd L1 hL1 (a • c) d = _
          rw [map_smul]; rfl)))
  have hker : (latticeCoboundaries LA).comap (latticeCocycles LA).subtype ≤ LinearMap.ker pr0 := by
    intro d hdB
    rw [LinearMap.mem_ker]
    ext c
    show (Submodule.Quotient.mk (⟨cupModuloIntegers PD hd L1 hL1 c d, cup_mem_cocycles PD hd L1 hL1 hopen c d⟩ :
          ↥(ReciprocityTheory.Def.Z2 (repD L1) ⊤)) : ReciprocityTheory.Def.H2 (repD L1) ⊤) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact cup_mem_coboundaries PD hd L1 hL1 c d hdB
  refine ⟨(Submodule.liftQ _ pr0 hker).flip, fun c d => ?_⟩
  show (Submodule.Quotient.mk (⟨cupModuloIntegers PD hd L1 hL1 c d, cup_mem_cocycles PD hd L1 hL1 hopen c d⟩ :
          ↥(ReciprocityTheory.Def.Z2 (repD L1) ⊤)) : ReciprocityTheory.Def.H2 (repD L1) ⊤) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  show cupModuloIntegers PD hd L1 hL1 c d ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ ↔ _
  rw [cup_eq_pairing]
  rfl

end Part4

section Part5

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]

theorem shear_stable {X U : GRep G Qp LL O} (LT : Lattice (O := O) U.ρ)
    (LY : Lattice (O := O) X.ρ) (φ : ↥LY.T →ₗ[O] (U.V ⧸ LT.T)) (hφ : IsGMapD LY LT φ)
    (ψ : X.V →ₗ[LL] U.V) (hψ : ∀ y : ↥LY.T, φ y = Submodule.Quotient.mk (ψ y)) :
    ∀ g, ∀ p ∈ shear LY.T LT.T ψ, (prodRep X U).ρ g p ∈ shear LY.T LT.T ψ := by
  rintro g p ⟨hp1, hp2⟩
  refine ⟨LY.stable g _ hp1, ?_⟩
  show U.ρ g p.2 - ψ (X.ρ g p.1) ∈ LT.T
  have e : U.ρ g p.2 - ψ (X.ρ g p.1) = U.ρ g (p.2 - ψ p.1) + (U.ρ g (ψ p.1) - ψ (X.ρ g p.1)) := by
    rw [map_sub]
    abel
  rw [e]
  refine LT.T.add_mem (LT.stable g _ hp2) ?_
  have h1 := hφ g ⟨p.1, hp1⟩
  rw [hψ, hψ] at h1
  have h2 : repD LT g (Submodule.Quotient.mk (ψ p.1)) = Submodule.Quotient.mk (U.ρ g (ψ p.1)) := rfl
  rw [h2] at h1
  exact (Submodule.Quotient.eq LT.T).mp h1.symm

theorem absorption_direct {X U : GRep G Qp LL O} (LT : Lattice (O := O) U.ρ) (e : ℕ)
    (hL : LiftAll PD X U e) (LY : Lattice (O := O) X.ρ) (φ : ↥LY.T →ₗ[O] (U.V ⧸ LT.T))
    (hφ : IsGMapD LY LT φ) (y : ↥(latticeCocycles LY)) (hy : (y : G → X.V) ∈ latticeFiniteCocycles PD LY) :
    ((PD.p : O) ^ e) • pushD LY LT φ y ∈ HfD PD LT := by
  obtain ⟨ψ, hψ⟩ := exists_lin_lift LY.T LY.fg LY.span LT.T φ
  have hst := shear_stable LT LY φ hφ ψ hψ
  obtain ⟨hfg, hsp⟩ := shear_lattice LY.T LY.fg LY.span LT.T LT.fg LT.span ψ
  let L : Lattice (O := O) (prodRep X U).ρ :=
    mkLat (A := prodRep X U) (shear LY.T LT.T ψ) hst hfg hsp
  let F : LatHom L LY :=
    { f := LinearMap.fst LL X.V U.V
      equiv := fun g x => rfl
      cont := continuous_fst
      T_le := fun x hx => hx.1 }
  have hon : F.Onto := fun v hv => ⟨(v, ψ v), ⟨hv, by simp⟩, rfl⟩
  have hs1 : IsSubSumOf (prodRep X U).ρ X.ρ U.ρ :=
    ⟨1, 1, fun _ => LinearMap.fst LL X.V U.V, fun _ => LinearMap.snd LL X.V U.V,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun w h1 h2 => Prod.ext (h1 0) (h2 0)⟩
  have hs2 : IsSubSumOf X.ρ X.ρ U.ρ :=
    ⟨1, 0, fun _ => LinearMap.id, fun _ => 0, fun _ _ _ => rfl, fun j => j.elim0,
      fun w h1 _ => h1 0⟩
  have hlift := hL (prodRep X U) X hs1 hs2 L LY F hon (y : G → X.V) hy
  obtain ⟨a, ⟨yt, hyt, rfl⟩, b, ⟨t, ht, rfl⟩, hab⟩ := Submodule.mem_sup.1 hlift
  have hsnd : (LinearMap.snd LL X.V U.V) ∘ yt ∈ finiteCocycles PD U.ρ :=
    (cocyclesFunctorial_holds G Qp K₀ K B BdR PD LL (X.V × U.V) U.V (X.ρ.prod U.ρ) U.ρ
      (LinearMap.snd LL X.V U.V) continuous_snd (fun g x => rfl) yt).2 hyt.2
  have key : ((PD.p : O) ^ e) • pushD LY LT φ y =
      LinearMap.compLeft LT.T.mkQ G ((LinearMap.snd LL X.V U.V) ∘ yt) +
        (LinearMap.pi fun g => actD LT g - LinearMap.id) (φ ⟨t, ht⟩) := by
    funext g
    have hg : ((PD.p : O) ^ e) • (y : G → X.V) g = (yt g).1 + (X.ρ g t - t) :=
      (congrFun hab g).symm
    have hm : (yt g).2 - ψ (yt g).1 ∈ LT.T := (hyt.1.2 g (Set.mem_univ g)).2
    have e1 : (Submodule.Quotient.mk (ψ (yt g).1) : U.V ⧸ LT.T) =
        Submodule.Quotient.mk (yt g).2 :=
      ((Submodule.Quotient.eq _).2 hm).symm
    have e2 : (Submodule.Quotient.mk (ψ (X.ρ g t)) : U.V ⧸ LT.T) = actD LT g (φ ⟨t, ht⟩) := by
      have := hφ g ⟨t, ht⟩
      rw [hψ] at this
      exact this
    have e3 : (Submodule.Quotient.mk (ψ t) : U.V ⧸ LT.T) = φ ⟨t, ht⟩ := (hψ ⟨t, ht⟩).symm
    show ((PD.p : O) ^ e) • φ (evT LY g y) =
      Submodule.Quotient.mk (yt g).2 + (actD LT g (φ ⟨t, ht⟩) - φ ⟨t, ht⟩)
    rw [hψ, ← Submodule.Quotient.mk_smul, ← LinearMap.map_smul_of_tower]
    have hg' : ((PD.p : O) ^ e) • ((evT LY g y : ↥LY.T) : X.V) = (yt g).1 + (X.ρ g t - t) := hg
    rw [hg', map_add, map_sub, Submodule.Quotient.mk_add, Submodule.Quotient.mk_sub, e1, e2, e3]
  rw [key]
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hsnd) (LinearMap.mem_range_self _ _)

end Part5

section LatticeGramTransferCondition

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]

omit [TopologicalSpace G] [TopologicalSpace Qp] [TopologicalSpace LL] [IsTopologicalRing LL]
  [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] in
theorem mem_integers_iff_alt {x : LL} : x ∈ OL O LL ↔ ∃ a : O, x = algebraMap O LL a := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

omit [TopologicalSpace G] [TopologicalSpace Qp] [TopologicalSpace LL] [IsTopologicalRing LL]
  [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] in

theorem cyclotomic_mul_mem_integers (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL) (g : G)
    {x : LL} (hx : x ∈ OL O LL) : ((cycLL PD LL g : LLˣ) : LL) * x ∈ OL O LL := by
  have h := L1.stable g x (by rw [hL1]; exact hx)
  rw [hL1] at h
  exact h

theorem equivariance_defect_mem_lattice {X U : GRep G Qp LL O} (LY : Lattice (O := O) X.ρ) (LT : Lattice (O := O) U.ρ)
    (φ : ↥LY.T →ₗ[O] (U.V ⧸ LT.T)) (hφ : IsGMapD LY LT φ) (ψ : X.V →ₗ[LL] U.V)
    (hψ : ∀ y : ↥LY.T, φ y = Submodule.Quotient.mk (ψ y)) (g : G) (y : X.V) (hy : y ∈ LY.T) :
    U.ρ g (ψ y) - ψ (X.ρ g y) ∈ LT.T := by
  have h1 := hφ g ⟨y, hy⟩
  rw [hψ, hψ] at h1
  have h2 : repD LT g (Submodule.Quotient.mk (ψ y)) = Submodule.Quotient.mk (U.ρ g (ψ y)) := rfl
  rw [h2] at h1
  exact (Submodule.Quotient.eq LT.T).mp h1.symm

omit [TopologicalSpace Qp] [IsTopologicalRing LL] in

theorem shear_pairing_mem_integers {X U X' U' : GRep G Qp LL O} (PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL)
    (PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL) (Y : Submodule O X.V) (ψ : X.V →ₗ[LL] U.V)
    (ψt : U'.V →ₗ[LL] X'.V) (hψt : ∀ x f, PX x (ψt f) = PU (ψ x) f) (T' : Submodule O U'.V)
    (p : U'.V × X'.V) (hp : p ∈ shear T' (dualS PX Y) ψt) (y : X.V) (hy : y ∈ Y) :
    PX y p.2 - PU (ψ y) p.1 ∈ OL O LL := by
  obtain ⟨-, h2⟩ := hp
  obtain ⟨a, ha⟩ := h2 y hy
  rw [map_sub, hψt] at ha
  exact mem_integers_iff_alt.mpr ⟨a, ha⟩

theorem shear_lattice_stable (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL)
    {X U X' U' : GRep G Qp LL O} (PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL)
    (PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL) (LT : Lattice (O := O) U.ρ) (LT' : Lattice (O := O) U'.ρ)
    (hXX' : IsDual1 PD X.ρ X'.ρ PX) (hTT' : IsDualLat1 PD LT LT' PU)
    (LY : Lattice (O := O) X.ρ) (φ : ↥LY.T →ₗ[O] (U.V ⧸ LT.T)) (hφ : IsGMapD LY LT φ)
    (ψ : X.V →ₗ[LL] U.V) (hψ : ∀ y : ↥LY.T, φ y = Submodule.Quotient.mk (ψ y))
    (ψt : U'.V →ₗ[LL] X'.V) (hψt : ∀ x f, PX x (ψt f) = PU (ψ x) f) (g : G)
    (p : U'.V × X'.V) (hp : p ∈ shear LT'.T (dualS PX LY.T) ψt) :
    (prodRep U' X').ρ g p ∈ shear LT'.T (dualS PX LY.T) ψt := by
  refine ⟨LT'.stable g _ hp.1, ?_⟩
  intro y hy
  apply mem_integers_iff_alt.1
  have hy' : X.ρ g⁻¹ y ∈ LY.T := LY.stable _ _ hy
  have e1 : PX y (X'.ρ g p.2) = ((cycLL PD LL g : LLˣ) : LL) * PX (X.ρ g⁻¹ y) p.2 := by
    rw [← hXX'.1, Representation.self_inv_apply]
  have e2 : PU (ψ y) (U'.ρ g p.1) = ((cycLL PD LL g : LLˣ) : LL) * PU (U.ρ g⁻¹ (ψ y)) p.1 := by
    rw [← hTT'.1.1, Representation.self_inv_apply]
  have e3 : PX y (((prodRep U' X').ρ g p).2 - ψt ((prodRep U' X').ρ g p).1) =
      ((cycLL PD LL g : LLˣ) : LL) * ((PX (X.ρ g⁻¹ y) p.2 - PU (ψ (X.ρ g⁻¹ y)) p.1) -
        PU (U.ρ g⁻¹ (ψ y) - ψ (X.ρ g⁻¹ y)) p.1) := by
    change PX y (X'.ρ g p.2 - ψt (U'.ρ g p.1)) = _
    rw [map_sub, hψt, e1, e2, map_sub, LinearMap.sub_apply]
    ring
  rw [e3]
  refine cyclotomic_mul_mem_integers PD L1 hL1 g (Submodule.sub_mem _ (shear_pairing_mem_integers PX PU LY.T ψ ψt hψt LT'.T p hp _ hy')
    (mem_integers_iff_alt.2 ((hTT'.2 p.1).1 hp.1 _ (equivariance_defect_mem_lattice LY LT φ hφ ψ hψ g⁻¹ y hy))))

theorem absorption_of_duality (hO : GoodO (Qp := Qp) LL O) (h1 : bkACore PD) (h2 : bkBCore PD)
    (h4 : cycIntCore PD) (h6 : drDualCore PD) {X U X' U' : GRep G Qp LL O}
    (PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL) (PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL)
    (LT : Lattice (O := O) U.ρ) (LT' : Lattice (O := O) U'.ρ) (e : ℕ)
    (hU : IsDR PD U.ρ) (hXX' : IsDual1 PD X.ρ X'.ρ PX) (hTT' : IsDualLat1 PD LT LT' PU)
    (hX : IsDR PD X.ρ) (hL : LiftAll PD X' U' e)
    (LY : Lattice (O := O) X.ρ) (φ : ↥LY.T →ₗ[O] (U.V ⧸ LT.T))
    (hφ : IsGMapD LY LT φ) (y : ↥(latticeCocycles LY)) (hy : (y : G → X.V) ∈ latticeFiniteCocycles PD LY) :
    ((PD.p : O) ^ e) • pushD LY LT φ y ∈ HfD PD LT := by
  have hopen : IsOpen (Set.range (algebraMap O LL)) := hO.2.2.2.2
  obtain ⟨L1, hL1⟩ := h4 LL O hO
  obtain ⟨ψ, hψ⟩ := exists_lin_lift LY.T LY.fg LY.span LT.T φ
  obtain ⟨ψt, hψt⟩ := exists_transpose PX hXX'.2.2.1 hXX'.2.2.2 PU ψ
  obtain ⟨hY'fg, hY'sp, -⟩ :=
    dualS_lattice PX hXX'.2.1 hXX'.2.2.1 hXX'.2.2.2 LY.T LY.fg LY.span
  obtain ⟨hLfg, hLsp⟩ := shear_lattice LT'.T LT'.fg LT'.span (dualS PX LY.T) hY'fg hY'sp ψt
  let Lb : Lattice (O := O) (prodRep U' X').ρ :=
    mkLat (A := prodRep U' X') (shear LT'.T (dualS PX LY.T) ψt)
      (shear_lattice_stable PD L1 hL1 PX PU LT LT' hXX' hTT' LY φ hφ ψ hψ ψt hψt) hLfg hLsp
  let F : LatHom Lb LT' :=
    ⟨LinearMap.fst LL U'.V X'.V, fun g x => rfl, continuous_fst, fun x hx => hx.1⟩
  have hOnto : F.Onto := fun f hf => ⟨(f, ψt f), ⟨hf, by simp⟩, rfl⟩
  have hs1 : IsSubSumOf (prodRep U' X').ρ X'.ρ U'.ρ :=
    ⟨1, 1, fun _ => LinearMap.snd LL U'.V X'.V, fun _ => LinearMap.fst LL U'.V X'.V,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun w hp hq => Prod.ext (hq 0) (hp 0)⟩
  have hs2 : IsSubSumOf U'.ρ X'.ρ U'.ρ :=
    ⟨0, 1, fun i => i.elim0, fun _ => LinearMap.id, fun i => i.elim0, fun _ _ _ => rfl,
      fun w _ hq => hq 0⟩
  have hLift := hL (prodRep U' X') U' hs1 hs2 Lb LT' F hOnto
  have hU' : IsDR PD U'.ρ := h6 LL O hO U U' PU hU hTT'.1
  have hX' : IsDR PD X'.ρ := h6 LL O hO X X' PX hX hXX'
  have hfl := isDualLat1_flip PD hTT'
  have hB := (h2 LL O hO L1 hL1 U' U LT' LT PU.flip hU' hfl).1
  have hA := (h1 LL O hO X' X PX.flip hX' (isDual1_flip PD hXX')).1
  have hc : pushD LY LT φ y ∈ divisibleCocycles LT := push_mem_Z1D hopen LY LT φ hφ y
  obtain ⟨pr, hpr⟩ := exists_pr PD hopen hfl L1 hL1
  rw [hB _ ((divisibleCocycles LT).smul_mem _ hc)]
  intro d hd
  obtain ⟨u, ⟨κ, hκ, rfl⟩, b, hb, hsum⟩ := Submodule.mem_sup.mp (hLift d hd)
  have hκT : F.post κ ∈ latticeCocycles LT' := F.post_Z1T κ hκ.1
  have hq : (Submodule.Quotient.mk (((PD.p : O) ^ e) • (⟨d, hd.1⟩ : ↥(latticeCocycles LT'))) : LatticeCohomology LT') =
      Submodule.Quotient.mk ⟨F.post κ, hκT⟩ := by
    rw [Submodule.Quotient.eq]
    show ((PD.p : O) ^ e) • d - F.post κ ∈ latticeCoboundaries LT'
    rw [← hsum]
    simpa using hb
  have key : CobO PD L1 (cupLD LT PU.flip (F.post κ) (pushD LY LT φ y)) := by
    have hκ2 : (LinearMap.snd LL U'.V X'.V) ∘ κ ∈ finiteCocycles PD X'.ρ :=
      (cocyclesFunctorial_holds G Qp K₀ K B BdR PD LL (U'.V × X'.V) X'.V (U'.ρ.prod X'.ρ) X'.ρ
        (LinearMap.snd LL U'.V X'.V) continuous_snd (fun g x => rfl) κ).2 hκ.2
    have hcob := (hA _ hκ2.1).1 hκ2 (y : G → X.V) hy.2
    refine (cobO_congr PD L1 _ _ ?_).2 (red_cob PD hopen L1 hL1 _ hcob)
    rintro ⟨g, h⟩
    have hκg : κ g ∈ shear LT'.T (dualS PX LY.T) ψt := hκ.1.2 g (Set.mem_univ g)
    have hyh : (y : G → X.V) h ∈ LY.T := y.2.2 h (Set.mem_univ h)
    rw [cup_lift PD hfl L1 hL1 (F.post κ) (pushD LY LT φ y) g h hκg.1 (ψ ((y : G → X.V) h))
      (hψ ⟨_, hyh⟩).symm]
    rw [Submodule.Quotient.eq, hL1]
    show PU (U.ρ g (ψ ((y : G → X.V) h))) (κ g).1 - PX (X.ρ g ((y : G → X.V) h)) (κ g).2 ∈ OL O LL
    have e1 : PU (U.ρ g (ψ ((y : G → X.V) h))) (κ g).1 - PX (X.ρ g ((y : G → X.V) h)) (κ g).2 =
        PU (U.ρ g (ψ ((y : G → X.V) h)) - ψ (X.ρ g ((y : G → X.V) h))) (κ g).1 -
          (PX (X.ρ g ((y : G → X.V) h)) (κ g).2 - PU (ψ (X.ρ g ((y : G → X.V) h))) (κ g).1) := by
      rw [map_sub, LinearMap.sub_apply]
      ring
    rw [e1]
    exact Submodule.sub_mem _
      (mem_integers_iff_alt.2 ((hTT'.2 _).1 hκg.1 _ (equivariance_defect_mem_lattice LY LT φ hφ ψ hψ g _ hyh)))
      (shear_pairing_mem_integers PX PU LY.T ψ ψt hψt LT'.T _ hκg _ (LY.stable g _ hyh))
  have h0 : pr ⟨pushD LY LT φ y, hc⟩ (Submodule.Quotient.mk ⟨F.post κ, hκT⟩) = 0 :=
    (hpr ⟨_, hc⟩ ⟨_, hκT⟩).2 key
  refine (hpr ⟨((PD.p : O) ^ e) • pushD LY LT φ y, (divisibleCocycles LT).smul_mem _ hc⟩ ⟨d, hd.1⟩).1 ?_
  have e2 : (⟨((PD.p : O) ^ e) • pushD LY LT φ y, (divisibleCocycles LT).smul_mem _ hc⟩ : ↥(divisibleCocycles LT)) =
      ((PD.p : O) ^ e) • ⟨pushD LY LT φ y, hc⟩ := rfl
  rw [e2, map_smul, LinearMap.smul_apply, ← map_smul, ← Submodule.Quotient.mk_smul, hq, h0]

end LatticeGramTransferCondition

section Part7

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]

def coboundaryPreimage {A : GRep G Qp LL O} (LA : Lattice (O := O) A.ρ) : Submodule O A.V where
  carrier := {v | ∀ g, A.ρ g v - v ∈ LA.T}
  add_mem' := by
    intro a b ha hb g
    have : A.ρ g (a + b) - (a + b) = (A.ρ g a - a) + (A.ρ g b - b) := by
      rw [map_add]; abel
    rw [this]; exact LA.T.add_mem (ha g) (hb g)
  zero_mem' := fun g => by simp
  smul_mem' := by
    intro c a ha g
    have : A.ρ g (c • a) - c • a = c • (A.ρ g a - a) := by
      rw [← algebraMap_smul LL c a, map_smul, algebraMap_smul, algebraMap_smul, smul_sub]
    rw [this]; exact LA.T.smul_mem c (ha g)

theorem coboundary_mem_finite_cocycles (A : GRep G Qp LL O) (v : A.V) : cob A.ρ v ∈ finiteCocycles PD A.ρ := by
  refine ⟨⟨(by simp_rw [sub_eq_add_neg]; exact (A.cont v).add continuous_const : Continuous fun g => A.ρ g v - v), fun g h => ?_⟩, v ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_mul,
      Module.End.mul_apply, map_sub]
    abel
  · simp [cob, actVB, TensorProduct.sub_tmul]

theorem coboundary_mem_cocycles (A : GRep G Qp LL O) (v : A.V) : cob A.ρ v ∈ continuousCocycles A.ρ := by
  refine ⟨(by simp_rw [sub_eq_add_neg]; exact (A.cont v).add continuous_const : Continuous fun g => A.ρ g v - v), fun g h => ?_⟩
  simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_mul,
    Module.End.mul_apply, map_sub]
  abel

theorem coboundary_mem_lattice_cocycles {A : GRep G Qp LL O} (LA : Lattice (O := O) A.ρ) (v : ↥(coboundaryPreimage LA)) :
    ((cob A.ρ).restrictScalars O ∘ₗ (coboundaryPreimage LA).subtype) v ∈ latticeCocycles LA := by
  exact ⟨coboundary_mem_cocycles A (v : A.V), fun g _ => v.2 g⟩

def invariantsToCocycle {A : GRep G Qp LL O} (LA : Lattice (O := O) A.ρ) : ↥(coboundaryPreimage LA) →ₗ[O] ↥(latticeCocycles LA) :=
  LinearMap.codRestrict (latticeCocycles LA) ((cob A.ρ).restrictScalars O ∘ₗ (coboundaryPreimage LA).subtype)
    (coboundary_mem_lattice_cocycles LA)

def connectingMap {A : GRep G Qp LL O} (LA : Lattice (O := O) A.ρ) :
    ↥(coboundaryPreimage LA) →ₗ[O] ↥(latticeFiniteCohomology PD LA) :=
  LinearMap.codRestrict (latticeFiniteCohomology PD LA) (Submodule.mkQ _ ∘ₗ invariantsToCocycle LA)
    (fun v => ⟨invariantsToCocycle LA v, ⟨(invariantsToCocycle LA v).2, coboundary_mem_finite_cocycles PD A v⟩, rfl⟩)

theorem connectingMap_alt {A : GRep G Qp LL O} (LA : Lattice (O := O) A.ρ) (v : ↥(coboundaryPreimage LA))
    (hv : (v : A.V) ∈ LA.T) : connectingMap PD LA v = 0 := by
  apply Subtype.ext
  show Submodule.mkQ _ (invariantsToCocycle LA v) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨(v : A.V), hv, rfl⟩

theorem torsion_le_connecting_range {A : GRep G Qp LL O} (LA : Lattice (O := O) A.ρ) :
    Submodule.torsion O ↥(latticeFiniteCohomology PD LA) ≤ LinearMap.range (connectingMap PD LA) := by
  intro x hx
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
  obtain ⟨d, hd, hdx⟩ := x.2
  have ha0 : algebraMap O LL (a : O) ≠ 0 := by
    intro h
    exact (nonZeroDivisors.ne_zero a.2) ((IsFractionRing.injective O LL) (by rw [h, map_zero]))
  have h1 : (Submodule.Quotient.mk ((a : O) • d) : LatticeCohomology LA) = 0 := by
    have := congrArg Subtype.val ha
    rw [Submodule.Quotient.mk_smul]
    rw [show (Submodule.Quotient.mk d : LatticeCohomology LA) = x.1 from hdx]
    exact this
  rw [Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨t, ht, htd⟩ := h1
  have htd' : cob A.ρ t = (a : O) • (d : G → A.V) := htd
  have hv : cob A.ρ ((algebraMap O LL (a : O))⁻¹ • t) = (d : G → A.V) := by
    rw [map_smul, htd', ← algebraMap_smul LL (a : O) (d : G → A.V), smul_smul,
      inv_mul_cancel₀ ha0, one_smul]
  have hInv : (algebraMap O LL (a : O))⁻¹ • t ∈ coboundaryPreimage LA := by
    intro g
    have := congrFun hv g
    have h2 : A.ρ g ((algebraMap O LL (a : O))⁻¹ • t) - (algebraMap O LL (a : O))⁻¹ • t =
      (d : G → A.V) g := this
    rw [h2]
    exact d.2.2 g (Set.mem_univ g)
  refine ⟨⟨_, hInv⟩, ?_⟩
  apply Subtype.ext
  rw [← hdx]
  show Submodule.Quotient.mk (invariantsToCocycle LA ⟨_, hInv⟩) = Submodule.Quotient.mk d
  congr 1
  exact Subtype.ext hv

theorem tors_range {A : GRep G Qp LL O} (LA : Lattice (O := O) A.ρ) :
    ∃ (N : Submodule O (Fin (finrank O ↥LA.T) → KO O)) (δ : ↥N →ₗ[O] ↥(latticeFiniteCohomology PD LA)),
      Submodule.torsion O ↥(latticeFiniteCohomology PD LA) ≤ LinearMap.range δ := by
  obtain ⟨E, hE⟩ := exists_quot_embed (LL := LL) LA.T LA.fg LA.span
  have hs : Function.Surjective (E.submoduleMap (coboundaryPreimage LA)) :=
    LinearMap.submoduleMap_surjective E (coboundaryPreimage LA)
  have hk : LinearMap.ker (E.submoduleMap (coboundaryPreimage LA)) ≤ LinearMap.ker (connectingMap PD LA) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    apply connectingMap_alt
    rw [← hE, LinearMap.mem_ker]
    exact congrArg Subtype.val hv
  refine ⟨(coboundaryPreimage LA).map E, (Submodule.liftQ _ (connectingMap PD LA) hk) ∘ₗ
    ((E.submoduleMap (coboundaryPreimage LA)).quotKerEquivOfSurjective hs).symm.toLinearMap, ?_⟩
  intro x hx
  obtain ⟨v, rfl⟩ := torsion_le_connecting_range PD LA hx
  refine ⟨E.submoduleMap (coboundaryPreimage LA) v, ?_⟩
  have : ((E.submoduleMap (coboundaryPreimage LA)).quotKerEquivOfSurjective hs).symm
      (E.submoduleMap (coboundaryPreimage LA) v) = Submodule.Quotient.mk v := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, this]
  rfl

end Part7

section Asm

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]

theorem absorption_all (hO : GoodO (Qp := Qp) LL O) (h1 : bkACore PD) (h2 : bkBCore PD)
    (h4 : cycIntCore PD) (h6 : drDualCore PD) {V X U X' U' : GRep G Qp LL O} {χ : G →* LLˣ}
    {PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL} {PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL}
    {LT : Lattice (O := O) U.ρ} {LT' : Lattice (O := O) U'.ρ} {e : ℕ}
    (hH : Hyp PD V X U X' U' χ PX PU LT LT' e)
    (LY : Lattice (O := O) X.ρ) (φ : ↥LY.T →ₗ[O] (U.V ⧸ LT.T))
    (hφ : IsGMapD LY LT φ) (y : ↥(latticeCocycles LY)) (hy : (y : G → X.V) ∈ latticeFiniteCocycles PD LY) :
    ((PD.p : O) ^ e) • pushD LY LT φ y ∈ HfD PD LT := by
  obtain ⟨_, hU, hXX', hTT', hc⟩ := hH
  rcases hc with hL | ⟨hX, hL⟩
  · exact absorption_direct PD LT e hL LY φ hφ y hy
  · exact absorption_of_duality PD hO h1 h2 h4 h6 PX PU LT LT' e hU hXX' hTT' hX hL LY φ hφ y hy

theorem mem_annih {A H Q : Type} [AddCommGroup A] [Module O A] [AddCommGroup H] [Module O H]
    [AddCommGroup Q] [Module O Q] (pr : A →ₗ[O] H →ₗ[O] Q) (M : Submodule O H) (c : A) :
    c ∈ annih pr M ↔ ∀ x ∈ M, pr c x = 0 := by
  simp [annih, Submodule.mem_iInf, LinearMap.mem_ker]

theorem equivariant_coefficient_reproduced (hO : GoodO (Qp := Qp) LL O) (h1 : bkACore PD) (h2 : bkBCore PD)
    (h3 : LocalTateTopDegree PD) (h4 : cycIntCore PD) (h5 : TateFiniteness PD) (h6 : drDualCore PD)
    {V X U X' U' : GRep G Qp LL O} {χ : G →* LLˣ}
    {PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL} {PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL}
    {LT : Lattice (O := O) U.ρ} {LT' : Lattice (O := O) U'.ρ} {e : ℕ}
    (hH : Hyp PD V X U X' U' χ PX PU LT LT' e) :
    ∃ m k : ℕ, lenMod (spanPush PD X U LT) (HfD PD LT) = m ∧ lenOl PD (O := O) = k ∧
      m ≤ e * (finrank O ↥(latticeFiniteCohomology PD LT') + finrank O ↥LT.T) * k := by
  have hopen : IsOpen (Set.range (algebraMap O LL)) := hO.2.2.2.2
  have hU : IsDR PD U.ρ := hH.2.1
  have hTT' : IsDualLat1 PD LT LT' PU := hH.2.2.2.1
  obtain ⟨L1, hL1⟩ := h4 LL O hO
  have hflip : IsDualLat1 PD LT' LT PU.flip := isDualLat1_flip PD hTT'
  have hU' : IsDR PD U'.ρ := h6 LL O hO U U' PU hU hTT'.1
  obtain ⟨pr0, hpr0⟩ := exists_pr PD hopen hflip L1 hL1
  obtain ⟨τ⟩ := h3 LL O hO L1 hL1
  obtain ⟨κ⟩ := exists_quotKO O LL
  let ι : ReciprocityTheory.Def.H2 (repD L1) ⊤ ≃ₗ[O] KO O :=
    τ ≪≫ₗ (Submodule.quotEquivOfEq _ _ hL1 ≪≫ₗ κ)
  let pr : ↥(divisibleCocycles LT) →ₗ[O] LatticeCohomology LT' →ₗ[O] KO O := pr0.compr₂ ι.toLinearMap
  have hpr : ∀ (c : ↥(divisibleCocycles LT)) (d : ↥(latticeCocycles LT')), pr c (Submodule.Quotient.mk d) = 0 ↔
      CobO PD L1 (cupLD LT PU.flip (d : G → U'.V) (c : G → U.V ⧸ LT.T)) := by
    intro c d
    rw [← hpr0 c d]
    show ι (pr0 c (Submodule.Quotient.mk d)) = 0 ↔ _
    exact ι.map_eq_zero_iff
  have hbk := (h2 LL O hO L1 hL1 U' U LT' LT PU.flip hU' hflip).1
  have hann : annih pr (latticeFiniteCohomology PD LT') = (HfD PD LT).comap (divisibleCocycles LT).subtype := by
    ext c
    rw [mem_annih, Submodule.mem_comap, Submodule.subtype_apply, hbk c.1 c.2]
    constructor
    · intro h d hd
      exact (hpr c ⟨d, hd.1⟩).1 (h _ ⟨⟨d, hd.1⟩, hd, rfl⟩)
    · rintro h _ ⟨d, hd, rfl⟩
      exact (hpr c d).2 (h d.1 hd)
  set S := spanPush PD X U LT with hSdef
  set H := HfD PD LT with hHdef
  have hS : S ≤ divisibleCocycles LT := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨LY, φ, hφ, y, _, rfl⟩
    exact push_mem_Z1D hopen LY LT φ hφ y
  have hSk : ∀ s ∈ S, ((PD.p : O) ^ e) • s ∈ H := by
    intro s hs
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨LY, φ, hφ, y, hy, rfl⟩
      exact absorption_all PD hO h1 h2 h4 h6 hH LY φ hφ y hy
    · rw [smul_zero]; exact H.zero_mem
    · intro a b _ _ ha hb
      rw [smul_add]; exact H.add_mem ha hb
    · intro a b _ hb
      rw [smul_comm]; exact H.smul_mem a hb
  let S₀ : Submodule O ↥(divisibleCocycles LT) := S.comap (divisibleCocycles LT).subtype
  have hkill : ∀ s ∈ S₀, ((PD.p : O) ^ e) • s ∈ annih pr (latticeFiniteCohomology PD LT') := by
    intro s hs
    rw [hann]
    exact hSk s.1 hs
  have hle1 := Formalism.RepresentationBoundsCohomology.LOC.locTorsDual O ↥(divisibleCocycles LT) (LatticeCohomology LT') pr (latticeFiniteCohomology PD LT') S₀ ((PD.p : O) ^ e)
    hkill
  have : Module.Finite O (LatticeCohomology LT') := h5 LL O hO U' LT'
  have : IsNoetherian O (LatticeCohomology LT') := isNoetherian_of_isNoetherianRing_of_finite O _
  obtain ⟨N, δ, hδ⟩ := tors_range PD LT'
  have hle2 := Formalism.RepresentationBoundsCohomology.LOC.locQuotLen O ↥(latticeFiniteCohomology PD LT') (finrank O ↥LT'.T) N δ hδ PD.p e
  have hrk : finrank O ↥LT'.T = finrank O ↥LT.T := by
    rw [finrank_lat (LL := LL) LT'.T LT'.fg LT'.span, finrank_lat (LL := LL) LT.T LT.fg LT.span]
    exact hTT'.1.2.2.2.symm

  let incl : ↥S₀ →ₗ[O] ↥(S ⊔ H) :=
    LinearMap.codRestrict (S ⊔ H) ((divisibleCocycles LT).subtype ∘ₗ S₀.subtype)
      (fun s => Submodule.mem_sup_left s.2)
  have hincl : (annih pr (latticeFiniteCohomology PD LT')).comap S₀.subtype ≤
      (H.comap (S ⊔ H).subtype).comap incl := by
    intro s hs
    rw [hann] at hs
    exact hs
  have hsurj : Function.Surjective (Submodule.mapQ _ _ incl hincl) := by
    intro x
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨s, hs, h, hh, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨Submodule.Quotient.mk ⟨⟨s, hS hs⟩, hs⟩, ?_⟩
    rw [Submodule.mapQ_apply]
    refine (Submodule.Quotient.eq _).2 ?_
    show s - (s + h) ∈ H
    rw [sub_add_cancel_left]
    exact H.neg_mem hh
  have hle0 : lenMod S H ≤ _ := Module.length_le_of_surjective _ hsurj
  have hk : lenOl PD (O := O) ≠ ⊤ := length_quot_ne_top _ (p_ne_zero PD LL)
  obtain ⟨k, hk'⟩ := ENat.ne_top_iff_exists.1 hk
  have hfin : lenMod S H ≤ ((finrank O ↥(latticeFiniteCohomology PD LT') + finrank O ↥LT.T : ℕ) : ℕ∞) *
      ((e : ℕ∞) * (k : ℕ∞)) := by
    refine (hle0.trans hle1).trans ?_
    rw [hrk] at hle2
    rw [hk']
    exact hle2
  have hm : lenMod S H ≠ ⊤ := by
    intro h
    rw [h] at hfin
    exact absurd (top_le_iff.1 hfin) (by exact_mod_cast ENat.natCast_ne_top _)
  obtain ⟨m, hm'⟩ := ENat.ne_top_iff_exists.1 hm
  refine ⟨m, k, hm'.symm, hk'.symm, ?_⟩
  rw [← hm'] at hfin
  have : m ≤ (finrank O ↥(latticeFiniteCohomology PD LT') + finrank O ↥LT.T) * (e * k) := by exact_mod_cast hfin
  calc m ≤ _ := this
    _ = _ := by ring

end Asm

section Final

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem absorption_over_period (h1 : bkACore PD) (h2 : bkBCore PD) (h4 : cycIntCore PD)
    (h6 : drDualCore PD) : ArcTheoremGlobal PD := by
  intro LL _ _ _ O _ _ hO V X U X' U' χ PX PU LT LT' e hH LY φ hφ y hy
  obtain ⟨⟨hD, hV, hF⟩, _, _, hR, _⟩ := id hO
  exact absorption_all PD hO h1 h2 h4 h6 hH LY φ hφ y hy

theorem length_bound_over_period (h1 : bkACore PD) (h2 : bkBCore PD) (h3 : LocalTateTopDegree PD)
    (h4 : cycIntCore PD) (h5 : TateFiniteness PD) (h6 : drDualCore PD) : PushoutSpanLengthBound PD := by
  intro LL _ _ _ O _ _ hO V X U X' U' χ PX PU LT LT' e hH
  obtain ⟨⟨hD, hV, hF⟩, _, _, hR, _⟩ := id hO
  exact equivariant_coefficient_reproduced PD hO h1 h2 h3 h4 h5 h6 hH

end Final

section Cyc

variable {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL]

theorem mem_of_pow_bdd (a : O) (ha : a ≠ 0) (u : LL)
    (h : ∀ k : ℕ, ∃ b : O, algebraMap O LL a * u ^ k = algebraMap O LL b) :
    ∃ b : O, u = algebraMap O LL b := by
  let S := Algebra.adjoin O ({u} : Set LL)
  have hle : Subalgebra.toSubmodule S ≤ Submodule.span O {(algebraMap O LL a)⁻¹} := by
    intro z hz
    have hz' : z ∈ Algebra.adjoin O ({u} : Set LL) := hz
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz'
    obtain ⟨q, rfl⟩ := hz'
    show Polynomial.aeval u q ∈ _
    rw [Polynomial.aeval_eq_sum_range]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨b, hb⟩ := h k
    have ha0 : algebraMap O LL a ≠ 0 := by
      intro h0
      exact ha ((IsFractionRing.injective O LL) (by rw [h0, map_zero]))
    have hu : u ^ k = b • (algebraMap O LL a)⁻¹ := by
      rw [Algebra.smul_def, ← hb]
      field_simp
    rw [hu, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hfg : (Subalgebra.toSubmodule S).FG := by
    haveI : IsNoetherian O (Submodule.span O {(algebraMap O LL a)⁻¹}) :=
      isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span_singleton _)
    exact isNoetherian_submodule.mp inferInstance _ hle
  have hint : IsIntegral O u := IsIntegral.of_mem_of_fg S hfg u (Algebra.self_mem_adjoin_singleton O u)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨y, hy.symm⟩

end Cyc

section CycTop

variable {l : ℕ} [Fact l.Prime] {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem zl_int (hO : GoodO (Qp := ℚ_[l]) LL O) (c : ℚ_[l]) (hc : ‖c‖ ≤ 1) :
    ∃ b : O, algebraMap ℚ_[l] LL c = algebraMap O LL b := by
  obtain ⟨⟨hD, hV, hF⟩, _, hM, hR, hopen⟩ := hO
  have hcont : Continuous (algebraMap ℚ_[l] LL) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] LL)
  have hU : IsOpen ((algebraMap ℚ_[l] LL) ⁻¹' Set.range (algebraMap O LL)) := hopen.preimage hcont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 ⟨0, by simp⟩
  have hl : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hl
  have hmem : ∀ k : ℕ, ∃ b : O, algebraMap O LL b = algebraMap ℚ_[l] LL ((l : ℚ_[l]) ^ n * c ^ k) := by
    intro k
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow, norm_pow]
    calc ‖(l : ℚ_[l])‖ ^ n * ‖c‖ ^ k ≤ ‖(l : ℚ_[l])‖ ^ n * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hc) (by positivity)
      _ < ε := by rwa [mul_one]
  obtain ⟨a, ha⟩ := hmem 0
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, pow_zero, mul_one] at ha
    exact pow_ne_zero n hl0 ((map_eq_zero _).1 ha.symm)
  refine mem_of_pow_bdd a ha0 _ fun k => ?_
  obtain ⟨b, hb⟩ := hmem k
  refine ⟨b, ?_⟩
  rw [hb, ha, pow_zero, mul_one, map_mul, map_pow, map_pow]

end CycTop

end Br

theorem frobenius_lifting (D : Formalism.BasicNotions.D7) : Stmt D := by
  rintro ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨fun l _ K => Br.absorption_over_period _ (h1 l K) (h2 l K) (h4 l K) (h6 l K),
    fun l _ K => Br.length_bound_over_period _ (h1 l K) (h2 l K) (h3 l K) (h4 l K) (h5 l K) (h6 l K)⟩

theorem low_degree_admissible_holds (D : Formalism.BasicNotions.D7) : ArchimedeanSignatureMatching D := by
  intro l _ K LL _ _ _ O _ _ hO
  have hχ : ∀ g, ∃ b : O, ((cycLL ((D.loc l).PD K) LL g : LLˣ) : LL) = algebraMap O LL b := by
    intro g
    refine Br.zl_int hO _ ?_
    rw [(D.loc l).PD_χ K g]
    obtain ⟨a, ha, _⟩ := (D.loc l).χQ_cyc (g : Formalism.BasicNotions.Loc.GQ l) 0 1 (one_pow _)
    have h1 : (((D.loc l).χQ (g : Formalism.BasicNotions.Loc.GQ l) : ℚ_[l]ˣ) : ℚ_[l]) =
        ((((D.loc l).χQ (g : Formalism.BasicNotions.Loc.GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l]) := by
      ring
    rw [h1]
    refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
    · simpa using ha
    · exact_mod_cast Padic.norm_int_le_one (a : ℤ)
  obtain ⟨⟨hD, hV, hF⟩, _⟩ := id hO
  refine ⟨⟨LinearMap.range (Algebra.linearMap O LL), ?_, ?_, ?_, ?_⟩, rfl⟩
  · rintro g _ ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := hχ g
    refine ⟨b * x, ?_⟩
    show algebraMap O LL (b * x) = ((cycLL ((D.loc l).PD K) LL g : LLˣ) : LL) • algebraMap O LL x
    rw [map_mul, hb, smul_eq_mul]
  · rw [← Submodule.map_top]
    exact Submodule.FG.map _ Module.Finite.fg_top
  · exact Module.Free.of_equiv
      (LinearEquiv.ofInjective (Algebra.linearMap O LL) (IsFractionRing.injective O LL))
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL
        ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h1

theorem ramification_two_and_conjugation_at_q_and_d (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (h2 : adm2 D) (h6 : adm6 D) : Conclusion1 D :=
  fun l _ K => Br.absorption_over_period _ (h1 l K) (h2 l K) (low_degree_admissible_holds D l K) (h6 l K)

theorem second_proposition_every_localisation (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (h2 : adm2 D) (h3 : adm3 D) (h5 : adm5 D)
    (h6 : adm6 D) : Conclusion2 D :=
  fun l _ K => Br.length_bound_over_period _ (h1 l K) (h2 l K) (h3 l K) (low_degree_admissible_holds D l K) (h5 l K) (h6 l K)

end Formalism.MainNotions.BlochKatoDuality
