import Mathlib
import GroundTheory.LocalFields.FilteredSurj

namespace GroundTheory.LocalField

open Finset Filter

section Tate

variable (G M : Type*) [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]

def tateNorm : M →* M where
  toFun x := ∏ g : G, g • x
  map_one' := by simp
  map_mul' x y := by simp only [smul_mul', prod_mul_distrib]

theorem tateNorm_apply (x : M) : tateNorm G M x = ∏ g : G, g • x := rfl

def invariants : Subgroup M where
  carrier := {x | ∀ g : G, g • x = x}
  one_mem' g := smul_one g
  mul_mem' {x y} hx hy g := by rw [smul_mul', hx g, hy g]
  inv_mem' {x} hx g := by rw [smul_inv', hx g]

omit [Fintype G] in
theorem mem_invariants {x : M} : x ∈ invariants G M ↔ ∀ g : G, g • x = x := Iff.rfl

def augmentation : Subgroup M :=
  Subgroup.closure {y | ∃ (g : G) (x : M), g • x / x = y}

abbrev TateZero : Type _ :=
  invariants G M ⧸ (tateNorm G M).range.subgroupOf (invariants G M)

abbrev TateNegOne : Type _ :=
  (tateNorm G M).ker ⧸ (augmentation G M).subgroupOf (tateNorm G M).ker

def augMap : (G → M) →* M where
  toFun m := ∏ g : G, g • m g / m g
  map_one' := by simp
  map_mul' m m' := by
    simp only [Pi.mul_apply, smul_mul', ← prod_mul_distrib, div_mul_div_comm]

theorem augMap_apply (m : G → M) : augMap G M m = ∏ g : G, g • m g / m g := rfl

variable {G M}

theorem smul_tateNorm (g : G) (x : M) : g • tateNorm G M x = tateNorm G M x := by
  rw [tateNorm_apply, Finset.smul_prod']
  simp_rw [smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

theorem tateNorm_smul (g : G) (x : M) : tateNorm G M (g • x) = tateNorm G M x := by
  simp_rw [tateNorm_apply, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

theorem tateNorm_mem_invariants (x : M) : tateNorm G M x ∈ invariants G M :=
  fun g => smul_tateNorm g x

theorem tateNorm_augMap (m : G → M) : tateNorm G M (augMap G M m) = 1 := by
  rw [augMap_apply, map_prod]
  refine prod_eq_one fun g _ => ?_
  rw [map_div, tateNorm_smul, div_self']

theorem augmentation_eq_range : augmentation G M = (augMap G M).range := by
  classical
  apply le_antisymm
  · rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, x, rfl⟩
    refine ⟨Pi.mulSingle g x, ?_⟩
    rw [augMap_apply, Fintype.prod_eq_single g (fun h hh => by simp [Pi.mulSingle_eq_of_ne hh])]
    simp
  · rintro _ ⟨m, rfl⟩
    exact Subgroup.prod_mem _ fun g _ => Subgroup.subset_closure ⟨g, m g, rfl⟩

theorem subsingleton_tateZero_iff :
    Subsingleton (TateZero G M) ↔ ∀ x : M, (∀ g : G, g • x = x) → ∃ y, tateNorm G M y = x := by
  rw [QuotientGroup.subsingleton_iff, Subgroup.subgroupOf_eq_top]
  exact ⟨fun h x hx => h hx, fun h x hx => h x hx⟩

theorem subsingleton_tateNegOne_iff :
    Subsingleton (TateNegOne G M) ↔ ∀ x : M, tateNorm G M x = 1 → x ∈ augmentation G M := by
  rw [QuotientGroup.subsingleton_iff, Subgroup.subgroupOf_eq_top]
  exact ⟨fun h x hx => h hx, fun h x hx => h x hx⟩

end Tate

section Filtration

structure StableFiltration (G V : Type*) [Group G] [CommGroup V] [MulDistribMulAction G V] where

  F : ℕ → Subgroup V

  antitone : Antitone F

  smul_mem : ∀ (n : ℕ) (g : G) {x : V}, x ∈ F n → g • x ∈ F n

namespace StableFiltration

variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)

instance instMulDistribMulActionF (n : ℕ) : MulDistribMulAction G (S.F n) where
  smul g x := ⟨g • (x : V), S.smul_mem n g x.2⟩
  one_smul x := Subtype.ext (one_smul G (x : V))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : V))
  smul_mul g x y := Subtype.ext (smul_mul' g (x : V) y)
  smul_one g := Subtype.ext (smul_one g)

@[simp]
theorem coe_smul_F {n : ℕ} (g : G) (x : S.F n) : ((g • x : S.F n) : V) = g • (x : V) := rfl

def gr (n : ℕ) : Type _ := S.F n ⧸ (S.F (n + 1)).subgroupOf (S.F n)

instance instCommGroupGr (n : ℕ) : CommGroup (S.gr n) :=
  QuotientGroup.Quotient.commGroup _

def grMk (n : ℕ) : S.F n →* S.gr n := QuotientGroup.mk' _

theorem grMk_surjective (n : ℕ) : Function.Surjective (S.grMk n) :=
  QuotientGroup.mk'_surjective _

theorem grMk_eq_one_iff {n : ℕ} (x : S.F n) : S.grMk n x = 1 ↔ (x : V) ∈ S.F (n + 1) :=
  (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf

theorem grMk_eq_grMk_iff {n : ℕ} (x y : S.F n) :
    S.grMk n x = S.grMk n y ↔ (x : V) / y ∈ S.F (n + 1) := by
  rw [← div_eq_one, ← map_div, grMk_eq_one_iff]
  rfl

def grAct (n : ℕ) (g : G) : S.gr n →* S.gr n :=
  QuotientGroup.map _ _ (MulDistribMulAction.toMonoidHom (S.F n) g) fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
    exact S.smul_mem (n + 1) g hx

theorem grAct_grMk {n : ℕ} (g : G) (x : S.F n) : S.grAct n g (S.grMk n x) = S.grMk n (g • x) :=
  rfl

instance instMulDistribMulActionGr (n : ℕ) : MulDistribMulAction G (S.gr n) where
  smul g q := S.grAct n g q
  one_smul q := by
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    exact (S.grAct_grMk 1 x).trans (congrArg _ (one_smul G x))
  mul_smul g h q := by
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    change S.grAct n (g * h) (S.grMk n x) = S.grAct n g (S.grAct n h (S.grMk n x))
    rw [grAct_grMk, grAct_grMk, grAct_grMk, mul_smul]
  smul_mul g q r := map_mul (S.grAct n g) q r
  smul_one g := map_one (S.grAct n g)

theorem smul_grMk {n : ℕ} (g : G) (x : S.F n) : g • S.grMk n x = S.grMk n (g • x) := rfl

variable [Fintype G]

theorem coe_tateNorm_F {n : ℕ} (x : S.F n) : ((tateNorm G (S.F n) x : S.F n) : V) = tateNorm G V x := by
  rw [tateNorm_apply, tateNorm_apply, SubmonoidClass.coe_finsetProd]
  rfl

theorem coe_augMap_F {n : ℕ} (m : G → S.F n) :
    ((augMap G (S.F n) m : S.F n) : V) = augMap G V (fun g => (m g : V)) := by
  rw [augMap_apply, augMap_apply, SubmonoidClass.coe_finsetProd]
  rfl

theorem tateNorm_grMk {n : ℕ} (x : S.F n) :
    tateNorm G (S.gr n) (S.grMk n x) = S.grMk n (tateNorm G (S.F n) x) := by
  rw [tateNorm_apply, tateNorm_apply, map_prod]
  rfl

theorem augMap_grMk {n : ℕ} (m : G → S.F n) :
    augMap G (S.gr n) (fun g => S.grMk n (m g)) = S.grMk n (augMap G (S.F n) m) := by
  rw [augMap_apply, augMap_apply, map_prod]
  simp only [map_div, smul_grMk]

theorem tateNorm_mem {n : ℕ} {x : V} (hx : x ∈ S.F n) : tateNorm G V x ∈ S.F n :=
  Subgroup.prod_mem _ fun g _ => S.smul_mem n g hx

theorem augMap_mem {n : ℕ} {m : G → V} (hm : ∀ g, m g ∈ S.F n) : augMap G V m ∈ S.F n :=
  Subgroup.prod_mem _ fun g _ => Subgroup.div_mem _ (S.smul_mem n g (hm g)) (hm g)

theorem subsingleton_tateZero_gr_iff (n : ℕ) :
    Subsingleton (TateZero G (S.gr n)) ↔
      ∀ x ∈ S.F n, (∀ g : G, g • x / x ∈ S.F (n + 1)) →
        ∃ y ∈ S.F n, x / tateNorm G V y ∈ S.F (n + 1) := by
  rw [subsingleton_tateZero_iff]
  constructor
  · intro h x hx hinv
    obtain ⟨q, hq⟩ := h (S.grMk n ⟨x, hx⟩) fun g => by
      rw [smul_grMk, grMk_eq_grMk_iff]
      exact hinv g
    obtain ⟨y, rfl⟩ := S.grMk_surjective n q
    rw [tateNorm_grMk, eq_comm, grMk_eq_grMk_iff, coe_tateNorm_F] at hq
    exact ⟨y, y.2, hq⟩
  · intro h q hq
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    obtain ⟨y, hy, hxy⟩ := h x x.2 fun g => by
      have := hq g
      rw [smul_grMk, grMk_eq_grMk_iff] at this
      exact this
    refine ⟨S.grMk n ⟨y, hy⟩, ?_⟩
    rw [tateNorm_grMk, eq_comm, grMk_eq_grMk_iff, coe_tateNorm_F]
    exact hxy

theorem subsingleton_tateNegOne_gr_iff (n : ℕ) :
    Subsingleton (TateNegOne G (S.gr n)) ↔
      ∀ x ∈ S.F n, tateNorm G V x ∈ S.F (n + 1) →
        ∃ m : G → V, (∀ g, m g ∈ S.F n) ∧ x / augMap G V m ∈ S.F (n + 1) := by
  rw [subsingleton_tateNegOne_iff, augmentation_eq_range]
  constructor
  · intro h x hx hN
    obtain ⟨q, hq⟩ := h (S.grMk n ⟨x, hx⟩) (by
      rw [tateNorm_grMk, grMk_eq_one_iff, coe_tateNorm_F]
      exact hN)
    have hl : ∀ g, ∃ y, S.grMk n y = q g := fun g => S.grMk_surjective n (q g)
    choose m hm using hl
    have e : q = fun g => S.grMk n (m g) := funext fun g => (hm g).symm
    rw [e, augMap_grMk, eq_comm, grMk_eq_grMk_iff, coe_augMap_F] at hq
    exact ⟨fun g => (m g : V), fun g => (m g).2, hq⟩
  · intro h q hq
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    rw [tateNorm_grMk, grMk_eq_one_iff, coe_tateNorm_F] at hq
    obtain ⟨m, hm, hxm⟩ := h x x.2 hq
    refine ⟨fun g => S.grMk n ⟨m g, hm g⟩, ?_⟩
    rw [augMap_grMk, eq_comm, grMk_eq_grMk_iff, coe_augMap_F]
    exact hxm

end StableFiltration

end Filtration

section Complete

variable {V : Type*} [CommGroup V]

theorem filtrationComplete_pi {ι : Type*} [Fintype ι] {F : ℕ → Subgroup V}
    (hc : FiltrationComplete F) :
    FiltrationComplete fun n => Subgroup.pi Set.univ fun _ : ι => F n := by
  intro x hx
  have hxi : ∀ i, FiltrationCauchy F fun k => x k i := by
    intro i N
    obtain ⟨M, hM⟩ := hx N
    exact ⟨M, fun m hm n hn => (Subgroup.mem_pi _).mp (hM m hm n hn) i (Set.mem_univ i)⟩
  choose y hy using fun i => hc _ (hxi i)
  refine ⟨y, fun N => ?_⟩
  choose M hM using fun i => hy i N
  refine ⟨Finset.univ.sup M, fun n hn => (Subgroup.mem_pi _).mpr fun i _ => ?_⟩
  exact hM i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)

variable {G : Type*} [Group G] [Fintype G] [MulDistribMulAction G V]

theorem subsingleton_tateZero_of_complete (S : StableFiltration G V) (h0 : S.F 0 = ⊤)
    (hc : FiltrationComplete S.F) (hs : FiltrationSeparated S.F)
    (hgr : ∀ n, Subsingleton (TateZero G (S.gr n))) : Subsingleton (TateZero G V) := by
  rw [subsingleton_tateZero_iff]
  intro x hx
  let f : V →* invariants G V := (tateNorm G V).codRestrict _ tateNorm_mem_invariants
  let E : ℕ → Subgroup (invariants G V) := fun n => (S.F n).subgroupOf (invariants G V)
  have key := map_eq_of_graded_surjective (F := S.F) (E := E) S.antitone
    (fun a b hab y hy => Subgroup.mem_subgroupOf.mpr (S.antitone hab (Subgroup.mem_subgroupOf.mp hy)))
    hc (fun y hy => Subtype.ext (hs _ fun n => Subgroup.mem_subgroupOf.mp (hy n))) f tendsto_id 0
    (fun n _ y hy => Subgroup.mem_subgroupOf.mpr (S.tateNorm_mem hy))
    (fun n _ h hh => by
      have hh' : (h : V) ∈ S.F n := Subgroup.mem_subgroupOf.mp hh
      obtain ⟨y, hy, hhy⟩ := (S.subsingleton_tateZero_gr_iff n).mp (hgr n) h hh' fun g => by
        rw [h.2 g, div_self']
        exact Subgroup.one_mem _
      exact ⟨y, hy, Subgroup.mem_subgroupOf.mpr hhy⟩)
  have hx0 : (⟨x, (mem_invariants G V).mpr hx⟩ : invariants G V) ∈ (S.F 0).map f := by
    rw [key]
    change _ ∈ E 0
    rw [Subgroup.mem_subgroupOf, h0]
    exact Subgroup.mem_top _
  obtain ⟨y, -, hy⟩ := hx0
  exact ⟨y, congrArg Subtype.val hy⟩

theorem subsingleton_tateNegOne_of_complete (S : StableFiltration G V) (h0 : S.F 0 = ⊤)
    (hc : FiltrationComplete S.F) (hs : FiltrationSeparated S.F)
    (hgr : ∀ n, Subsingleton (TateNegOne G (S.gr n))) : Subsingleton (TateNegOne G V) := by
  rw [subsingleton_tateNegOne_iff, augmentation_eq_range]
  intro x hx
  let f : (G → V) →* (tateNorm G V).ker := (augMap G V).codRestrict _ tateNorm_augMap
  let P : ℕ → Subgroup (G → V) := fun n => Subgroup.pi Set.univ fun _ : G => S.F n
  let E : ℕ → Subgroup (tateNorm G V).ker := fun n => (S.F n).subgroupOf (tateNorm G V).ker
  have key := map_eq_of_graded_surjective (F := P) (E := E)
    (fun a b hab m hm => (Subgroup.mem_pi _).mpr fun g _ =>
      S.antitone hab ((Subgroup.mem_pi _).mp hm g (Set.mem_univ g)))
    (fun a b hab y hy => Subgroup.mem_subgroupOf.mpr (S.antitone hab (Subgroup.mem_subgroupOf.mp hy)))
    (filtrationComplete_pi hc)
    (fun y hy => Subtype.ext (hs _ fun n => Subgroup.mem_subgroupOf.mp (hy n))) f tendsto_id 0
    (fun n _ m hm => Subgroup.mem_subgroupOf.mpr
      (S.augMap_mem fun g => (Subgroup.mem_pi _).mp hm g (Set.mem_univ g)))
    (fun n _ h hh => by
      have hh' : (h : V) ∈ S.F n := Subgroup.mem_subgroupOf.mp hh
      have hN : tateNorm G V h ∈ S.F (n + 1) := by
        rw [h.2]
        exact Subgroup.one_mem _
      obtain ⟨m, hm, hhm⟩ := (S.subsingleton_tateNegOne_gr_iff n).mp (hgr n) h hh' hN
      exact ⟨m, (Subgroup.mem_pi _).mpr fun g _ => hm g, Subgroup.mem_subgroupOf.mpr hhm⟩)
  have hx0 : (⟨x, MonoidHom.mem_ker.mpr hx⟩ : (tateNorm G V).ker) ∈ (P 0).map f := by
    rw [key]
    change _ ∈ E 0
    rw [Subgroup.mem_subgroupOf, h0]
    exact Subgroup.mem_top _
  obtain ⟨m, -, hm⟩ := hx0
  exact ⟨m, congrArg Subtype.val hm⟩

theorem subsingleton_tate_of_complete (S : StableFiltration G V) (h0 : S.F 0 = ⊤)
    (hc : FiltrationComplete S.F) (hs : FiltrationSeparated S.F)
    (hgr0 : ∀ n, Subsingleton (TateZero G (S.gr n)))
    (hgr1 : ∀ n, Subsingleton (TateNegOne G (S.gr n))) :
    Subsingleton (TateZero G V) ∧ Subsingleton (TateNegOne G V) :=
  ⟨subsingleton_tateZero_of_complete S h0 hc hs hgr0,
    subsingleton_tateNegOne_of_complete S h0 hc hs hgr1⟩

end Complete

end GroundTheory.LocalField
