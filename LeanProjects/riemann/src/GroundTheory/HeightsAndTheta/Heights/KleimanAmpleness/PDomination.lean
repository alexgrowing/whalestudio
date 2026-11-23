import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace Domination

section Charts

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}

theorem mem_twistMod_zero_iff {R : Type*} [CommRing R] [Algebra R Ω] {y : Fin (N' + 1) → Ω}
    (J : Chart y) (z : Ω) : z ∈ twistMod R y 0 J ↔ z ∈ chartRing R y J := by
  obtain ⟨j, hj⟩ := J.2.1
  rw [twistMod_eq_span 0 J hj, zpow_zero, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [chartRing_smul_def, mul_one]
    exact a.2
  · intro hz
    exact ⟨⟨z, hz⟩, by rw [chartRing_smul_def, mul_one]⟩

abbrev pullPow (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω) (n : ℕ) (J : Chart x') :
    Submodule (chartRing S x' J) Ω :=
  ((pullSys (S := S) x x').pow n).sub J

theorem pullPow_succ (n : ℕ) (J : Chart x') :
    pullPow (S := S) x x' (n + 1) J = Submodule.span _ {z | ∃ q ∈ (pullSys (S := S) x x').sub J,
      ∃ y ∈ pullPow (S := S) x x' n J, z = q • y} := rfl

theorem mem_pullPow_zero_iff (J : Chart x') (z : Ω) :
    z ∈ pullPow (S := S) x x' 0 J ↔ z ∈ chartRing S x' J :=
  mem_twistMod_zero_iff J z

theorem coord_mem_pullPow_one (J : Chart x') (l : Fin (N + 1)) : x l ∈ pullPow (S := S) x x' 1 J := by
  rw [pullPow_succ]
  exact Submodule.subset_span ⟨x l, Submodule.subset_span ⟨l, rfl⟩, 1,
    (mem_pullPow_zero_iff J 1).mpr (one_mem _), by rw [smul_eq_mul, mul_one]⟩

theorem mul_mem_pullPow (J : Chart x') {n : ℕ} {z : Ω} (hz : z ∈ pullPow (S := S) x x' n J) :
    ∀ (m : ℕ) {y : Ω}, y ∈ pullPow (S := S) x x' m J → z * y ∈ pullPow (S := S) x x' (n + m) J := by
  intro m
  induction m with
  | zero =>
    intro y hy
    have hy' := (mem_pullPow_zero_iff J y).mp hy
    have h : z * y = (⟨y, hy'⟩ : chartRing S x' J) • z := by
      rw [chartRing_smul_def, mul_comm]
    rw [h]
    exact Submodule.smul_mem _ _ hz
  | succ m ih =>
    intro y hy
    rw [pullPow_succ] at hy
    rw [← Nat.add_assoc, pullPow_succ]
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨q, hq, y', hy', rfl⟩ := hw
      refine Submodule.subset_span ⟨q, hq, z * y', ih hy', ?_⟩
      simp only [smul_eq_mul]
      ring
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have h : z * (c • a) = c • (z * a) := by simp only [chartRing_smul_def]; ring
      rw [h]
      exact Submodule.smul_mem _ _ ha

theorem pow_mem_pullPow (J : Chart x') (l : Fin (N + 1)) :
    ∀ n : ℕ, x l ^ n ∈ pullPow (S := S) x x' n J
  | 0 => by rw [pow_zero]; exact (mem_pullPow_zero_iff J 1).mpr (one_mem _)
  | n + 1 => by
    rw [pow_succ]
    exact mul_mem_pullPow J (pow_mem_pullPow J l n) 1 (coord_mem_pullPow_one J l)

theorem mem_ampleChart_iff (J : Chart x') (l : Fin (N + 1)) (a : Ω) :
    a ∈ ampleChart (pullSys (S := S) x x') 1 (x l) J ↔ ∃ n : ℕ, a * x l ^ n ∈ pullPow (S := S) x x' n J := by
  simp only [ampleChart, one_mul, Set.mem_ofPred_eq]

def ampleSub (J : Chart x') (l : Fin (N + 1)) : Subalgebra S Ω where
  carrier := ampleChart (pullSys (S := S) x x') 1 (x l) J
  mul_mem' := by
    intro a b ha hb
    rw [mem_ampleChart_iff] at ha hb ⊢
    obtain ⟨n, hn⟩ := ha
    obtain ⟨m, hm⟩ := hb
    refine ⟨n + m, ?_⟩
    have h := mul_mem_pullPow J hn m hm
    rw [show a * x l ^ n * (b * x l ^ m) = a * b * x l ^ (n + m) by ring] at h
    exact h
  add_mem' := by
    intro a b ha hb
    rw [mem_ampleChart_iff] at ha hb ⊢
    obtain ⟨n, hn⟩ := ha
    obtain ⟨m, hm⟩ := hb
    refine ⟨n + m, ?_⟩
    have h1 := mul_mem_pullPow J hn m (pow_mem_pullPow J l m)
    have h2 := mul_mem_pullPow J hm n (pow_mem_pullPow J l n)
    rw [Nat.add_comm m n] at h2
    have h := Submodule.add_mem _ h1 h2
    rw [show a * x l ^ n * x l ^ m + b * x l ^ m * x l ^ n = (a + b) * x l ^ (n + m) by ring] at h
    exact h
  algebraMap_mem' s := by
    show _ ∈ ampleChart _ _ _ _
    rw [mem_ampleChart_iff]
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, mem_pullPow_zero_iff]
    exact Subalgebra.algebraMap_mem _ s

theorem chartRing_eq_ampleBase {i : Fin (N + 1)} (hi : x i ≠ 0) :
    chartRing S x (singleChart hi) = ampleBase (S := S) x i := by
  apply le_antisymm
  · intro a ha
    exact mem_ampleBase_of_mem_chartRing hi ha
  · rw [ampleBase, Algebra.adjoin_le_iff]
    rintro _ ⟨l, rfl⟩
    exact (ratio (S := S) hi l).2

theorem isNoetherianRing_chartRing [IsNoetherianRing S] {i : Fin (N + 1)} (hi : x i ≠ 0) :
    IsNoetherianRing (chartRing S x (singleChart hi)) := by
  classical
  have hfg : (chartRing S x (singleChart hi)).FG := by
    rw [chartRing_eq_ampleBase hi, ampleBase]
    refine ⟨Finset.univ.image fun l => x l / x i, ?_⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have : Algebra.FiniteType S (chartRing S x (singleChart hi)) := ⟨(Subalgebra.fg_top _).mpr hfg⟩
  exact Algebra.FiniteType.isNoetherianRing S _

variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)

theorem mem_chartRing_base_of_mem (z : Ω) (hz : z ∈ chartRing S x' (singleChart hj)) :
    z ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) := by
  have h := mem_ampleBase_of_mem_chartRing (S := S) hj hz
  rw [ampleBase] at h
  clear hz
  induction h using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨k, rfl⟩ := hz
    exact (ratio (S := chartRing S x (singleChart hi)) hj k).2
  | algebraMap s =>
    exact Subalgebra.algebraMap_mem _ (algebraMap S (chartRing S x (singleChart hi)) s)
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem mem_chartRing_base_of_base (z : Ω) (hz : z ∈ chartRing S x (singleChart hi)) :
    z ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) :=
  Subalgebra.algebraMap_mem _ (⟨z, hz⟩ : chartRing S x (singleChart hi))

theorem div_mem_of_mem_pullPow : ∀ (n : ℕ) {y : Ω}, y ∈ pullPow (S := S) x x' n (singleChart hj) →
    y / x i ^ n ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj)
  | 0, y, hy => by
    rw [pow_zero, div_one]
    exact mem_chartRing_base_of_mem hi hj y ((mem_pullPow_zero_iff _ y).mp hy)
  | n + 1, y, hy => by
    rw [pullPow_succ] at hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨q, hq, y', hy', rfl⟩ := hw
      change q ∈ Submodule.span _ (Set.range x) at hq
      have hq' : q / x i ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) := by
        induction hq using Submodule.span_induction with
        | mem q hq =>
          obtain ⟨l, rfl⟩ := hq
          exact mem_chartRing_base_of_base hi hj _ (ratio (S := S) hi l).2
        | zero => rw [zero_div]; exact zero_mem _
        | add a b _ _ ha hb => rw [add_div]; exact add_mem ha hb
        | smul c a _ ha =>
          rw [chartRing_smul_def, mul_div_assoc]
          exact mul_mem (mem_chartRing_base_of_mem hi hj _ c.2) ha
      have h := mul_mem hq' (div_mem_of_mem_pullPow n hy')
      rw [smul_eq_mul, pow_succ]
      rwa [div_mul_div_comm, mul_comm (x i) (x i ^ n)] at h
    | zero => rw [zero_div]; exact zero_mem _
    | add a b _ _ ha hb => rw [add_div]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [chartRing_smul_def, mul_div_assoc]
      exact mul_mem (mem_chartRing_base_of_mem hi hj _ c.2) ha

theorem mem_ampleChart_single_iff (a : Ω) :
    a ∈ ampleChart (pullSys (S := S) x x') 1 (x i) (singleChart hj) ↔
      a ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) := by
  constructor
  · intro ha
    rw [mem_ampleChart_iff] at ha
    obtain ⟨n, hn⟩ := ha
    have h := div_mem_of_mem_pullPow hi hj n hn
    rwa [mul_div_assoc, div_self (pow_ne_zero n hi), mul_one] at h
  · intro ha
    have hA : chartRing S x (singleChart hi) ≤ ampleSub (S := S) (x := x) (singleChart hj) i := by
      rw [chartRing_eq_ampleBase hi, ampleBase, Algebra.adjoin_le_iff]
      rintro _ ⟨l, rfl⟩
      show _ ∈ ampleChart _ _ _ _
      rw [mem_ampleChart_iff]
      refine ⟨1, ?_⟩
      rw [pow_one, div_mul_cancel₀ _ hi]
      exact coord_mem_pullPow_one _ l
    have h := mem_ampleBase_of_mem_chartRing (S := chartRing S x (singleChart hi)) hj ha
    rw [ampleBase] at h
    clear ha
    induction h using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      rw [mem_ampleChart_iff]
      refine ⟨0, ?_⟩
      rw [pow_zero, mul_one, mem_pullPow_zero_iff]
      exact (ratio (S := S) hj k).2
    | algebraMap a0 => exact hA a0.2
    | add a b _ _ ha hb => exact (ampleSub (S := S) (x := x) (singleChart hj) i).add_mem ha hb
    | mul a b _ _ ha hb => exact (ampleSub (S := S) (x := x) (singleChart hj) i).mul_mem ha hb

theorem mem_domRing_iff (b : Ω) : b ∈ domRing S x x' i ↔
    ∀ J : Chart x', b ∈ chartRing (chartRing S x (singleChart hi)) x' J := by
  rw [domRing, ampleRing, Set.mem_iInter]
  constructor
  · intro hb J
    obtain ⟨j, hjJ⟩ := J.2.1
    have hj : x' j ≠ 0 := (mem_support x').mp (J.2.2 hjJ)
    have h1 := (mem_ampleChart_single_iff hi hj b).mp (hb (singleChart hj))
    exact chartRing_mono (Finset.singleton_subset_iff.mpr hjJ) h1
  · intro hb J
    obtain ⟨j, hjJ⟩ := J.2.1
    have hj : x' j ≠ 0 := (mem_support x').mp (J.2.2 hjJ)
    have h1 := (mem_ampleChart_single_iff hi hj b).mpr (hb (singleChart hj))
    rw [mem_ampleChart_iff] at h1 ⊢
    obtain ⟨n, hn⟩ := h1
    exact ⟨n, ((pullSys (S := S) x x').pow n).mono _ _ (Finset.singleton_subset_iff.mpr hjJ) _ hn⟩

omit [Algebra S Ω] in

theorem mem_secs_twistBundle_zero_iff {R : Type*} [CommRing R] [Algebra R Ω] (z : Ω) :
    z ∈ (twistBundle R x' 0).secs ↔ ∀ J : Chart x', z ∈ chartRing R x' J := by
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
  exact forall_congr' fun J => mem_twistMod_zero_iff J z

variable (x') in

def domSub : Subalgebra (chartRing S x (singleChart hi)) Ω :=
  ⨅ J : Chart x', chartRing (chartRing S x (singleChart hi)) x' J

theorem mem_domSub_iff (b : Ω) : b ∈ domSub (S := S) x' hi ↔ b ∈ domRing S x x' i := by
  rw [domSub, Algebra.mem_iInf, mem_domRing_iff hi]

theorem fg_domSub [IsNoetherianRing S] (hF : FiniteSections.Statement.{w, w}) (hx' : x' ≠ 0) :
    (Subalgebra.toSubmodule (domSub (S := S) x' hi)).FG := by
  have := isNoetherianRing_chartRing (S := S) hi
  have h := (hF (chartRing S x (singleChart hi)) Ω N' x' (twistBundle _ x' 0) hx').1
  rw [Module.Finite.iff_fg] at h
  have heq : Subalgebra.toSubmodule (domSub (S := S) x' hi) = (twistBundle _ x' 0).secs := by
    ext z
    rw [Subalgebra.mem_toSubmodule, mem_secs_twistBundle_zero_iff, domSub, Algebra.mem_iInf]
  rw [heq]
  exact h

end Charts

section Clauses

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}

theorem exists_clear {A : Subalgebra S Ω} {B : Submodule A Ω} (hB : B.FG) (P : Set Ω) (hP1 : (1 : Ω) ∈ P)
    (hPmul : ∀ a ∈ P, ∀ b ∈ P, a * b ∈ P) (hPA : ∀ a ∈ P, a ∈ A)
    (h : ∀ g ∈ B, ∃ d ∈ P, d * g ∈ A) : ∃ d ∈ P, ∀ b ∈ B, d * b ∈ A := by
  classical
  obtain ⟨t, ht⟩ := hB
  have h' : ∀ g : t, ∃ d ∈ P, d * (g : Ω) ∈ A := fun g =>
    h g (by rw [← ht]; exact Submodule.subset_span (Finset.mem_coe.mpr g.2))
  choose d hdP hdA using h'
  refine ⟨∏ g, d g, Finset.prod_induction _ (· ∈ P) (fun a b ha hb => hPmul a ha b hb) hP1
    fun g _ => hdP g, ?_⟩
  intro b hb
  rw [← ht] at hb
  induction hb using Submodule.span_induction with
  | mem g hg =>
    have hg' : g ∈ t := Finset.mem_coe.mp hg
    rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ ⟨g, hg'⟩),
      show ∀ p q r : Ω, p * q * r = q * (p * r) from fun p q r => by ring]
    exact A.mul_mem (Finset.prod_induction _ (· ∈ A) (fun a b ha hb => A.mul_mem ha hb) A.one_mem
      fun g' _ => hPA _ (hdP g')) (hdA ⟨g, hg'⟩)
  | zero => rw [mul_zero]; exact A.zero_mem
  | add a b _ _ ha hb => rw [mul_add]; exact A.add_mem ha hb
  | smul c a _ ha =>
    change (∏ g, d g) * ((c : Ω) * a) ∈ A
    rw [mul_left_comm]
    exact A.mul_mem c.2 ha

theorem mul_mem_secs_of_pullSecs {L L' : SubSystem S x Ω} {κ : Ω}
    (h : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∀ b ∈ domRing S x x' i, ∀ l ∈ L.sub (singleChart hi),
      κ * (b * l) ∈ L'.sub (singleChart hi)) :
    ∀ z ∈ pullSecs x' L, κ * z ∈ L'.secs := by
  intro z hz
  simp only [pullSecs, Submodule.mem_iInf] at hz
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
  intro I
  obtain ⟨i, hiI⟩ := I.2.1
  have hi : x i ≠ 0 := (mem_support x).mp (I.2.2 hiI)
  refine L'.mono (singleChart hi) I (Finset.singleton_subset_iff.mpr hiI) _ ?_
  have hz' := hz i hi
  clear hz
  induction hz' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, l, hl, rfl⟩ := hw
    exact h i hi b hb l hl
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | smul s a _ ha =>
    rw [mul_smul_comm]
    exact Submodule.smul_of_tower_mem _ s ha

omit [Algebra S Ω] in

theorem ne_zero_of_isBirationalPt [Algebra S Ω] {y : Fin (N' + 1) → Ω} (h : IsBirationalPt S y) :
    y ≠ 0 := by
  obtain ⟨I, -⟩ := h 0
  obtain ⟨j, hj⟩ := I.2.1
  intro hy
  exact (mem_support y).mp (I.2.2 hj) (by rw [hy]; rfl)

theorem birational_clear (hbir : IsBirationalPt S x) {i : Fin (N + 1)} (hi : x i ≠ 0) (g : Ω) :
    ∃ d ∈ {y | ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ aeval x f ≠ 0 ∧ aeval x f / x i ^ e = y},
      d * g ∈ chartRing S x (singleChart hi) := by
  obtain ⟨I, a, b, ⟨f, s, e, hs, hf, hse, rfl⟩, ⟨f', s', e', hs', hf', hse', rfl⟩, hb0, hgb⟩ := hbir g
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hs0' := eval_ne_zero_of_mem_monos I hs'
  have hf'0 : aeval x f' ≠ 0 := by
    intro h
    apply hb0
    rw [h, zero_div]
  have key : aeval x s * aeval x f' * g = aeval x f * aeval x s' := by
    calc aeval x s * aeval x f' * g
        = aeval x s * aeval x s' * (g * (aeval x f' / aeval x s')) := by
          field_simp
      _ = aeval x s * aeval x s' * (aeval x f / aeval x s) := by rw [hgb]
      _ = aeval x f * aeval x s' := by
          field_simp
  refine ⟨aeval x (s * f') / x i ^ (e + e'),
    ⟨s * f', e + e', hse.mul hf', by rw [map_mul]; exact mul_ne_zero hs0 hf'0, rfl⟩, ?_⟩
  refine ⟨f * s', X i ^ (e + e'), e + e', pow_mem (X_mem_monos (Finset.mem_singleton_self i)) _,
    hf.mul hse', isHomogeneous_X_pow i _, ?_⟩
  rw [map_pow, aeval_X, map_mul, map_mul, div_mul_eq_mul_div, key]

end Clauses

theorem Generic.proof (hF : FiniteSections.Statement.{w, w}) : Generic.Statement.{u, w} := by
  intro S _ _ _ Ω _ _ N N' x x' hx' _ hcl
  classical
  have key : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ m : S, algebraMap S Ω m ≠ 0 ∧
      ∀ b ∈ domRing S x x' i, algebraMap S Ω m * b ∈ chartRing S x (singleChart hi) := by
    intro i hi
    obtain ⟨d, ⟨m, hm0, rfl⟩, hd⟩ := exists_clear (A := chartRing S x (singleChart hi))
      (fg_domSub hi hF hx') {y | ∃ s : S, algebraMap S Ω s ≠ 0 ∧ algebraMap S Ω s = y}
      ⟨1, by simp, by simp⟩
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact ⟨a * b, by rw [map_mul]; exact mul_ne_zero ha hb, map_mul _ _ _⟩)
      (by
        rintro _ ⟨a, -, rfl⟩
        exact Subalgebra.algebraMap_mem _ a)
      (fun g hg => by
        obtain ⟨s, hs0, hs⟩ := hcl i hi g ((mem_domSub_iff hi g).mp hg)
        exact ⟨_, ⟨s, hs0, rfl⟩, hs⟩)
    exact ⟨m, hm0, fun b hb => hd b ((mem_domSub_iff hi b).mpr hb)⟩
  choose m hm0 hm using key
  have hM : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∀ b ∈ domRing S x x' i,
      algebraMap S Ω (∏ j : {i // x i ≠ 0}, m j.1 j.2) * b ∈ chartRing S x (singleChart hi) := by
    intro i hi b hb
    rw [← Finset.mul_prod_erase Finset.univ (fun j : {i // x i ≠ 0} => m j.1 j.2)
      (Finset.mem_univ ⟨i, hi⟩), map_mul, mul_comm (algebraMap S Ω _) (algebraMap S Ω _), mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hm i hi b hb)
  refine ⟨∏ j : {i // x i ≠ 0}, m j.1 j.2, ?_, hM, fun L n z hz => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hm0 j.1 j.2
  · refine mul_mem_secs_of_pullSecs (fun i hi b hb l hl => ?_) z hz
    rw [← mul_assoc]
    exact Submodule.smul_mem _ (⟨_, hM i hi b hb⟩ : chartRing S x (singleChart hi)) hl

theorem Normal.proof (hF : FiniteSections.Statement.{w, w}) : Normal.Statement.{u, w} := by
  intro S _ _ Ω _ _ N N' x x' _ _ hbir' hnorm
  have hx' : x' ≠ 0 := ne_zero_of_isBirationalPt hbir'
  have key : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0),
      domRing S x x' i = (chartRing S x (singleChart hi) : Set Ω) := by
    intro i hi
    ext b
    constructor
    · intro hb
      exact hnorm i hi b (IsIntegral.of_mem_of_fg _ (fg_domSub hi hF hx') b
        ((mem_domSub_iff hi b).mpr hb))
    · intro hb
      exact (mem_domRing_iff hi b).mpr fun J =>
        Subalgebra.algebraMap_mem _ (⟨b, hb⟩ : chartRing S x (singleChart hi))
  refine ⟨key, fun L n => ?_⟩
  intro z hz
  have h := mul_mem_secs_of_pullSecs (κ := 1) (L := L.pow n) (L' := L.pow n)
    (fun i hi b hb l hl => by
      rw [one_mul]
      have hb' : b ∈ chartRing S x (singleChart hi) := by
        rw [key i hi] at hb
        exact hb
      exact Submodule.smul_mem _ (⟨b, hb'⟩ : chartRing S x (singleChart hi)) hl) z hz
  rwa [one_mul] at h

theorem Conductor.proof (hF : FiniteSections.Statement.{w, w}) : Conductor.Statement.{u, w} := by
  intro S _ _ Ω _ _ N N' x x' _ hbir hbir'
  classical
  have hx' : x' ≠ 0 := ne_zero_of_isBirationalPt hbir'
  have key : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧
      aeval x f ≠ 0 ∧ ∀ b ∈ domRing S x x' i, aeval x f / x i ^ e * b ∈ chartRing S x (singleChart hi) := by
    intro i hi
    obtain ⟨d, ⟨f, e, hf, hf0, rfl⟩, hd⟩ := exists_clear (A := chartRing S x (singleChart hi))
      (fg_domSub hi hF hx')
      {y | ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ aeval x f ≠ 0 ∧ aeval x f / x i ^ e = y}
      ⟨1, 0, isHomogeneous_one _ _, by simp, by simp⟩
      (by
        rintro _ ⟨f, e, hf, hf0, rfl⟩ _ ⟨f', e', hf', hf0', rfl⟩
        refine ⟨f * f', e + e', hf.mul hf', by rw [map_mul]; exact mul_ne_zero hf0 hf0', ?_⟩
        rw [map_mul, pow_add, div_mul_div_comm])
      (by
        rintro _ ⟨f, e, hf, -, rfl⟩
        exact ⟨f, X i ^ e, e, pow_mem (X_mem_monos (Finset.mem_singleton_self i)) e, hf,
          isHomogeneous_X_pow i e, by rw [map_pow, aeval_X]⟩)
      (fun g _ => birational_clear hbir hi g)
    exact ⟨f, e, hf, hf0, fun b hb => hd b ((mem_domSub_iff hi b).mpr hb)⟩
  choose f e hf hf0 hfb using key
  have hG : (∏ j : {i // x i ≠ 0}, f j.1 j.2).IsHomogeneous (∑ j : {i // x i ≠ 0}, e j.1 j.2) :=
    IsHomogeneous.prod _ _ _ fun j _ => hf j.1 j.2
  have hsplit : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ w ∈ chartRing S x (singleChart hi),
      aeval x (∏ j : {i // x i ≠ 0}, f j.1 j.2) / x i ^ (∑ j : {i // x i ≠ 0}, e j.1 j.2) =
        aeval x (f i hi) / x i ^ e i hi * w := by
    intro i hi
    have hmem := Finset.mem_univ (⟨i, hi⟩ : {i // x i ≠ 0})
    refine ⟨aeval x (∏ j ∈ Finset.univ.erase (⟨i, hi⟩ : {i // x i ≠ 0}), f j.1 j.2) /
      x i ^ (∑ j ∈ Finset.univ.erase (⟨i, hi⟩ : {i // x i ≠ 0}), e j.1 j.2),
      ⟨_, X i ^ _, _, pow_mem (X_mem_monos (Finset.mem_singleton_self i)) _,
        IsHomogeneous.prod _ _ _ fun (j : {i // x i ≠ 0}) _ => hf j.1 j.2, isHomogeneous_X_pow i _,
        by rw [map_pow, aeval_X]⟩, ?_⟩
    rw [← Finset.mul_prod_erase _ (fun j : {i // x i ≠ 0} => f j.1 j.2) hmem,
      ← Finset.add_sum_erase _ (fun j : {i // x i ≠ 0} => e j.1 j.2) hmem, map_mul, pow_add,
      div_mul_div_comm]
  refine ⟨∑ j : {i // x i ≠ 0}, e j.1 j.2, aeval x (∏ j : {i // x i ≠ 0}, f j.1 j.2), ?_, ?_, ?_⟩
  · simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
    intro I
    exact Submodule.subset_span ⟨_, 1, 0, _, one_mem _, hG, isHomogeneous_one _ _, by simp,
      by rw [map_one, div_one]⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hf0 j.1 j.2
  · intro L n z hz
    refine mul_mem_secs_of_pullSecs (fun i hi b hb l hl => ?_) z hz
    refine Submodule.subset_span ⟨_ * b, ?_, l, hl, by rw [smul_eq_mul, mul_assoc]⟩
    change _ ∈ twistMod S x _ (singleChart hi)
    rw [twistMod_eq_span _ (singleChart hi) (Finset.mem_singleton_self i), Submodule.mem_span_singleton]
    obtain ⟨w, hw, hw'⟩ := hsplit i hi
    have hmem : aeval x (∏ j : {i // x i ≠ 0}, f j.1 j.2) / x i ^ (∑ j : {i // x i ≠ 0}, e j.1 j.2) * b ∈
        chartRing S x (singleChart hi) := by
      rw [hw', show ∀ p q r : Ω, p * q * r = q * (p * r) from fun p q r => by ring]
      exact mul_mem hw (hfb i hi b hb)
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [chartRing_smul_def, zpow_natCast]
    field_simp

theorem proof (hF : FiniteSections.Statement.{w, w}) : Domination.Statement.{u, w} :=
  ⟨Generic.proof hF, Normal.proof hF, Conductor.proof hF⟩

end Domination

end

end GroundTheory.Heights₂.Heights.Kleiman
