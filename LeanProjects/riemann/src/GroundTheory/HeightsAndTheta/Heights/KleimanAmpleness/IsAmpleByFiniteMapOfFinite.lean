import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ObjectsAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AmpleRingFiniteSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

noncomputable section

section Core

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem mem_of_pow_mul_mem (A : Subalgebra S Ω) {m : ℕ} (e : Fin m → Ω) (he : ∀ j, e j ∈ A)
    (hsum : ∑ j, e j = 1) (z : Ω) (hz : ∀ j, ∃ M : ℕ, e j ^ M * z ∈ A) : z ∈ A := by
  classical
  choose M hM using hz
  let e' : Fin m → A := fun j => ⟨e j, he j⟩
  have hspan : Ideal.span (Set.range e') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : A) = ∑ j, e' j := Subtype.ext (by simp [e', hsum])
    rw [h1]
    exact Ideal.sum_mem _ fun j _ => Ideal.subset_span ⟨j, rfl⟩
  have hpow := Ideal.span_pow_eq_top _ hspan (∑ j, M j)
  have hle : Ideal.span ((fun a => a ^ (∑ j, M j)) '' Set.range e') ≤ mulMemIdeal A z := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    have hj : M j ≤ ∑ j, M j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    change ((e' j ^ (∑ j, M j) : A) : Ω) * z ∈ A
    rw [SubmonoidClass.coe_pow, ← Nat.sub_add_cancel hj, pow_add, mul_assoc]
    exact A.mul_mem (A.pow_mem (he j) _) (hM j)
  rw [hpow] at hle
  have h1 : (1 : A) ∈ mulMemIdeal A z := hle Submodule.mem_top
  simpa [mulMemIdeal] using h1

theorem mem_pow_of_div_pow_mem (A : Subalgebra S Ω) (Q' : Submodule A Ω) {m : ℕ} (g : Fin m → Ω)
    (hQQ : Submodule.span A (Set.range g) * Q' = 1) (k : ℕ) (t : Ω)
    (ht : ∀ j, g j ≠ 0 → t / g j ^ k ∈ Algebra.adjoin S ((A : Set Ω) ∪ Set.range fun b => g b / g j)) :
    t ∈ Submodule.span A (Set.range g) ^ k := by
  classical
  set Q := Submodule.span A (Set.range g) with hQdef
  have hone : (1 : Ω) ∈ Q * Q' := by
    rw [hQQ]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨w, hwQ, hsum⟩ : ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = 1 := by
    refine Submodule.mul_induction_on
      (C := fun z => ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = z) hone ?_ ?_
    · intro q hq q' hq'
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hq
      refine ⟨fun b => (a b : Ω) * q', fun b => Q'.smul_mem (a b) hq', ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
    · rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
      refine ⟨w + w', fun b => Q'.add_mem (hw b) (hw' b), ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by simp [mul_add]
  have hmulA : ∀ p ∈ Q, ∀ q ∈ Q', p * q ∈ A := by
    intro p hp q hq
    have h := Submodule.mul_mem_mul hp hq
    rw [hQQ, Submodule.mem_one] at h
    obtain ⟨y, hy⟩ := h
    rw [← hy]
    exact y.2
  have hg : ∀ a, g a ∈ Q := fun a => Submodule.subset_span ⟨a, rfl⟩
  have he : ∀ j, g j * w j ∈ A := fun j => hmulA _ (hg j) _ (hwQ j)
  have hprod : ∀ q : Fin k → Ω, (∀ l, q l ∈ Q') → t * ∏ l, q l ∈ A := by
    intro q hq
    refine mem_of_pow_mul_mem A (fun j => g j * w j) he hsum _ fun j => ?_
    by_cases hj : g j = 0
    · exact ⟨1, by simp [hj]⟩
    · have h1 : t / g j ^ k ∈ powMulMem A (g j * w j) (he j) := by
        refine (Algebra.adjoin_le ?_) (ht j hj)
        rintro _ (ha | ⟨c, rfl⟩)
        · exact ⟨0, by simpa using ha⟩
        · refine ⟨1, ?_⟩
          have : (g j * w j) ^ 1 * (g c / g j) = g c * w j := by
            field_simp
          rw [this]
          exact hmulA _ (hg c) _ (hwQ j)
      obtain ⟨M, hM⟩ := h1
      refine ⟨M, ?_⟩
      have : (g j * w j) ^ M * (t * ∏ l, q l) = (g j * w j) ^ M * (t / g j ^ k) * ∏ l, (g j * q l) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        field_simp
      rw [this]
      exact A.mul_mem hM (Subalgebra.prod_mem _ fun l _ => hmulA _ (hg j) _ (hq l))
  have hQ'k : ∀ q ∈ Q' ^ k, t * q ∈ A := by
    intro q hq
    rw [Submodule.pow_eq_span_pow_set] at hq
    induction hq using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨f, rfl⟩ := Set.mem_pow.mp hz
      rw [List.prod_ofFn]
      exact hprod (fun l => f l) fun l => (f l).2
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact A.add_mem ha hb
    | smul a z _ hz =>
      rw [Subalgebra.smul_def, smul_eq_mul, mul_left_comm]
      exact A.mul_mem a.2 hz
  have h1 : (1 : Ω) ∈ Q ^ k * Q' ^ k := by
    rw [← mul_pow, hQQ, one_pow]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have key : ∀ z ∈ Q ^ k * Q' ^ k, t * z ∈ Q ^ k := by
    intro z hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro p hp q hq
      have : t * (p * q) = (⟨t * q, hQ'k q hq⟩ : A) • p := by
        rw [Subalgebra.smul_def]; ring
      rw [this]
      exact Submodule.smul_mem _ _ hp
    · intro a b ha hb
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
  simpa using key 1 h1

end Core

section Graph

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

theorem span_graphGen_eq_sub (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s)
    {i : Fin (N + 1)} (hi : x i ≠ 0) :
    Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart hi)) (Set.range fun b => x i ^ (-n) * s b) =
      Q.sub (Kleiman.singleChart hi) := by
  set I := Kleiman.singleChart hi with hIdef
  have hiI : i ∈ I.1 := Finset.mem_singleton_self i
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    have hb : s b ∈ (Q.twist (Kleiman.twistSys S x n)).sub I := by
      rw [← hgen I]; exact Submodule.subset_span ⟨b, rfl⟩
    obtain ⟨y, hy, hyb⟩ := (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n I hiI (s b)).mp hb
    have : x i ^ (-n) * s b = y := by
      simp only [hyb, smul_eq_mul, zpow_neg]
      field_simp
    show x i ^ (-n) * s b ∈ _
    rw [this]
    exact hy
  · intro y hy
    have hy' : x i ^ n * y ∈ Submodule.span (Kleiman.chartRing S x I) (Set.range s) := by
      rw [hgen I]
      exact (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n I hiI _).mpr ⟨y, hy, rfl⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy'
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, ?_⟩
    simp only [Subalgebra.smul_def, smul_eq_mul] at ha ⊢
    have : ∑ b, (a b : Ω) * (x i ^ (-n) * s b) = x i ^ (-n) * ∑ b, (a b : Ω) * s b := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, ha, zpow_neg]
    field_simp

theorem mem_pow_sub_iff_graph (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s)
    {i : Fin (N + 1)} (hi : x i ≠ 0) (k : ℕ) (t : Ω) :
    t ∈ (Q.pow k).sub (Kleiman.singleChart hi) ↔
      ∀ j, s j ≠ 0 → t * (x i ^ n * (s j)⁻¹) ^ k ∈ graphRing S x s i j := by
  rw [Kleiman.SubSystem.pow_sub]
  constructor
  · intro ht j hj
    induction k generalizing t with
    | zero =>
      rw [pow_zero, Submodule.mem_one] at ht
      obtain ⟨a, rfl⟩ := ht
      rw [pow_zero, mul_one]
      exact chartRing_le_graphRing x s hi j a.2
    | succ k ih =>
      rw [pow_succ'] at ht
      refine Submodule.mul_induction_on ht ?_ ?_
      · intro p hp q hq
        have : p * q * (x i ^ n * (s j)⁻¹) ^ (k + 1) =
            (p * (x i ^ n * (s j)⁻¹)) * (q * (x i ^ n * (s j)⁻¹) ^ k) := by ring
        rw [this]
        exact Subalgebra.mul_mem _ ((mem_sub_iff_graph Q n s hgen hi p).mp hp j hj) (ih q hq)
      · intro a b ha hb
        rw [add_mul]
        exact Subalgebra.add_mem _ ha hb
  · intro ht
    obtain ⟨Q', hQ'⟩ := Q.invertible (Kleiman.singleChart hi)
    rw [← span_graphGen_eq_sub Q n s hgen hi] at hQ' ⊢
    refine mem_pow_of_div_pow_mem _ Q' _ hQ' k t fun j hj => ?_
    have hsj : s j ≠ 0 := by
      intro h0; apply hj; simp [h0]
    have hgdiv : ∀ b, x i ^ (-n) * s b / (x i ^ (-n) * s j) = s b / s j := by
      intro b
      simp only [zpow_neg]
      field_simp
    have ht' : t / (x i ^ (-n) * s j) ^ k = t * (x i ^ n * (s j)⁻¹) ^ k := by
      rw [div_eq_mul_inv, ← inv_pow, mul_inv, zpow_neg, inv_inv]
    rw [ht']
    refine (graphRing_le x s hi j _ (fun a ha => Algebra.subset_adjoin (Or.inl ha)) fun b => ?_) (ht j hsj)
    rw [← hgdiv]
    exact Algebra.subset_adjoin (Or.inr ⟨b, rfl⟩)

theorem pow_graphDeg_exp (n : ℤ) (k : ℕ) (a b : Ω) :
    a ^ (-(k • graphDeg n) (Sum.inl ())) * b ^ (-(k • graphDeg n) (Sum.inr ())) = (a ^ n * b⁻¹) ^ k := by
  simp only [Pi.smul_apply, graphDeg_inl, graphDeg_inr, smul_neg, neg_neg, nsmul_eq_mul, mul_one]
  rw [mul_pow, inv_pow, ← zpow_natCast (a ^ n), ← zpow_mul, zpow_neg, zpow_natCast, mul_comm n]

theorem pow_secs_eq_secOver (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s)
    (k : ℕ) : (Q.pow k).secs = secOver S (graphVec x s) (k • graphDeg n) := by
  ext t
  rw [mem_secs_iff, mem_secOver_graph_iff]
  simp only [pow_graphDeg_exp]
  constructor
  · intro h i j hi hj
    exact (mem_pow_sub_iff_graph Q n s hgen hi k t).mp (h i hi) j hj
  · intro h i hi
    exact (mem_pow_sub_iff_graph Q n s hgen hi k t).mpr fun j hj => h i j hi hj

end Graph

section Ample

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

theorem generatesOver_graph (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s)
    (D : Kleiman.AmpleData S x Q) : GeneratesOver S (graphVec x s) (D.m • graphDeg n) D.h := by
  intro c hc
  obtain ⟨i, j, rfl⟩ : ∃ (i : Fin (N + 1)) (j : Fin m), c = graphChart i j :=
    ⟨c (Sum.inl ()), c (Sum.inr ()), graphChart_eta c⟩
  have hi : x i ≠ 0 := hc (Sum.inl ())
  have hj : s j ≠ 0 := hc (Sum.inr ())
  have hone : x i ^ (-n) * s j * (x i ^ n * (s j)⁻¹) = 1 := by
    rw [zpow_neg]
    field_simp
  have hy : (x i ^ (-n) * s j) ^ D.m ∈ (Q.pow D.m).sub (Kleiman.singleChart hi) := by
    refine (mem_pow_sub_iff_graph Q n s hgen hi D.m _).mpr fun j' hj' => ?_
    rw [← mul_pow]
    have : x i ^ (-n) * s j * (x i ^ n * (s j')⁻¹) = s j / s j' := by
      rw [zpow_neg]
      field_simp
    rw [this]
    exact Subalgebra.pow_mem _ (div_mem_graphRing_inr x s i j' j) _
  rw [← D.generates (Kleiman.singleChart hi)] at hy
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
  refine ⟨fun l => a l, fun l => chartRing_le_graphRing x s hi j (a l).2, ?_⟩
  rw [prod_graph, pow_graphDeg_exp]
  calc ∑ l, (a l : Ω) * (D.h l * (x i ^ n * (s j)⁻¹) ^ D.m)
      = (∑ l, a l • D.h l) * (x i ^ n * (s j)⁻¹) ^ D.m := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc]
    _ = 1 := by rw [ha, ← mul_pow, hone, one_pow]

theorem preimRing_subset_ampleRing (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω)
    (hgen : IsGraphGen Q n s) (D : Kleiman.AmpleData S x Q) {j : Fin (D.r + 1)} (hj : D.h j ≠ 0) :
    (IndefiniteRowSideFullHecke.Kleiman2.preimRing S (graphVec x s) D.h j : Set Ω) ⊆
      Kleiman.ampleRing Q.toSubSystem D.m (D.h j) := by
  intro f hf
  have hf0 : f ∈ IndefiniteRowSideFullHecke.Kleiman2.preimRing S (graphVec x s) D.h j := hf
  simp only [IndefiniteRowSideFullHecke.Kleiman2.preimRing, Algebra.mem_iInf] at hf0
  rw [Kleiman.ampleRing, Set.mem_iInter]
  intro I
  obtain ⟨i, hiI⟩ := I.2.1
  have hi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hiI)
  suffices h : ∃ M : ℕ, f * D.h j ^ M ∈ (Q.pow (D.m * M)).sub (Kleiman.singleChart hi) by
    obtain ⟨M, hM⟩ := h
    exact ⟨M, (Q.pow (D.m * M)).mono _ I (Finset.singleton_subset_iff.mpr hiI) _ hM⟩
  have hsec : ∀ l, D.h l ∈ (Q.pow D.m).sub (Kleiman.singleChart hi) := fun l =>
    (mem_secs_iff _ _).mp (D.mem_secs l) i hi
  have hM : ∀ j', ∃ M : ℕ, s j' ≠ 0 →
      (D.h j * (x i ^ n * (s j')⁻¹) ^ D.m) ^ M * f ∈ graphRing S x s i j' := by
    intro j'
    by_cases hj' : s j' = 0
    · exact ⟨0, fun h => absurd hj' h⟩
    have he : D.h j * (x i ^ n * (s j')⁻¹) ^ D.m ∈ graphRing S x s i j' :=
      (mem_pow_sub_iff_graph Q n s hgen hi D.m _).mp (hsec j) j' hj'
    have hle : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec (graphVec x s) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock D.h))
        (IndefiniteRowSideFullHecke.Kleiman2.joinChart (graphChart i j') fun _ => j) ≤ powMulMem (graphRing S x s i j') _ he := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨⟨(⟨⟩ | ⟨⟩) | ⟨⟩, a⟩, rfl⟩
      · exact ⟨0, by rw [pow_zero, one_mul]; exact div_mem_graphRing_inl x s i a j'⟩
      · exact ⟨0, by rw [pow_zero, one_mul]; exact div_mem_graphRing_inr x s i j' a⟩
      · refine ⟨1, ?_⟩
        have h1 := (mem_pow_sub_iff_graph Q n s hgen hi D.m _).mp (hsec a) j' hj'
        change (D.h j * (x i ^ n * (s j')⁻¹) ^ D.m) ^ 1 * (D.h a / D.h j) ∈ _
        have : (D.h j * (x i ^ n * (s j')⁻¹) ^ D.m) ^ 1 * (D.h a / D.h j) =
            D.h a * (x i ^ n * (s j')⁻¹) ^ D.m := by
          field_simp
        rw [this]
        exact h1
    obtain ⟨M, hM⟩ := hle (hf0 (graphChart i j') (by rintro (⟨⟩ | ⟨⟩); exacts [hi, hj']))
    exact ⟨M, fun _ => hM⟩
  choose M hM using hM
  refine ⟨∑ j', M j', (mem_pow_sub_iff_graph Q n s hgen hi _ _).mpr fun j' hj' => ?_⟩
  have he : D.h j * (x i ^ n * (s j')⁻¹) ^ D.m ∈ graphRing S x s i j' :=
    (mem_pow_sub_iff_graph Q n s hgen hi D.m _).mp (hsec j) j' hj'
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j') : M j' ≤ ∑ j', M j')
  rw [hd]
  have : f * D.h j ^ (M j' + d) * (x i ^ n * (s j')⁻¹) ^ (D.m * (M j' + d)) =
      (D.h j * (x i ^ n * (s j')⁻¹) ^ D.m) ^ d * ((D.h j * (x i ^ n * (s j')⁻¹) ^ D.m) ^ M j' * f) := by
    ring
  rw [this]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ he _) (hM j' hj')

theorem ampleRing_subset_preimRing (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω)
    (hgen : IsGraphGen Q n s) (D : Kleiman.AmpleData S x Q) {j : Fin (D.r + 1)} (hj : D.h j ≠ 0) :
    Kleiman.ampleRing Q.toSubSystem D.m (D.h j) ⊆
      (IndefiniteRowSideFullHecke.Kleiman2.preimRing S (graphVec x s) D.h j : Set Ω) := by
  intro f hf
  show f ∈ IndefiniteRowSideFullHecke.Kleiman2.preimRing S (graphVec x s) D.h j
  simp only [IndefiniteRowSideFullHecke.Kleiman2.preimRing, Algebra.mem_iInf]
  intro c hc
  obtain ⟨i, j', rfl⟩ : ∃ (i : Fin (N + 1)) (j' : Fin m), c = graphChart i j' :=
    ⟨c (Sum.inl ()), c (Sum.inr ()), graphChart_eta c⟩
  have hi : x i ≠ 0 := hc (Sum.inl ())
  have hj' : s j' ≠ 0 := hc (Sum.inr ())
  set R := chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec (graphVec x s) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock D.h))
    (IndefiniteRowSideFullHecke.Kleiman2.joinChart (graphChart i j') fun _ => j) with hRdef
  have hgR : graphRing S x s i j' ≤ R := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨⟨⟩ | ⟨⟩, a⟩, rfl⟩
    · exact Algebra.subset_adjoin ⟨⟨Sum.inl (Sum.inl ()), a⟩, rfl⟩
    · exact Algebra.subset_adjoin ⟨⟨Sum.inl (Sum.inr ()), a⟩, rfl⟩
  have hhR : ∀ l, D.h l / D.h j ∈ R := fun l => Algebra.subset_adjoin ⟨⟨Sum.inr (), l⟩, rfl⟩
  have hcc : x i ^ n * (s j')⁻¹ ≠ 0 := mul_ne_zero (zpow_ne_zero n hi) (inv_ne_zero hj')
  have hinv : (D.h j * (x i ^ n * (s j')⁻¹) ^ D.m)⁻¹ ∈ R := by
    obtain ⟨u, hu, hsum⟩ := generatesOver_graph Q n s hgen D (graphChart i j') hc
    rw [prod_graph, pow_graphDeg_exp] at hsum
    have : (D.h j * (x i ^ n * (s j')⁻¹) ^ D.m)⁻¹ = ∑ l, u l * (D.h l / D.h j) := by
      rw [← mul_one (D.h j * (x i ^ n * (s j')⁻¹) ^ D.m)⁻¹, ← hsum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have : (x i ^ n * (s j')⁻¹) ^ D.m ≠ 0 := pow_ne_zero _ hcc
      field_simp
    rw [this]
    exact Subalgebra.sum_mem _ fun l _ => Subalgebra.mul_mem _ (hgR (hu l)) (hhR l)
  obtain ⟨M, hM⟩ := Set.mem_iInter.mp hf (Kleiman.singleChart hi)
  have h1 := (mem_pow_sub_iff_graph Q n s hgen hi _ _).mp hM j' hj'
  have : f = f * D.h j ^ M * (x i ^ n * (s j')⁻¹) ^ (D.m * M) *
      ((D.h j * (x i ^ n * (s j')⁻¹) ^ D.m)⁻¹) ^ M := by
    have hne : D.h j * (x i ^ n * (s j')⁻¹) ^ D.m ≠ 0 := mul_ne_zero hj (pow_ne_zero _ hcc)
    have key : D.h j ^ M * ((x i ^ n * (s j')⁻¹) ^ D.m) ^ M *
        ((D.h j * (x i ^ n * (s j')⁻¹) ^ D.m)⁻¹) ^ M = 1 := by
      rw [← mul_pow, ← mul_pow, mul_inv_cancel₀ hne, one_pow]
    calc f = f * 1 := (mul_one f).symm
      _ = _ := by rw [← key, pow_mul]; ring
  rw [this]
  exact Subalgebra.mul_mem _ (hgR h1) (Subalgebra.pow_mem _ hinv _)

theorem isAmpleByFiniteMap_of_finite (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω)
    (hgen : IsGraphGen Q n s) (D : Kleiman.AmpleData S x Q)
    (hfin : ∀ j, D.h j ≠ 0 → ∃ (r : ℕ) (b : Fin r → Ω),
      (∀ l, b l ∈ IndefiniteRowSideFullHecke.Kleiman2.preimRing S (graphVec x s) D.h j) ∧
        (IndefiniteRowSideFullHecke.Kleiman2.preimRing S (graphVec x s) D.h j : Set Ω) ⊆
          Submodule.span (Kleiman.ampleBase (S := S) D.h j) (Set.range b)) :
    IndefiniteRowSideFullHecke.Kleiman2.IsAmpleByFiniteMap S (graphVec x s) (graphDeg n) :=
  ⟨D.m, D.r + 1, D.h, D.m_pos, fun l => by rw [← pow_secs_eq_secOver Q n s hgen]; exact D.mem_secs l,
    generatesOver_graph Q n s hgen D, hfin⟩

end Ample

theorem AmpleEq.proof (hfin : Kleiman.AmpleRingFinite.Statement) : AmpleEq.Statement := by
  intro S _ N Ω _ _ x Q n m s hgen hD
  obtain ⟨D⟩ := hD
  refine isAmpleByFiniteMap_of_finite Q n s hgen D fun j hj => ?_
  obtain ⟨r, b, hb, hsub⟩ := hfin S N Ω x Q D j hj
  exact ⟨r, b, fun l => ampleRing_subset_preimRing Q n s hgen D hj (hb l),
    (preimRing_subset_ampleRing Q n s hgen D hj).trans hsub⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
