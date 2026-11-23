import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqBundle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Alg

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem zpow_mem_of_inv_mem (R : Subalgebra S Ω) {a : Ω} (ha : a ∈ R) (ha' : a⁻¹ ∈ R) (n : ℤ) :
    a ^ n ∈ R := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]; exact pow_mem ha m
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem ha' m

theorem le_powMulMem (A : Subalgebra S Ω) {f : Ω} (hf : f ∈ A) : A ≤ powMulMem A f hf :=
  fun r hr => ⟨0, by simpa using hr⟩

theorem powMulMem_mono {A B : Subalgebra S Ω} (hAB : A ≤ B) {f : Ω} (hf : f ∈ A) :
    powMulMem A f hf ≤ powMulMem B f (hAB hf) := by
  rintro r ⟨M, hM⟩
  exact ⟨M, hAB hM⟩

theorem pow_mul_mem_of_le (A : Subalgebra S Ω) {f r : Ω} (hf : f ∈ A) {M M' : ℕ} (h : M ≤ M')
    (hM : f ^ M * r ∈ A) : f ^ M' * r ∈ A := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_assoc]
  exact A.mul_mem (A.pow_mem hf _) hM

def fracSubring (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] : Subring Ω where
  carrier := {r | ∃ b : A, b ∉ p ∧ (b : Ω) * r ∈ A}
  mul_mem' := by
    rintro r s ⟨b, hb, hbr⟩ ⟨b', hb', hbs⟩
    refine ⟨b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    have := A.mul_mem hbr hbs
    convert this using 1
    push_cast
    ring
  one_mem' := ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h), by simpa using A.one_mem⟩
  add_mem' := by
    rintro r s ⟨b, hb, hbr⟩ ⟨b', hb', hbs⟩
    refine ⟨b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    have := A.add_mem (A.mul_mem b'.2 hbr) (A.mul_mem b.2 hbs)
    convert this using 1
    push_cast
    ring
  zero_mem' := ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h), by simpa using A.zero_mem⟩
  neg_mem' := by
    rintro r ⟨b, hb, hbr⟩
    exact ⟨b, hb, by rw [mul_neg]; exact neg_mem hbr⟩

theorem locIn_le_fracSubring (A : Subalgebra S Ω) (p : Ideal A) [p.IsPrime] :
    IndefiniteRowSideFullHecke.Kleiman2.locIn A p ≤ fracSubring A p := by
  refine Subring.closure_le.mpr ?_
  rintro _ ⟨a, b, hb, rfl⟩
  refine ⟨b, hb, ?_⟩
  have hb0 : (b : Ω) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact p.zero_mem)
  have : (b : Ω) * ((a : Ω) / b) = a := by field_simp
  rw [this]
  exact a.2

theorem subset_locIn (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] {r : Ω} (hr : r ∈ A) :
    r ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  Subring.subset_closure ⟨⟨r, hr⟩, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h), by simp⟩

end Alg

section Model

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]

variable (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))

abbrev baseVec : Fin (N + 1) → Ω := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm

theorem baseVec_apply (i : Fin (N + 1)) : baseVec y k₀ e i = y ⟨k₀, e.symm i⟩ := rfl

def genInv (β : K → ℤ) (d : ∀ k, ι k) : Ω := ∏ k, y ⟨k, d k⟩ ^ (-β k)

def overRing (d : ∀ k, ι k) (i : Fin (N + 1)) : Subalgebra S Ω :=
  chartRingOver S y d ⊔ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i

def latOf (β : K → ℤ) (i : Fin (N + 1)) : AddSubgroup Ω where
  carrier := {t | ∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) → t * genInv y β d ∈ overRing (S := S) y k₀ e d i}
  add_mem' := by
    intro a b ha hb d hd
    rw [add_mul]
    exact add_mem (ha d hd) (hb d hd)
  zero_mem' := by
    intro d _
    rw [zero_mul]
    exact zero_mem _
  neg_mem' := by
    intro a ha d hd
    rw [neg_mul]
    exact neg_mem (ha d hd)

variable {y k₀ e}

theorem mem_latOf (β : K → ℤ) (i : Fin (N + 1)) (t : Ω) :
    t ∈ latOf (S := S) y k₀ e β i ↔
      ∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) → t * genInv y β d ∈ overRing (S := S) y k₀ e d i :=
  Iff.rfl

theorem genInv_ne_zero (β : K → ℤ) {d : ∀ k, ι k} (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) : genInv y β d ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hd k)

theorem genInv_add_baseDeg (β : K → ℤ) (c : ℤ) {d : ∀ k, ι k} (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) :
    genInv y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) d = genInv y β d * y ⟨k₀, d k₀⟩ ^ (-c) := by
  unfold genInv
  have h : ∀ k, y ⟨k, d k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      y ⟨k, d k⟩ ^ (-β k) * y ⟨k, d k⟩ ^ (-(c * IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ k)) := by
    intro k
    rw [← zpow_add₀ (hd k)]
    congr 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.prod_congr rfl fun k _ => h k, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single k₀]
  · simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  · intro k _ hk
    simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, Pi.single_apply, hk]
  · simp

theorem div_mem_chartRingOver (d : ∀ k, ι k) (k : K) (a : ι k) :
    y ⟨k, a⟩ / y ⟨k, d k⟩ ∈ chartRingOver S y d :=
  Algebra.subset_adjoin ⟨⟨k, a⟩, rfl⟩

theorem chartRing_le_chartRingOver (d : ∀ k, ι k) :
    ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) (e (d k₀)) ≤ chartRingOver S y d := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨j, rfl⟩
  simp only [baseVec_apply, Equiv.symm_apply_apply]
  exact div_mem_chartRingOver d k₀ _

theorem chartRing_le_overRing (d : ∀ k, ι k) (i : Fin (N + 1)) :
    ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i ≤ overRing y k₀ e d i :=
  le_sup_right

theorem chartRingOver_le_overRing (d : ∀ k, ι k) (i : Fin (N + 1)) :
    chartRingOver S y d ≤ overRing y k₀ e d i :=
  le_sup_left

theorem overRing_self (d : ∀ k, ι k) : overRing (S := S) y k₀ e d (e (d k₀)) = chartRingOver S y d :=
  sup_eq_left.mpr (chartRing_le_chartRingOver d)

theorem chartRingOver_oneBlock_base (i : Fin (N + 1)) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ : Unit => e.symm i) =
      ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨⟨⟩, a⟩, rfl⟩
    have h := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := S) (baseVec y k₀ e) i (e a)
    rw [baseVec_apply, baseVec_apply, Equiv.symm_apply_apply] at h
    exact h
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    have h : IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) ⟨(), e.symm j⟩ /
        IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) ⟨(), e.symm i⟩ ∈
        chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ : Unit => e.symm i) :=
      Algebra.subset_adjoin ⟨⟨(), e.symm j⟩, rfl⟩
    exact h

theorem model_pt_of_prime (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) {i : Fin (N + 1)}
    (hi : baseVec y k₀ e i ≠ 0)
    (p' : Ideal (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ : Unit => e.symm i)))
    (hp' : p'.IsPrime) :
    ∃ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) ∧ ∃ q : Ideal (chartRingOver S y d), q.IsPrime ∧
      IndefiniteRowSideFullHecke.Kleiman2.locIn _ p' = IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y d) q := by
  have hc0 : ∀ k : Unit, IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) ⟨k, e.symm i⟩ ≠ 0 :=
    fun _ => hi
  have hmem : IndefiniteRowSideFullHecke.Kleiman2.locIn _ p' ∈
      IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) :=
    ⟨fun _ => e.symm i, hc0, p', hp', rfl⟩
  rw [← hy.2] at hmem
  exact hmem

theorem exists_chart_of_prime (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) {i : Fin (N + 1)}
    (hi : baseVec y k₀ e i ≠ 0) (p : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i))
    [hp : p.IsPrime] :
    ∃ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) ∧ ∀ s : Σ k, ι k,
      ∃ b : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i, b ∉ p ∧
        (b : Ω) * (y s / y ⟨s.1, d s.1⟩) ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i := by
  have hA := chartRingOver_oneBlock_base (S := S) (y := y) (e := e) i
  let φ := Subalgebra.inclusion hA.le
  let p' := p.comap φ
  have hp' : p'.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨d, hd, q, hq, hz⟩ := model_pt_of_prime hy hi p' hp'
  refine ⟨d, hd, fun s => ?_⟩
  have h1 : y s / y ⟨s.1, d s.1⟩ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y d) q :=
    subset_locIn _ q (Algebra.subset_adjoin ⟨s, rfl⟩)
  rw [← hz] at h1
  obtain ⟨b, hb, hbr⟩ := locIn_le_fracSubring _ p' h1
  have hb' : φ b ∉ p := fun h => hb (Ideal.mem_comap.mpr h)
  refine ⟨φ b, hb', ?_⟩
  have hc : ((φ b : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i) : Ω) = (b : Ω) :=
    Subalgebra.coe_inclusion hA.le b
  rw [hc]
  exact hA.le hbr

theorem exists_basic (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) {i : Fin (N + 1)}
    (hi : baseVec y k₀ e i ≠ 0) (p : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i))
    [hp : p.IsPrime] :
    ∃ f : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i, f ∉ p ∧ ∃ d : ∀ k, ι k,
      (∀ k, y ⟨k, d k⟩ ≠ 0) ∧ chartRingOver S y d ≤ powMulMem _ (f : Ω) f.2 := by
  classical
  obtain ⟨d, hd, hgen⟩ := exists_chart_of_prime hy hi p
  choose b hb hbr using hgen
  refine ⟨∏ s, b s, ?_, d, hd, ?_⟩
  · intro hmem
    obtain ⟨s, _, hs⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hp)).mp hmem
    exact hb s hs
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨s, rfl⟩
    refine ⟨1, ?_⟩
    have key : ((∏ s', b s' : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i) : Ω) ^ 1 *
        (y s / y ⟨s.1, d s.1⟩) =
        ((∏ s' ∈ Finset.univ.erase s, b s' : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i) : Ω) *
          ((b s : Ω) * (y s / y ⟨s.1, d s.1⟩)) := by
      rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ s)]
      push_cast
      ring
    rw [key]
    exact Subalgebra.mul_mem _ (Subtype.prop _) (hbr s)

theorem stable_latOf (β : K → ℤ) (i : Fin (N + 1)) (a : Ω)
    (ha : a ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i) (t : Ω)
    (ht : t ∈ latOf (S := S) y k₀ e β i) : a • t ∈ latOf (S := S) y k₀ e β i := by
  intro d hd
  rw [smul_eq_mul, mul_assoc]
  exact mul_mem (chartRing_le_overRing d i ha) (ht d hd)

theorem overlap_latOf (β : K → ℤ) (i j : Fin (N + 1)) (hi : baseVec y k₀ e i ≠ 0)
    (hj : baseVec y k₀ e j ≠ 0) (t : Ω) (ht : t ∈ latOf (S := S) y k₀ e β i) :
    ∃ m : ℕ, (baseVec y k₀ e i / baseVec y k₀ e j) ^ m • t ∈ latOf (S := S) y k₀ e β j := by
  set x := baseVec y k₀ e
  have hM : ∀ d : ∀ k, ι k, ∃ M : ℕ, (∀ k, y ⟨k, d k⟩ ≠ 0) →
      (x i / x j) ^ M * (t * genInv y β d) ∈ overRing (S := S) y k₀ e d j := by
    intro d
    by_cases hd : ∀ k, y ⟨k, d k⟩ ≠ 0
    · have hr : x i / x j ∈ overRing (S := S) y k₀ e d j :=
        chartRing_le_overRing d j (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j i)
      have hle : overRing (S := S) y k₀ e d i ≤ powMulMem _ (x i / x j) hr := by
        refine sup_le ((chartRingOver_le_overRing d j).trans (le_powMulMem _ hr)) ?_
        refine Algebra.adjoin_le ?_
        rintro _ ⟨a, rfl⟩
        refine ⟨1, ?_⟩
        have : (x i / x j) ^ 1 * (x a / x i) = x a / x j := by field_simp
        rw [this]
        exact chartRing_le_overRing d j (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j a)
      obtain ⟨M, hM⟩ := hle (ht d hd)
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose M hM using hM
  refine ⟨∑ d, M d, fun d hd => ?_⟩
  rw [smul_eq_mul, mul_assoc]
  have hr : x i / x j ∈ overRing (S := S) y k₀ e d j :=
    chartRing_le_overRing d j (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j i)
  exact pow_mul_mem_of_le _ hr (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ d))
    (hM d hd)

theorem frame_latOf (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) (β : K → ℤ) (i : Fin (N + 1))
    (hi : baseVec y k₀ e i ≠ 0) :
    ∃ (n : ℕ) (f c : Fin n → Ω), (∀ l, f l ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i) ∧
      (∀ l, c l ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i) ∧ ∑ l, c l * f l = 1 ∧
      ∀ l, ∃ b : Fin 1 → Ω, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
        ∀ t, (∃ n : ℕ, f l ^ n • t ∈ latOf (S := S) y k₀ e β i) ↔
          ∃ a : Fin 1 → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i) ∧
            t = ∑ q, a q • b q := by
  set A := ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i
  let T : Set A := {f | ∃ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) ∧
    chartRingOver S y d ≤ powMulMem A (f : Ω) f.2}
  have hT : Ideal.span T = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI := hm.isPrime
    obtain ⟨f, hf, d, hd, hdle⟩ := exists_basic hy hi m
    exact hf (hle (Ideal.subset_span ⟨d, hd, hdle⟩))
  have h1 : (1 : A) ∈ Ideal.span T := by rw [hT]; exact Submodule.mem_top
  obtain ⟨n, cf, g, hsum⟩ := Submodule.mem_span_set'.mp h1
  choose d hd hdle using fun l => (g l).2
  refine ⟨n, fun l => (((g l).1 : A) : Ω), fun l => (cf l : Ω), fun l => (g l).1.2, fun l => (cf l).2, ?_,
    fun l => ?_⟩
  · have := congrArg Subtype.val hsum
    simpa [smul_eq_mul] using this
  · set f : A := (g l).1
    set w := genInv y β (d l)
    have hw : w ≠ 0 := genInv_ne_zero β (hd l)
    refine ⟨fun _ => w⁻¹, linearIndependent_unique_iff.2 (inv_ne_zero hw), ?_, fun t => ?_⟩
    · rw [Set.range_const]
      exact Ideal.span_singleton_eq_top.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hw))
    simp only [Fin.sum_univ_one, smul_eq_mul]
    constructor
    · rintro ⟨m, hm⟩
      have h2 : (f : Ω) ^ m * t * w ∈ powMulMem A (f : Ω) f.2 :=
        sup_le (hdle l) (le_powMulMem A f.2) (hm (d l) (hd l))
      obtain ⟨M, hM⟩ := h2
      refine ⟨fun _ => t * w, fun _ => ⟨M + m, ?_⟩, ?_⟩
      · convert hM using 1; ring
      · field_simp
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨n0, hn0⟩ := ha 0
      have hM : ∀ d' : ∀ k, ι k, ∃ M : ℕ, (∀ k, y ⟨k, d' k⟩ ≠ 0) →
          (f : Ω) ^ M * (a 0 * w⁻¹ * genInv y β d') ∈ overRing (S := S) y k₀ e d' i := by
        intro d'
        by_cases hd' : ∀ k, y ⟨k, d' k⟩ ≠ 0
        · have hfB : (f : Ω) ∈ overRing (S := S) y k₀ e d' i := chartRing_le_overRing d' i f.2
          set P := powMulMem _ (f : Ω) hfB
          have hdP : chartRingOver S y (d l) ≤ P :=
            (hdle l).trans (powMulMem_mono (chartRing_le_overRing d' i) f.2)
          have hd'P : chartRingOver S y d' ≤ P :=
            (chartRingOver_le_overRing d' i).trans (le_powMulMem _ hfB)
          have hratio : genInv y β d' / w = ∏ k, (y ⟨k, d l k⟩ / y ⟨k, d' k⟩) ^ β k := by
            simp only [w, genInv]
            rw [← Finset.prod_div_distrib]
            refine Finset.prod_congr rfl fun k _ => ?_
            rw [zpow_neg, zpow_neg, inv_div_inv, div_zpow]
          have hrP : genInv y β d' / w ∈ P := by
            rw [hratio]
            refine Subalgebra.prod_mem _ fun k _ => zpow_mem_of_inv_mem _ ?_ ?_ _
            · exact hd'P (div_mem_chartRingOver d' k _)
            · rw [inv_div]; exact hdP (div_mem_chartRingOver (d l) k _)
          have haP : a 0 ∈ P := powMulMem_mono (chartRing_le_overRing d' i) f.2 ⟨n0, hn0⟩
          have heq : a 0 * w⁻¹ * genInv y β d' = a 0 * (genInv y β d' / w) := by ring
          obtain ⟨M, hM⟩ := P.mul_mem haP hrP
          exact ⟨M, fun _ => heq ▸ hM⟩
        · exact ⟨0, fun h => absurd h hd'⟩
      choose M hM using hM
      refine ⟨∑ d', M d', fun d' hd' => ?_⟩
      rw [mul_assoc]
      exact pow_mul_mem_of_le _ (chartRing_le_overRing d' i f.2)
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ d')) (hM d' hd')

def bundleOfDeg (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) (β : K → ℤ) :
    IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) (baseVec y k₀ e) where
  lat := latOf y k₀ e β
  stable i a ha t ht := stable_latOf β i a ha t ht
  frame i hi := frame_latOf hy β i hi
  overlap i j hi hj t ht := overlap_latOf β i j hi hj t ht

theorem ofSecond_sub_single {x : Fin (N + 1) → Ω} (Q' : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x)
    {i : Fin (N + 1)} (h : x i ≠ 0) (z : Ω) :
    z ∈ (TranslateEq.ofSecond Q').sub (Kleiman.singleChart h) ↔ z ∈ Q'.lat i := by
  change z ∈ TranslateEq.subOf Q' (Kleiman.singleChart h) ↔ _
  rw [TranslateEq.subOf_eq Q' (Finset.mem_singleton_self i), ← TranslateEq.coe_latSub Q' h, Submodule.span_eq]
  rfl

end Model

theorem BundleOfDeg.full : BundleOfDeg.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ N e hy β
  refine ⟨TranslateEq.ofSecond (bundleOfDeg (e := e) hy β), fun c => ?_⟩
  set x := baseVec y k₀ e with hx
  ext t
  rw [mem_secs_iff]
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  have key : ∀ i (hi : x i ≠ 0),
      t ∈ ((TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).twist (Kleiman.twistSys S x c)).sub
          (Kleiman.singleChart hi) ↔
        ∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) →
          x i ^ (-c) * t * genInv y β d ∈ overRing (S := S) y k₀ e d i := by
    intro i hi
    rw [TranslateEq.mem_twist_twistSys_iff (TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).toSubSystem c
      (Kleiman.singleChart hi) (Finset.mem_singleton_self i)]
    change _ ↔ x i ^ (-c) * t ∈ (bundleOfDeg (e := e) hy β).lat i
    rw [← ofSecond_sub_single (bundleOfDeg (e := e) hy β) hi]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have : x i ^ (-c) * x i ^ c • u = u := by
        rw [smul_eq_mul, zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero c hi), one_mul]
      rw [this]
      exact hu
    · intro h
      refine ⟨_, h, ?_⟩
      rw [smul_eq_mul, zpow_neg, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero c hi), one_mul]
  constructor
  · intro h d hd
    have hxe : x (e (d k₀)) = y ⟨k₀, d k₀⟩ := by simp [hx, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
    have hi : x (e (d k₀)) ≠ 0 := by rw [hxe]; exact hd k₀
    have h1 := (key _ hi).mp (h _ hi) d hd
    rw [overRing_self, hxe] at h1
    change t * genInv y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) d ∈ _
    rw [genInv_add_baseDeg β c hd]
    convert h1 using 1
    ring
  · intro h i hi
    rw [key]
    intro d hd
    have h1 := h d hd
    change t * genInv y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) d ∈ _ at h1
    rw [genInv_add_baseDeg β c hd] at h1
    have hyd : y ⟨k₀, d k₀⟩ ≠ 0 := hd k₀
    have hu : (y ⟨k₀, d k₀⟩ / x i) ^ c ∈ overRing (S := S) y k₀ e d i := by
      refine zpow_mem_of_inv_mem _ ?_ ?_ c
      · have : y ⟨k₀, d k₀⟩ / x i = x (e (d k₀)) / x i := by simp [hx, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
        rw [this]
        exact chartRing_le_overRing d i (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x i _)
      · rw [inv_div]
        exact chartRingOver_le_overRing d i (div_mem_chartRingOver d k₀ (e.symm i))
    have heq : x i ^ (-c) * t * genInv y β d =
        (y ⟨k₀, d k₀⟩ / x i) ^ c * (t * (genInv y β d * y ⟨k₀, d k₀⟩ ^ (-c))) := by
      rw [div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [heq]
    exact mul_mem hu (chartRingOver_le_overRing d i h1)

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
