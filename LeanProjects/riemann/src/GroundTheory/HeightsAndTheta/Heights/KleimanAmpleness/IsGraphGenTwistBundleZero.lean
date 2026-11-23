import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.EqZeroOrIsHomogeneousOfMemPolyPiece
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Core

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

def powMulMem (A : Subalgebra S Ω) (e : Ω) (he : e ∈ A) : Subalgebra S Ω where
  carrier := {r | ∃ M : ℕ, e ^ M * r ∈ A}
  mul_mem' := by
    rintro a b ⟨M, hM⟩ ⟨M', hM'⟩
    refine ⟨M + M', ?_⟩
    have := A.mul_mem hM hM'
    convert this using 1
    ring
  one_mem' := ⟨0, by simpa using A.one_mem⟩
  add_mem' := by
    rintro a b ⟨M, hM⟩ ⟨M', hM'⟩
    refine ⟨M + M', ?_⟩
    have := A.add_mem (A.mul_mem (A.pow_mem he M') hM) (A.mul_mem (A.pow_mem he M) hM')
    convert this using 1
    ring
  zero_mem' := ⟨0, by simpa using A.zero_mem⟩
  algebraMap_mem' r := ⟨0, by simpa using A.algebraMap_mem r⟩

def mulMemIdeal (A : Subalgebra S Ω) (r : Ω) : Ideal A where
  carrier := {a | (a : Ω) * r ∈ A}
  add_mem' := by
    intro a b ha hb
    simpa [add_mul] using A.add_mem ha hb
  zero_mem' := by simpa using A.zero_mem
  smul_mem' := by
    intro c a ha
    simpa [smul_eq_mul, mul_assoc] using A.mul_mem c.2 ha

theorem mem_span_of_div_mem (A : Subalgebra S Ω) (Q' : Submodule A Ω) {m : ℕ} (g : Fin m → Ω)
    (hQQ : Submodule.span A (Set.range g) * Q' = 1) (R : Fin m → Subalgebra S Ω)
    (hR : ∀ j, g j ≠ 0 → R j ≤ Algebra.adjoin S ((A : Set Ω) ∪ Set.range fun b => g b / g j))
    (t : Ω) (ht : ∀ j, g j ≠ 0 → t / g j ∈ R j) : t ∈ Submodule.span A (Set.range g) := by
  classical
  have hone : (1 : Ω) ∈ Submodule.span A (Set.range g) * Q' := by
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
  have hgA : ∀ a b, g a * w b ∈ A := by
    intro a b
    have h := Submodule.mul_mem_mul (Submodule.subset_span ⟨a, rfl⟩ : g a ∈ Submodule.span A (Set.range g))
      (hwQ b)
    rw [hQQ, Submodule.mem_one] at h
    obtain ⟨y, hy⟩ := h
    rw [← hy]
    exact y.2
  have htw : ∀ b, t * w b ∈ A := by
    intro b
    have hM : ∀ j, ∃ M : ℕ, (g j * w j) ^ M * (t * w b) ∈ A := by
      intro j
      by_cases hj : g j = 0
      · exact ⟨1, by simp [hj]⟩
      · have h1 : t / g j ∈ powMulMem A (g j * w j) (hgA j j) := by
          refine ((hR j hj).trans ?_) (ht j hj)
          refine Algebra.adjoin_le ?_
          rintro _ (ha | ⟨c, rfl⟩)
          · exact ⟨0, by simpa using ha⟩
          · refine ⟨1, ?_⟩
            have : (g j * w j) ^ 1 * (g c / g j) = g c * w j := by
              field_simp
            rw [this]
            exact hgA c j
        obtain ⟨M, hM⟩ := h1
        refine ⟨M, ?_⟩
        have : (g j * w j) ^ M * (t * w b) = (g j * w j) ^ M * (t / g j) * (g j * w b) := by
          field_simp
        rw [this]
        exact A.mul_mem hM (hgA j b)
    choose M hM using hM
    let e : Fin m → A := fun j => ⟨g j * w j, hgA j j⟩
    have hspan : Ideal.span (Set.range e) = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have h1 : (1 : A) = ∑ j, e j := Subtype.ext (by simp [e, hsum])
      rw [h1]
      exact Ideal.sum_mem _ fun j _ => Ideal.subset_span ⟨j, rfl⟩
    have hpow := Ideal.span_pow_eq_top _ hspan (∑ j, M j)
    have hle : Ideal.span ((fun a => a ^ (∑ j, M j)) '' Set.range e) ≤ mulMemIdeal A (t * w b) := by
      rw [Ideal.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      have hj : M j ≤ ∑ j, M j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      change ((e j ^ (∑ j, M j) : A) : Ω) * (t * w b) ∈ A
      rw [SubmonoidClass.coe_pow, ← Nat.sub_add_cancel hj, pow_add, mul_assoc]
      exact A.mul_mem (A.pow_mem (hgA j j) _) (hM j)
    rw [hpow] at hle
    have h1 : (1 : A) ∈ mulMemIdeal A (t * w b) := hle Submodule.mem_top
    simpa [mulMemIdeal] using h1
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun b => ⟨t * w b, htw b⟩, ?_⟩
  simp only [Subalgebra.smul_def, smul_eq_mul]
  calc ∑ b, t * w b * g b = t * ∑ b, g b * w b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
    _ = t := by rw [hsum, mul_one]

end Core

section Graph

variable {Ω : Type} {N m : ℕ}

abbrev graphIdx (N m : ℕ) : Unit ⊕ Unit → Type :=
  Sum.elim (fun _ : Unit => Fin (N + 1)) (fun _ : Unit => Fin m)

def graphVec (x : Fin (N + 1) → Ω) (s : Fin m → Ω) : (Σ k, graphIdx N m k) → Ω :=
  IndefiniteRowSideFullHecke.Kleiman2.joinVec (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock s)

abbrev baseBlock : Unit ⊕ Unit := Sum.inl ()

def graphDeg (n : ℤ) : Unit ⊕ Unit → ℤ := Sum.elim (fun _ => -n) (fun _ => 1)

def graphChart (i : Fin (N + 1)) (j : Fin m) : ∀ k, graphIdx N m k :=
  IndefiniteRowSideFullHecke.Kleiman2.joinChart (fun _ : Unit => i) (fun _ : Unit => j)

@[simp] theorem graphVec_inl (x : Fin (N + 1) → Ω) (s : Fin m → Ω) (a : Fin (N + 1)) :
    graphVec x s ⟨Sum.inl (), a⟩ = x a := rfl

@[simp] theorem graphVec_inr (x : Fin (N + 1) → Ω) (s : Fin m → Ω) (b : Fin m) :
    graphVec x s ⟨Sum.inr (), b⟩ = s b := rfl

@[simp] theorem graphChart_inl (i : Fin (N + 1)) (j : Fin m) : graphChart i j (Sum.inl ()) = i := rfl

@[simp] theorem graphChart_inr (i : Fin (N + 1)) (j : Fin m) : graphChart i j (Sum.inr ()) = j := rfl

@[simp] theorem graphDeg_inl (n : ℤ) : graphDeg n (Sum.inl ()) = -n := rfl

@[simp] theorem graphDeg_inr (n : ℤ) : graphDeg n (Sum.inr ()) = 1 := rfl

theorem graphChart_eta (c : ∀ k, graphIdx N m k) : c = graphChart (c (Sum.inl ())) (c (Sum.inr ())) := by
  funext k
  rcases k with ⟨⟩ | ⟨⟩ <;> rfl

variable (S : Type) [CommRing S] [Field Ω] [Algebra S Ω]

abbrev graphRing (x : Fin (N + 1) → Ω) (s : Fin m → Ω) (i : Fin (N + 1)) (j : Fin m) : Subalgebra S Ω :=
  chartRingOver S (graphVec x s) (graphChart i j)

variable {S}

theorem div_mem_graphRing_inl (x : Fin (N + 1) → Ω) (s : Fin m → Ω) (i a : Fin (N + 1)) (j : Fin m) :
    x a / x i ∈ graphRing S x s i j :=
  Algebra.subset_adjoin ⟨⟨Sum.inl (), a⟩, rfl⟩

theorem div_mem_graphRing_inr (x : Fin (N + 1) → Ω) (s : Fin m → Ω) (i : Fin (N + 1)) (j b : Fin m) :
    s b / s j ∈ graphRing S x s i j :=
  Algebra.subset_adjoin ⟨⟨Sum.inr (), b⟩, rfl⟩

theorem chartRing_le_graphRing (x : Fin (N + 1) → Ω) (s : Fin m → Ω) {i : Fin (N + 1)} (hi : x i ≠ 0)
    (j : Fin m) : Kleiman.chartRing S x (Kleiman.singleChart hi) ≤ graphRing S x s i j := by
  rw [← TranslateEq.chartRing.equiv S x hi]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨a, rfl⟩
  exact div_mem_graphRing_inl x s i a j

theorem graphRing_le (x : Fin (N + 1) → Ω) (s : Fin m → Ω) {i : Fin (N + 1)} (hi : x i ≠ 0) (j : Fin m)
    (T : Subalgebra S Ω) (hA : Kleiman.chartRing S x (Kleiman.singleChart hi) ≤ T)
    (hs : ∀ b, s b / s j ∈ T) : graphRing S x s i j ≤ T := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨⟨⟨⟩ | ⟨⟩, a⟩, rfl⟩
  · exact hA (Kleiman.ratio hi a).2
  · exact hs a

theorem prod_graph (x : Fin (N + 1) → Ω) (s : Fin m → Ω) (β : Unit ⊕ Unit → ℤ) (i : Fin (N + 1)) (j : Fin m) :
    ∏ k, graphVec x s ⟨k, graphChart i j k⟩ ^ (-β k) = x i ^ (-β (Sum.inl ())) * s j ^ (-β (Sum.inr ())) := by
  simp only [Fintype.prod_sum_type, Fintype.univ_unit, Finset.prod_singleton]
  rfl

theorem mem_secOver_graph_iff (x : Fin (N + 1) → Ω) (s : Fin m → Ω) (β : Unit ⊕ Unit → ℤ) (t : Ω) :
    t ∈ secOver S (graphVec x s) β ↔ ∀ i j, x i ≠ 0 → s j ≠ 0 →
      t * (x i ^ (-β (Sum.inl ())) * s j ^ (-β (Sum.inr ()))) ∈ graphRing S x s i j := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  constructor
  · intro h i j hi hj
    have := h (graphChart i j) (by rintro (⟨⟩ | ⟨⟩); exacts [hi, hj])
    rwa [prod_graph] at this
  · intro h c hc
    obtain ⟨i, j, rfl⟩ : ∃ (i : Fin (N + 1)) (j : Fin m), c = graphChart i j :=
      ⟨c (Sum.inl ()), c (Sum.inr ()), graphChart_eta c⟩
    rw [prod_graph]
    exact h i j (hc (Sum.inl ())) (hc (Sum.inr ()))

end Graph

section Sections

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

def IsGraphGen (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) : Prop :=
  ∀ I, Submodule.span (Kleiman.chartRing S x I) (Set.range s) = (Q.twist (Kleiman.twistSys S x n)).sub I

theorem mem_secs_iff (F : Kleiman.SubSystem S x Ω) (t : Ω) :
    t ∈ F.secs ↔ ∀ i (hi : x i ≠ 0), t ∈ F.sub (Kleiman.singleChart hi) := by
  rw [Kleiman.SubSystem.secs, Submodule.mem_iInf]
  constructor
  · intro h i hi
    exact h _
  · intro h I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
    exact F.mono _ I (Finset.singleton_subset_iff.mpr hi) t (h i hxi)

theorem mem_sub_iff_graph (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω)
    (hgen : IsGraphGen Q n s)
    {i : Fin (N + 1)} (hi : x i ≠ 0) (t : Ω) :
    t ∈ Q.sub (Kleiman.singleChart hi) ↔
      ∀ j, s j ≠ 0 → t * (x i ^ n * (s j)⁻¹) ∈ graphRing S x s i j := by
  set I := Kleiman.singleChart hi with hIdef
  have hiI : i ∈ I.1 := Finset.mem_singleton_self i
  have hxn : x i ^ n ≠ 0 := zpow_ne_zero n hi
  let g : Fin m → Ω := fun b => x i ^ (-n) * s b
  have hgQ : Submodule.span (Kleiman.chartRing S x I) (Set.range g) = Q.sub I := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      have hb : s b ∈ (Q.twist (Kleiman.twistSys S x n)).sub I := by
        rw [← hgen I]; exact Submodule.subset_span ⟨b, rfl⟩
      obtain ⟨y, hy, hyb⟩ := (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n I hiI (s b)).mp hb
      have : g b = y := by
        simp only [g, hyb, smul_eq_mul, zpow_neg]
        field_simp
      rw [SetLike.mem_coe, this]
      exact hy
    · intro y hy
      have hy' : x i ^ n * y ∈ Submodule.span (Kleiman.chartRing S x I) (Set.range s) := by
        rw [hgen I]
        exact (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n I hiI _).mpr ⟨y, hy, rfl⟩
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy'
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨a, ?_⟩
      simp only [g, Subalgebra.smul_def, smul_eq_mul] at ha ⊢
      have : ∑ b, (a b : Ω) * (x i ^ (-n) * s b) = x i ^ (-n) * ∑ b, (a b : Ω) * s b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
      rw [this, ha, zpow_neg]
      field_simp
  have hgdiv : ∀ b j, g b / g j = s b / s j := by
    intro b j
    simp only [g, zpow_neg]
    field_simp
  have hgt : ∀ j, t / g j = t * (x i ^ n * (s j)⁻¹) := by
    intro j
    simp only [g, zpow_neg]
    field_simp
  rw [← hgQ]
  constructor
  · intro ht j _
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp ht
    rw [← hgt, Finset.sum_div]
    refine Subalgebra.sum_mem _ fun b _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul, mul_div_assoc, hgdiv]
    exact Subalgebra.mul_mem _ (chartRing_le_graphRing x s hi j (a b).2) (div_mem_graphRing_inr x s i j b)
  · intro ht
    obtain ⟨Q', hQ'⟩ := Q.invertible I
    rw [← hgQ] at hQ'
    refine mem_span_of_div_mem _ Q' g hQ' (fun j => graphRing S x s i j) ?_ t ?_
    · intro j _
      refine graphRing_le x s hi j _ (fun a ha => Algebra.subset_adjoin (Or.inl ha)) fun b => ?_
      rw [← hgdiv]
      exact Algebra.subset_adjoin (Or.inr ⟨b, rfl⟩)
    · intro j hj
      have hsj : s j ≠ 0 := by
        intro h0; apply hj; simp [g, h0]
      rw [hgt]
      exact ht j hsj

theorem secs_eq_secOver (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω)
    (hgen : IsGraphGen Q n s) :
    Q.secs = secOver S (graphVec x s) (graphDeg n) := by
  ext t
  rw [mem_secs_iff, mem_secOver_graph_iff]
  simp only [graphDeg_inl, graphDeg_inr, neg_neg, zpow_neg, zpow_one]
  constructor
  · intro h i j hi hj
    exact (mem_sub_iff_graph Q n s hgen hi t).mp (h i hi) j hj
  · intro h i hi
    exact (mem_sub_iff_graph Q n s hgen hi t).mpr fun j hj => h i j hi hj

theorem twist_secs_eq_secOver (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω)
    (hgen : IsGraphGen Q n s) (c : ℤ) :
    (Q.twist (Kleiman.twistSys S x c)).secs =
      secOver S (graphVec x s) (graphDeg n + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg baseBlock) := by
  ext t
  rw [mem_secs_iff, mem_secOver_graph_iff]
  have hb1 : (graphDeg n + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg baseBlock) (Sum.inl ()) = -n + c := by
    simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  have hb2 : (graphDeg n + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg baseBlock) (Sum.inr ()) = 1 := by
    simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  rw [hb1, hb2]
  have key : ∀ i (hi : x i ≠ 0), t ∈ (Q.twist (Kleiman.twistSys S x c)).sub (Kleiman.singleChart hi) ↔
      x i ^ (-c) * t ∈ Q.sub (Kleiman.singleChart hi) := by
    intro i hi
    rw [TranslateEq.mem_twist_twistSys_iff Q.toSubSystem c _ (Finset.mem_singleton_self i)]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : x i ^ (-c) * x i ^ c • y = y := by
        rw [smul_eq_mul, zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero c hi), one_mul]
      rw [this]; exact hy
    · intro h
      refine ⟨_, h, ?_⟩
      rw [smul_eq_mul, zpow_neg, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero c hi), one_mul]
  have hmul : ∀ i j, x i ≠ 0 → x i ^ (-c) * t * (x i ^ n * (s j)⁻¹) =
      t * (x i ^ (-(-n + c)) * s j ^ (-(1 : ℤ))) := by
    intro i j hi
    rw [zpow_neg_one, show -(-n + c) = n + -c by ring, zpow_add₀ hi]
    ring
  constructor
  · intro h i j hi hj
    rw [← hmul i j hi]
    exact (mem_sub_iff_graph Q n s hgen hi _).mp ((key i hi).mp (h i hi)) j hj
  · intro h i hi
    refine (key i hi).mpr ((mem_sub_iff_graph Q n s hgen hi _).mpr fun j hj => ?_)
    rw [hmul i j hi]
    exact h i j hi hj

end Sections

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
