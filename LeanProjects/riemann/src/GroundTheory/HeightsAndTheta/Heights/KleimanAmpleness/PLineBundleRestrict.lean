import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LineBundleRestrictSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionBundle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

def restrictUnion (I J : Chart y) : Chart y :=
  ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩

variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp

theorem redAt_isUnit_of_isUnit {I J : Chart y} (h : I.1 ⊆ J.1)
    (a : chartRing k x (liftChart hxy I))
    (ha : IsUnit (chartIncl (S := k) (x := x) (I := liftChart hxy I) (J := liftChart hxy J) h a)) :
    (a : Ω) ∈ locAt k x y ∧ ∃ b ∈ chartRing k y J, redAt k x y a * b = 1 := by
  obtain ⟨c, hc⟩ := ha.exists_right_inv
  have hc' : (a : Ω) * (c : Ω) = 1 := congrArg Subtype.val hc
  have haL := chartRing_sub_locAt hsp hxy I a.2
  have hcL := chartRing_sub_locAt hsp hxy J c.2
  refine ⟨haL.1, _, hcL.2, ?_⟩
  rw [← (locAt_mul hsp haL.1 hcL.1).2, hc', (locAt_one hsp).2]

theorem exists_mul_mem_of_mem_restrictUnion (Q : LineBundle k x) (I J : Chart y) {z : Ω}
    (hz : z ∈ Q.sub (liftChart hxy (restrictUnion I J))) :
    ∃ a ∈ chartRing k x (liftChart hxy I), a ∈ locAt k x y ∧ redAt k x y a ≠ 0 ∧
      a * z ∈ Q.sub (liftChart hxy I) := by
  have hIJ : I.1 ⊆ (restrictUnion I J).1 := Finset.subset_union_left
  obtain ⟨a, ha, haz⟩ := (Q.mem_iff (liftChart hxy I) (liftChart hxy (restrictUnion I J)) hIJ z).mp hz
  obtain ⟨haL, b, -, hb⟩ := redAt_isUnit_of_isUnit hsp hxy hIJ a ha
  rw [smul_eq_mul] at haz
  exact ⟨a, a.2, haL, left_ne_zero_of_mul_eq_one hb, haz⟩

theorem exists_restrict_gen (Q : LineBundle k x) :
    ∃ γ : Ω, γ ≠ 0 ∧ RedGood hxy Q.toSubSystem γ ∧ ∀ I : Chart y,
      ∃ b ∈ chartRing k x (liftChart hxy I), b ∈ locAt k x y ∧ redAt k x y b ≠ 0 ∧
        b * γ ∈ Q.sub (liftChart hxy I) := by
  by_cases hI : Nonempty (Chart y)
  swap
  · exact ⟨1, one_ne_zero, fun I => (hI ⟨I⟩).elim, fun I => (hI ⟨I⟩).elim⟩
  obtain ⟨I₀⟩ := hI
  obtain ⟨M, hM⟩ := Q.invertible (liftChart hxy I₀)
  have hA : ∀ {q m : Ω}, q ∈ Q.sub (liftChart hxy I₀) → m ∈ M → q * m ∈ locAt k x y :=
    fun hq hm => (chartRing_sub_locAt hsp hxy I₀ (mul_mem_chartRing_of_mul_eq_one hM hq hm)).1
  have h1 : (1 : Ω) ∈ Q.sub (liftChart hxy I₀) * M := by
    rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨γ, hγ, m₀, hm₀, hne⟩ :
      ∃ γ ∈ Q.sub (liftChart hxy I₀), ∃ m₀ ∈ M, redAt k x y (γ * m₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z = 0) h1
      (fun q hq m hm => ⟨hA hq hm, hcon q hq m hm⟩)
      (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
        rw [(locAt_add hsp hu.1 hv.1).2, hu.2, hv.2, add_zero]⟩)
    rw [(locAt_one hsp).2] at this
    exact one_ne_zero this.2
  have hγm := hA hγ hm₀
  have hγm0 := (locAt_inv hsp hγm hne).1
  have hγ0 : γ ≠ 0 := left_ne_zero_of_mul hγm0
  have hm0 : m₀ ≠ 0 := right_ne_zero_of_mul hγm0
  refine ⟨γ, hγ0, ?_, ?_⟩
  · intro I q hq
    have hsub : I.1 ⊆ (restrictUnion I₀ I).1 := Finset.subset_union_right
    obtain ⟨a, -, haL, har, haq⟩ := exists_mul_mem_of_mem_restrictUnion hsp hxy Q I₀ I
      (Q.mono (liftChart hxy I) (liftChart hxy (restrictUnion I₀ I)) hsub q hq)
    have ha0 : a ≠ 0 := (locAt_inv hsp haL har).1
    have hnum := hA haq hm₀
    have hden := locAt_mul hsp haL hγm
    have hden0 : redAt k x y (a * (γ * m₀)) ≠ 0 := by rw [hden.2]; exact mul_ne_zero har hne
    have heq : q / γ = a * q * m₀ / (a * (γ * m₀)) := by
      rw [mul_assoc a q m₀, mul_div_mul_left _ _ ha0, mul_div_mul_right _ _ hm0]
    rw [heq]; exact (locAt_div hsp hnum hden.1 hden0).1
  · intro I
    have hsub : I₀.1 ⊆ (restrictUnion I I₀).1 := Finset.subset_union_right
    exact exists_mul_mem_of_mem_restrictUnion hsp hxy Q I I₀
      (Q.mono (liftChart hxy I₀) (liftChart hxy (restrictUnion I I₀)) hsub γ hγ)

variable {γ : Ω} {Q : LineBundle k x}

theorem redSys_sub_eq_span (hg : RedGood hxy Q.toSubSystem γ) (I : Chart y) {s : Set Ω}
    (hs : Submodule.span (chartRing k x (liftChart hxy I)) s = Q.sub (liftChart hxy I)) :
    (redSys hxy Q.toSubSystem γ).sub I =
      Submodule.span (chartRing k y I) ((fun q => redAt k x y (q / γ)) '' s) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    have hq' : q ∈ Submodule.span (chartRing k x (liftChart hxy I)) s := by rw [hs]; exact hq
    refine Submodule.span_induction (p := fun q _ => redAt k x y (q / γ) ∈
      Submodule.span (chartRing k y I) ((fun q => redAt k x y (q / γ)) '' s)) ?_ ?_ ?_ ?_ hq'
    · intro q hq; exact Submodule.subset_span ⟨q, hq, rfl⟩
    · rw [zero_div, (locAt_zero hsp).2]; exact Submodule.zero_mem _
    · intro u v hu hv ihu ihv
      rw [add_div, (locAt_add hsp (hg I u (hs ▸ hu)) (hg I v (hs ▸ hv))).2]
      exact Submodule.add_mem _ ihu ihv
    · intro c u hu ihu
      rw [chartRing_smul_def, mul_div_assoc,
        (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 (hg I u (hs ▸ hu))).2]
      have := Submodule.smul_mem _ (⟨_, (chartRing_sub_locAt hsp hxy I c.2).2⟩ : chartRing k y I) ihu
      rwa [chartRing_smul_def] at this
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    have hq' : q ∈ Q.sub (liftChart hxy I) := by rw [← hs]; exact Submodule.subset_span hq
    exact Submodule.subset_span ⟨q, hq', rfl⟩

theorem redSys_mem_iff (hg : RedGood hxy Q.toSubSystem γ) (I J : Chart y) (h : I.1 ⊆ J.1) (z : K') :
    z ∈ (redSys hxy Q.toSubSystem γ).sub J ↔ ∃ c : chartRing k y I, IsUnit (chartIncl h c) ∧
      (c : K') • z ∈ (redSys hxy Q.toSubSystem γ).sub I := by
  constructor
  · intro hz
    obtain ⟨q, hq, rfl⟩ := (mem_redSys_iff hsp hxy hg J z).mp hz
    obtain ⟨b, hb, hbq⟩ := (Q.mem_iff (liftChart hxy I) (liftChart hxy J) h q).mp hq
    obtain ⟨hbL, b', hb'A, hbb'⟩ := redAt_isUnit_of_isUnit hsp hxy h b hb
    have hbI := (chartRing_sub_locAt hsp hxy I b.2).2
    refine ⟨⟨_, hbI⟩, IsUnit.of_mul_eq_one ⟨b', hb'A⟩ (Subtype.ext hbb'), ?_⟩
    rw [smul_eq_mul] at hbq
    change redAt k x y b * redAt k x y (q / γ) ∈ (redSys hxy Q.toSubSystem γ).sub I
    rw [← (locAt_mul hsp hbL (hg J q hq)).2, ← mul_div_assoc]
    exact Submodule.subset_span ⟨_, hbq, rfl⟩
  · rintro ⟨c, hc, hcz⟩
    obtain ⟨c', hc'⟩ := hc.exists_left_inv
    have hc'' : (c' : K') * (c : K') = 1 := congrArg Subtype.val hc'
    have := Submodule.smul_mem _ c' ((redSys hxy Q.toSubSystem γ).mono I J h _ hcz)
    rwa [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hc'', one_mul] at this

theorem redSys_invertible (hγ0 : γ ≠ 0) (hg : RedGood hxy Q.toSubSystem γ) (I : Chart y)
    (hb : ∃ b ∈ chartRing k x (liftChart hxy I), b ∈ locAt k x y ∧ redAt k x y b ≠ 0 ∧
      b * γ ∈ Q.sub (liftChart hxy I)) :
    ∃ M' : Submodule (chartRing k y I) K', (redSys hxy Q.toSubSystem γ).sub I * M' = 1 := by
  obtain ⟨b, -, hbL, hbr, hbγ⟩ := hb
  obtain ⟨M, hM⟩ := Q.invertible (liftChart hxy I)
  refine ⟨Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * γ)) '' M), ?_⟩
  have hA : ∀ {q m : Ω}, q ∈ Q.sub (liftChart hxy I) → m ∈ M →
      q * m ∈ chartRing k x (liftChart hxy I) :=
    fun hq hm => mul_mem_chartRing_of_mul_eq_one hM hq hm
  have hb0 : b ≠ 0 := (locAt_inv hsp hbL hbr).1
  have hmg : ∀ {m : Ω}, m ∈ M → m * γ ∈ locAt k x y := by
    intro m hm
    have h1 := (chartRing_sub_locAt hsp hxy I (hA hbγ hm)).1
    have heq : m * γ = b * γ * m / b := by rw [eq_div_iff hb0]; ring
    rw [heq]; exact (locAt_div hsp h1 hbL hbr).1
  have hsplit : ∀ q m : Ω, q * m = q / γ * (m * γ) := fun q m => by field_simp
  apply le_antisymm
  · change Submodule.span _ _ * Submodule.span _ _ ≤ 1
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨q, hq, rfl⟩, _, ⟨m, hm, rfl⟩, rfl⟩
    show redAt k x y (q / γ) * redAt k x y (m * γ) ∈ (1 : Submodule (chartRing k y I) K')
    rw [← (locAt_mul hsp (hg I q hq) (hmg hm)).2, ← hsplit]
    exact Submodule.mem_one.mpr ⟨⟨_, (chartRing_sub_locAt hsp hxy I (hA hq hm)).2⟩, rfl⟩
  · rw [Submodule.one_le]
    have h1 : (1 : Ω) ∈ Q.sub (liftChart hxy I) * M := by
      rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z ∈
        (redSys hxy Q.toSubSystem γ).sub I *
          Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * γ)) '' M)) h1
      (fun q hq m hm => ⟨(chartRing_sub_locAt hsp hxy I (hA hq hm)).1, by
        rw [hsplit, (locAt_mul hsp (hg I q hq) (hmg hm)).2]
        exact Submodule.mul_mem_mul (Submodule.subset_span ⟨q, hq, rfl⟩)
          (Submodule.subset_span ⟨m, hm, rfl⟩)⟩)
      (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
        rw [(locAt_add hsp hu.1 hv.1).2]; exact Submodule.add_mem _ hu.2 hv.2⟩)
    rw [(locAt_one hsp).2] at this
    exact this.2

omit hsp in

theorem LineBundleRestrict.proof : LineBundleRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hsp Q
  obtain ⟨γ, hγ0, hg, hb⟩ := exists_restrict_gen hsp hxy Q
  refine ⟨LineBundle.mk (SubFamily.mk (redSys hxy Q.toSubSystem γ) (redSys_mem_iff hsp hxy hg)) ?_ ?_,
    _, restrictData_redSys hsp hxy hg _ rfl⟩
  · intro I
    obtain ⟨s, hs⟩ := Q.fg (liftChart hxy I)
    rw [redSys_sub_eq_span hsp hxy hg I hs]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · intro I
    exact redSys_invertible hsp hxy hγ0 hg I (hb I)

end

end GroundTheory.Heights₂.Heights.Kleiman
