import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionLocal
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionPowers
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

def redSys (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (P : SubSystem k x Ω) (γ : Ω) : SubSystem k y K' where
  sub I := Submodule.span (chartRing k y I)
    ((fun q => redAt k x y (q / γ)) '' P.sub (liftChart hxy I))
  mono I J h z hz := by
    refine Submodule.span_induction (p := fun z _ => z ∈ Submodule.span (chartRing k y J)
      ((fun q => redAt k x y (q / γ)) '' P.sub (liftChart hxy J))) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, rfl⟩
      exact Submodule.subset_span ⟨q, P.mono _ _ h q hq, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact Submodule.smul_mem _ (chartIncl h a) hz

def RedGood (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (P : SubSystem k x Ω) (γ : Ω) : Prop :=
  ∀ (I : Chart y), ∀ q ∈ P.sub (liftChart hxy I), q / γ ∈ locAt k x y

variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp

theorem mem_redSys_iff {P : SubSystem k x Ω} {γ : Ω} (hP : RedGood hxy P γ) (I : Chart y) (z : K') :
    z ∈ (redSys hxy P γ).sub I ↔ ∃ q ∈ P.sub (liftChart hxy I), redAt k x y (q / γ) = z := by
  constructor
  · intro hz
    refine Submodule.span_induction (p := fun z _ => ∃ q ∈ P.sub (liftChart hxy I),
      redAt k x y (q / γ) = z) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
    · exact ⟨0, Submodule.zero_mem _, by rw [zero_div]; exact (locAt_zero hsp).2⟩
    · rintro u v _ _ ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
      refine ⟨q + q', Submodule.add_mem _ hq hq', ?_⟩
      rw [add_div]; exact (locAt_add hsp (hP I q hq) (hP I q' hq')).2
    · rintro c u _ ⟨q, hq, rfl⟩
      obtain ⟨a, ha, hac⟩ := exists_redAt_eq hsp hxy I c.2
      refine ⟨a * q, ?_, ?_⟩
      · have := Submodule.smul_mem _ (⟨a, ha⟩ : chartRing k x (liftChart hxy I)) hq
        rwa [chartRing_smul_def] at this
      · rw [chartRing_smul_def, ← hac, mul_div_assoc]
        exact (locAt_mul hsp (chartRing_sub_locAt hsp hxy I ha).1 (hP I q hq)).2
  · rintro ⟨q, hq, rfl⟩; exact Submodule.subset_span ⟨q, hq, rfl⟩

theorem redGood_twist {P Q : SubSystem k x Ω} {γ δ : Ω} (hP : RedGood hxy P γ)
    (hQ : RedGood hxy Q δ) : RedGood hxy (P.twist Q) (γ * δ) := by
  intro I z hz
  refine Submodule.span_induction (p := fun z _ => z / (γ * δ) ∈ locAt k x y) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, p, hp, rfl⟩
    have : q • p / (γ * δ) = q / δ * (p / γ) := by rw [smul_eq_mul]; ring
    rw [this]; exact (locAt_mul hsp (hQ I q hq) (hP I p hp)).1
  · rw [zero_div]; exact (locAt_zero hsp).1
  · intro u v _ _ hu hv; rw [add_div]; exact (locAt_add hsp hu hv).1
  · intro c u _ hu
    rw [chartRing_smul_def, mul_div_assoc]
    exact (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 hu).1

theorem redSys_twist {P Q : SubSystem k x Ω} {γ δ : Ω} (hP : RedGood hxy P γ)
    (hQ : RedGood hxy Q δ) :
    redSys hxy (P.twist Q) (γ * δ) = (redSys hxy P γ).twist (redSys hxy Q δ) := by
  have hPQ := redGood_twist hsp hxy hP hQ
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    refine Submodule.span_induction (p := fun z _ => redAt k x y (z / (γ * δ)) ∈
      ((redSys hxy P γ).twist (redSys hxy Q δ)).sub I) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, p, hp, rfl⟩
      have : q • p / (γ * δ) = q / δ * (p / γ) := by rw [smul_eq_mul]; ring
      rw [this, (locAt_mul hsp (hQ I q hq) (hP I p hp)).2]
      exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨q, hq, rfl⟩, _,
        Submodule.subset_span ⟨p, hp, rfl⟩, rfl⟩
    · rw [zero_div, (locAt_zero hsp).2]; exact Submodule.zero_mem _
    · intro u v hu hv ihu ihv
      rw [add_div, (locAt_add hsp (hPQ I u hu) (hPQ I v hv)).2]
      exact Submodule.add_mem _ ihu ihv
    · intro c u hu ihu
      rw [chartRing_smul_def, mul_div_assoc,
        (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 (hPQ I u hu)).2]
      have := Submodule.smul_mem _ (⟨_, (chartRing_sub_locAt hsp hxy I c.2).2⟩ : chartRing k y I) ihu
      rwa [chartRing_smul_def] at this
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q', hq', p', hp', rfl⟩
    obtain ⟨q, hq, rfl⟩ := (mem_redSys_iff hsp hxy hQ I q').mp hq'
    obtain ⟨p, hp, rfl⟩ := (mem_redSys_iff hsp hxy hP I p').mp hp'
    have : q • p / (γ * δ) = q / δ * (p / γ) := by rw [smul_eq_mul]; ring
    refine Submodule.subset_span ⟨q • p, Submodule.subset_span ⟨q, hq, p, hp, rfl⟩, ?_⟩
    change redAt k x y (q • p / (γ * δ)) = redAt k x y (q / δ) * redAt k x y (p / γ)
    rw [this, (locAt_mul hsp (hQ I q hq) (hP I p hp)).2]

theorem redGood_twistSys_zero : RedGood hxy (twistSys k x 0) 1 := by
  intro I q hq
  rw [div_one]; exact (chartRing_sub_locAt hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hq)).1

theorem redSys_twistSys_zero : redSys hxy (twistSys k x 0) 1 = twistSys k y 0 := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    change redAt k x y (q / 1) ∈ twistMod k y 0 I
    rw [div_one]
    exact res_mem_twistMod_zero_of_mem_chartRing
      (chartRing_sub_locAt hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hq)).2
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := exists_redAt_eq hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hz)
    exact Submodule.subset_span ⟨a, res_mem_twistMod_zero_of_mem_chartRing ha, by
      change redAt k x y (a / 1) = redAt k x y a
      rw [div_one]⟩

theorem redSys_pow {P : SubSystem k x Ω} {γ : Ω} (hP : RedGood hxy P γ) (n : ℕ) :
    RedGood hxy (P.pow n) (γ ^ n) ∧ redSys hxy (P.pow n) (γ ^ n) = (redSys hxy P γ).pow n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ⟨redGood_twistSys_zero hsp hxy, redSys_twistSys_zero hsp hxy⟩
  | succ n ih =>
    rw [pow_succ]
    change RedGood hxy ((P.pow n).twist P) (γ ^ n * γ) ∧
      redSys hxy ((P.pow n).twist P) (γ ^ n * γ) = ((redSys hxy P γ).pow n).twist (redSys hxy P γ)
    exact ⟨redGood_twist hsp hxy ih.1 hP, by rw [redSys_twist hsp hxy ih.1 hP, ih.2]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
