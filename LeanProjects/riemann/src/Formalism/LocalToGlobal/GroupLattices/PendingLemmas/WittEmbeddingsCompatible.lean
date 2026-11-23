import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ICIntCp

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable (p : ℕ) [hp : Fact p.Prime]

def OcC : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by
    show ‖(1 : ℂ_[p])‖ ≤ 1
    rw [norm_one]
  add_mem' := fun {a b} ha hb => by
    show ‖a + b‖ ≤ 1
    exact le_trans (IsUltrametricDist.norm_add_le_max a b) (max_le ha hb)
  zero_mem' := by
    show ‖(0 : ℂ_[p])‖ ≤ 1
    rw [norm_zero]
    exact zero_le_one
  neg_mem' := fun {a} ha => by
    show ‖-a‖ ≤ 1
    rw [norm_neg]
    exact ha

variable {p}

theorem mem_OcC (x : ℂ_[p]) : x ∈ OcC p ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem OcC_val (x : ℂ_[p]) : x ∈ OcC p ∨ x⁻¹ ∈ OcC p := by
  rcases le_total ‖x‖ 1 with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    show ‖x⁻¹‖ ≤ 1
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ h

theorem norm_p_pos : 0 < ‖(p : ℂ_[p])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)

theorem OcC_rank1 (x : ℂ_[p]) (hx : x ≠ 0) :
    (∃ n : ℕ, (p : ℂ_[p]) ^ n / x ∈ OcC p) ∧ (x⁻¹ ∉ OcC p → ∃ n : ℕ, x ^ n / (p : ℂ_[p]) ∈ OcC p) := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  constructor
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx0 (norm_p_lt_one (p := p))
    refine ⟨n, ?_⟩
    show ‖(p : ℂ_[p]) ^ n / x‖ ≤ 1
    rw [norm_div, norm_pow, div_le_one hx0]
    exact hn.le
  · intro h
    have h1 : ‖x‖ < 1 := by
      by_contra hc
      refine h ?_
      show ‖x⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (not_lt.1 hc)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_p_pos (p := p)) h1
    refine ⟨n, ?_⟩
    show ‖x ^ n / (p : ℂ_[p])‖ ≤ 1
    rw [norm_div, norm_pow, div_le_one norm_p_pos]
    exact hn.le

section Emb

variable {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (i : Kf →+* ℂ_[p]) (hi : ∀ x : O, ‖i (algebraMap O Kf x)‖ ≤ 1)

include hi

theorem norm_unit (u : Oˣ) : ‖i (algebraMap O Kf (u : O))‖ = 1 := by
  refine le_antisymm (hi _) ?_
  have h1 : i (algebraMap O Kf (u : O)) * i (algebraMap O Kf ((u⁻¹ : Oˣ) : O)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one] at h2
  calc (1 : ℝ) = ‖i (algebraMap O Kf (u : O))‖ * ‖i (algebraMap O Kf ((u⁻¹ : Oˣ) : O))‖ := h2.symm
    _ ≤ ‖i (algebraMap O Kf (u : O))‖ * 1 := mul_le_mul_of_nonneg_left (hi _) (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_nonunit {y : O} (hy : ¬ IsUnit y) : ‖i (algebraMap O Kf y)‖ < 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp0 : (p : O) ≠ 0 := by
    intro h0
    have := congrArg (fun z => i (algebraMap O Kf z)) h0
    simp only [map_natCast, map_zero] at this
    exact (Nat.cast_ne_zero.2 hp.out.ne_zero : (p : ℂ_[p]) ≠ 0) this
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  obtain ⟨u, hu⟩ := he.symm
  have hϖ1 : ‖i (algebraMap O Kf ϖ)‖ < 1 := by
    by_contra hc
    have h1 : ‖i (algebraMap O Kf ϖ)‖ = 1 := le_antisymm (hi _) (not_lt.1 hc)
    have h2 := congrArg (fun t => ‖i (algebraMap O Kf t)‖) hu
    simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h2
    rw [h1, norm_unit i hi u, one_pow, one_mul] at h2
    exact absurd h2.symm (ne_of_lt (norm_p_lt_one (p := p)))
  have hy1 : ϖ ∣ y := by
    have : y ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal y).2 hy
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    exact this
  obtain ⟨z, rfl⟩ := hy1
  rw [map_mul, map_mul, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hi z)) hϖ1

theorem norm_le_one_iff [IsFractionRing O Kf] (x : Kf) : ‖i x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap O Kf) := by
  constructor
  · intro hx
    rcases ValuationRing.isInteger_or_isInteger O x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨y, hy⟩
    · by_cases hx0 : x = 0
      · exact ⟨0, by rw [hx0, map_zero]⟩
      by_cases hu : IsUnit y
      · obtain ⟨u, rfl⟩ := hu
        refine ⟨((u⁻¹ : Oˣ) : O), ?_⟩
        have h1 : algebraMap O Kf ((u⁻¹ : Oˣ) : O) * algebraMap O Kf (u : O) = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        rw [hy] at h1
        exact (eq_of_mul_inv_eq_one h1)
      · exfalso
        have h1 := norm_nonunit i hi hu
        rw [hy, map_inv₀, norm_inv] at h1
        have hpos : 0 < ‖i x‖ := norm_pos_iff.2 ((map_ne_zero i).2 hx0)
        exact absurd h1 (not_lt.2 ((one_le_inv₀ hpos).2 hx))
  · rintro ⟨y, rfl⟩
    exact hi y

end Emb

structure CEmb (G : GAtP p) where
  iK : G.Kf →+* ℂ_[p]
  int : ∀ x : G.O, ‖iK (algebraMap G.O G.Kf x)‖ ≤ 1

theorem CEmb.mem_iff {X : Sys p} (E : CEmb X.G) [IsFractionRing X.G.O X.G.Kf] (x : X.G.Kf) :
    E.iK x ∈ OcC p ↔ x ∈ X.intK := by
  rw [mem_OcC, norm_le_one_iff E.iK E.int]
  rfl

section Conc

variable {n : ℕ} (f : K0 p →+* ℂ_[p]) (hf : ∀ x : WW p, ‖f (algebraMap (WW p) (K0 p) x)‖ ≤ 1)
  (L : IntermediateField (KO p n) (Om p n)) [FiniteDimensional (KO p n) L]

def embLC : L →+* ℂ_[p] := (iC f).comp (gL L)

include hf in
theorem embLC_int (x : OL p n L) : ‖embLC f L (algebraMap (OL p n L) L x)‖ ≤ 1 :=
  (iC_int_Cp f hf _).1 ((Oc_K L _).2 ⟨x, rfl⟩)

theorem witt_embeddings_compatible (a : W2 p n) :
    embLC f L (algebraMap (OO p n) L (algebraMap (W2 p n) (OO p n) a)) =
      f (algebraMap (WW p) (K0 p) (gWW p n a)) := by
  show iC f (gL L _) = _
  rw [intermediate_map_witt_quadratic, iC_alg]

end Conc

end Formalism.L2.G.Pend
