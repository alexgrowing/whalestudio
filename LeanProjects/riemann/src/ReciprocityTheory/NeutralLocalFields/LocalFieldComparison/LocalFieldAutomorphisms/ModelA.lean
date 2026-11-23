import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.MemRangeOfAevalRatEqZero

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

def locVal (ι : Ω →+* PadicAlgCl p) : Valuation (Kloc F ι) NNReal :=
  (PadicAlgCl.valued p).v.comap (algebraMap (Kloc F ι) (PadicAlgCl p))

theorem locVal_apply (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) : ((locVal ι x : NNReal) : ℝ) = ‖(x : PadicAlgCl p)‖ :=
  rfl

@[instance_reducible]
def locRel (ι : Ω →+* PadicAlgCl p) : ValuativeRel (Kloc F ι) := .ofValuation (locVal ι)

attribute [local instance] locRel

theorem locVal_compat (ι : Ω →+* PadicAlgCl p) : (locVal (F := F) ι).Compatible := Valuation.Compatible.ofValuation _

theorem valuation_lt_iff_Kloc (ι : Ω →+* PadicAlgCl p) (x y : Kloc F ι) :
    valuation (Kloc F ι) x < valuation (Kloc F ι) y ↔ ‖(x : PadicAlgCl p)‖ < ‖(y : PadicAlgCl p)‖ := by
  have := locVal_compat (F := F) ι
  rw [(ValuativeRel.isEquiv (valuation (Kloc F ι)) (locVal ι)).lt_iff_lt, ← NNReal.coe_lt_coe,
    locVal_apply, locVal_apply]

theorem valuation_le_iff_Kloc (ι : Ω →+* PadicAlgCl p) (x y : Kloc F ι) :
    valuation (Kloc F ι) x ≤ valuation (Kloc F ι) y ↔ ‖(x : PadicAlgCl p)‖ ≤ ‖(y : PadicAlgCl p)‖ := by
  rw [← not_lt, valuation_lt_iff_Kloc, not_lt]

theorem norm_natCast_p_Kloc (ι : Ω →+* PadicAlgCl p) : ‖(((p : ℕ) : Kloc F ι) : PadicAlgCl p)‖ < 1 := by
  have h : (((p : ℕ) : Kloc F ι) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by
    simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem mem_integer_Kloc (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) :
    x ∈ 𝒪[Kloc F ι] ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by
  have h := valuation_le_iff_Kloc ι x 1
  rw [map_one] at h
  rw [Valuation.mem_integer_iff, h]
  simp

theorem isNonarchimedeanLocalField_Kloc (ι : Ω →+* PadicAlgCl p) : IsNonarchimedeanLocalField (Kloc F ι) := by
  have : FiniteDimensional ℚ_[p] (Kloc F ι) := finiteDimensional_Kloc ι
  have : ProperSpace (Kloc F ι) := FiniteDimensional.proper ℚ_[p] (Kloc F ι)
  set q : Kloc F ι := ((p : ℕ) : Kloc F ι) with hq
  have hq1 : ‖(q : PadicAlgCl p)‖ < 1 := norm_natCast_p_Kloc ι
  have hq0 : q ≠ 0 := by
    rw [hq]; exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hqn : 0 < ‖(q : PadicAlgCl p)‖ := by
    rw [norm_pos_iff]; exact_mod_cast hq0
  have hnt : ValuativeRel.IsNontrivial (Kloc F ι) := by
    refine ⟨⟨valuation (Kloc F ι) q, ?_, ?_⟩⟩
    · simpa using hq0
    · intro h
      have := (valuation_lt_iff_Kloc ι q 1).2 (by simpa using hq1)
      rw [h, map_one] at this
      exact lt_irrefl _ this
  have hvt : IsValuativeTopology (Kloc F ι) := by
    constructor
    intro s x
    rw [Metric.mem_nhds_iff]
    constructor
    · rintro ⟨ε, hε, hs⟩
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hq1
      have hqn0 : q ^ n ≠ 0 := pow_ne_zero _ hq0
      refine ⟨Units.mk0 (valuation (Kloc F ι) (q ^ n)) (by simpa using hqn0), ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      apply hs
      rw [Set.mem_ofPred_eq, Units.val_mk0, valuation_lt_iff_Kloc] at hz
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      calc ‖z‖ = ‖(z : PadicAlgCl p)‖ := rfl
        _ < ‖((q ^ n : Kloc F ι) : PadicAlgCl p)‖ := hz
        _ = ‖(q : PadicAlgCl p)‖ ^ n := by simp
        _ < ε := hn
    · rintro ⟨γ, hγ⟩
      obtain ⟨y, hy⟩ := valuation_surjective (γ : ValueGroupWithZero (Kloc F ι))
      have hy0 : y ≠ 0 := by
        rintro rfl; simp at hy; exact γ.ne_zero hy.symm
      refine ⟨‖(y : PadicAlgCl p)‖, by rw [gt_iff_lt, norm_pos_iff]; exact_mod_cast hy0, fun w hw => hγ ?_⟩
      refine ⟨w - x, ?_, by simp⟩
      rw [Set.mem_ofPred_eq, ← hy, valuation_lt_iff_Kloc]
      rw [Metric.mem_ball, dist_eq_norm] at hw
      exact hw
  exact { toIsValuativeTopology := hvt, toLocallyCompactSpace := inferInstance, toIsNontrivial := hnt }

end ReciprocityTheory.Neutral.Cmp
