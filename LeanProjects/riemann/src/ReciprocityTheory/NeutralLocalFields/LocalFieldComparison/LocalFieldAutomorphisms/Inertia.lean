import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ContinuousGK

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem norm_add_le_max_padic (x y : PadicAlgCl p) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ :=
  PadicAlgCl.isNonarchimedean p x y

theorem padicAlgCl_norm_sub_le_max (x y : PadicAlgCl p) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg] using norm_add_le_max_padic x (-y)

variable (F) in
include F in
theorem exists_integral_approx {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι)
    (x : PadicAlgCl p) (hx : ‖x‖ ≤ 1) : ∃ b : Ω, b ∈ A ∧ ‖x - ι b‖ < 1 := by
  obtain ⟨b, hb⟩ := (Metric.denseRange_iff.mp (denseRange F ι)) x 1 one_pos
  rw [dist_eq_norm] at hb
  refine ⟨b, (h b).2 ?_, hb⟩
  have e : ι b = x - (x - ι b) := by ring
  rw [e]
  exact (padicAlgCl_norm_sub_le_max _ _).trans (max_le hx hb.le)

theorem norm_sub_lt_one_of_dense {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) (σ : GK F ι)
    (g : PadicAlgCl p → PadicAlgCl p)
    (hg : ∀ x y : PadicAlgCl p, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖g x - g y‖ ≤ ‖x - y‖)
    (H : ∀ b ∈ A, ‖σ (ι b) - g (ι b)‖ < 1) (x : PadicAlgCl p) (hx : ‖x‖ ≤ 1) :
    ‖σ x - g x‖ < 1 := by
  obtain ⟨b, hb, hxb⟩ := exists_integral_approx F h x hx
  have hyb : ‖ι b‖ ≤ 1 := (h b).1 hb
  have e : σ x - g x = σ (x - ι b) + ((σ (ι b) - g (ι b)) + (g (ι b) - g x)) := by
    rw [map_sub]; ring
  rw [e]
  have h1 : ‖σ (x - ι b)‖ < 1 := by rw [norm_map_GK]; exact hxb
  have h3 : ‖g (ι b) - g x‖ < 1 := by
    refine (hg _ _ hyb hx).trans_lt ?_
    rw [norm_sub_rev]; exact hxb
  refine (norm_add_le_max_padic _ _).trans_lt (max_lt h1 ?_)
  exact (norm_add_le_max_padic _ _).trans_lt (max_lt (H b hb) h3)

theorem res_mem_ine_iff {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) (σ : GK F ι) :
    res ι σ ∈ Ine (F := F) A ↔ ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by
  constructor
  · rintro ⟨-, h2⟩
    refine norm_sub_lt_one_of_dense h σ id (fun x y _ _ => le_rfl) ?_
    intro b hb
    have := (h.valuation_lt_one_iff _).1 (h2 b ((A.valuation_le_one_iff b).2 hb))
    rwa [map_sub, res_spec] at this
  · intro H
    refine ⟨res_mem_dec h σ, fun b hb => (h.valuation_lt_one_iff _).2 ?_⟩
    rw [map_sub, res_spec]
    exact H _ ((h b).1 ((A.valuation_le_one_iff b).1 hb))

theorem cycZ_res (ι : Ω →+* PadicAlgCl p) (l : ℕ) [Fact l.Prime] (σ : GK F ι) :
    cycZ F Ω l (res ι σ) = cyclotomicCharacter (PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have : NeZero (l : ℚ_[p]) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  change (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut _ Ω (res ι σ))).val.toZModPow n = _
  rw [cyclotomicCharacter.toZModPow]
  refine (modularCyclotomicCharacter.unique _ _ _ ?_).symm
  intro t ht
  apply ι.injective
  have ht' : (t : Ω) ^ l ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]
  have h1 : ι (t : Ω) ^ l ^ n = 1 := by rw [← map_pow, ht', map_one]
  have := cyclotomicCharacter.spec (L := PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p) (ι t) h1
  rw [map_pow]
  change ι (res ι σ t) = _
  rw [res_spec]
  exact this

theorem norm_le_one_iff_isIntegral (x : PadicAlgCl p) : ‖x‖ ≤ 1 ↔ IsIntegral (PadicInt.subring p) x := by
  have hint : IsIntegral ℚ_[p] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hm := minpoly.monic hint
  change spectralValue (minpoly ℚ_[p] x) ≤ 1 ↔ _
  rw [spectralValue_le_one_iff hm]
  constructor
  · intro hc
    have hl : minpoly ℚ_[p] x ∈ Polynomial.lifts (PadicInt.subring p).subtype := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
    refine ⟨q, hqm, ?_⟩
    have e : algebraMap (PadicInt.subring p) (PadicAlgCl p) =
        (algebraMap ℚ_[p] (PadicAlgCl p)).comp (PadicInt.subring p).subtype := rfl
    rw [e, ← Polynomial.eval₂_map, hq]
    exact minpoly.aeval ℚ_[p] x
  · rintro ⟨q, hqm, he⟩
    set P := q.map (PadicInt.subring p).subtype
    have hPm : P.Monic := hqm.map _
    have hP : Polynomial.aeval x P = 0 := by
      have e : algebraMap (PadicInt.subring p) (PadicAlgCl p) =
          (algebraMap ℚ_[p] (PadicAlgCl p)).comp (PadicInt.subring p).subtype := rfl
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← e]
      exact he
    have h1 : spectralNorm ℚ_[p] (PadicAlgCl p) x ≤ spectralValue P :=
      norm_root_le_spectralValue (f := spectralAlgNorm ℚ_[p] (PadicAlgCl p))
        spectralAlgNorm_isPowMul isNonarchimedean_spectralNorm hPm hP
    have h2 : spectralValue P ≤ 1 := by
      rw [spectralValue_le_one_iff hPm]
      intro n
      rw [Polynomial.coeff_map]
      exact (q.coeff n).2
    have h3 : spectralValue (minpoly ℚ_[p] x) ≤ 1 := h1.trans h2
    exact (spectralValue_le_one_iff hm).1 h3

end ReciprocityTheory.Neutral.Cmp
