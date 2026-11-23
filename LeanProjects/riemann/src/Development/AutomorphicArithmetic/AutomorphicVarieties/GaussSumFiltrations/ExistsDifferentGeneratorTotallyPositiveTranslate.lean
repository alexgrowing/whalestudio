import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTotallyPositiveApproxAtFinitePlaces
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.DelGen

variable {F : Type} [Field F] [NumberField F]

theorem exists_pos_val (T : Finset (HeightOneSpectrum (𝓞 F))) (γ : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ))
    (hγ : ∀ w ∈ T, γ w ≠ 0) :
    ∃ a : F, (∀ w ∈ T, w.valuation F a = γ w) ∧ ∀ φ : F →+* ℝ, 0 < φ a := by
  choose t ht using fun w : HeightOneSpectrum (𝓞 F) => w.valuation_surjective F (γ w)
  set M : ℕ := T.sup (fun w => (WithZero.log (γ w)).natAbs) + 1 with hM
  obtain ⟨a, ha, hpos⟩ := GlobalTheory.FinPlaceApproxPos.approxpos_target F T t M
  refine ⟨a, fun w hw => ?_, hpos⟩
  have hle : (WithZero.log (γ w)).natAbs ≤ T.sup (fun w => (WithZero.log (γ w)).natAbs) :=
    Finset.le_sup (f := fun w => (WithZero.log (γ w)).natAbs) hw
  have hlt : WithZero.exp (-(M : ℤ)) < γ w := by
    conv_rhs => rw [← WithZero.exp_log (hγ w hw)]
    rw [WithZero.exp_lt_exp]
    omega
  rw [← ht w]
  exact Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt (ha w hw) (by rw [ht w]; exact hlt))

theorem finite_over (p : ℕ) (hp : p ≠ 0) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ w, w ∈ T ↔ ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine ⟨(Ideal.finite_factors h0).toFinset, fun w => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]

end GlobalTheory.HilbertThetaSeries.DelGen

open GlobalTheory.HilbertThetaSeries.DelGen in

theorem GlobalTheory.HilbertThetaSeries.del_exists_and_move : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → (∃ δ : F, IsDel p δ) ∧ ∀ δ : F, IsDel p δ → ∀ y : (Af F)ˣ, ∃ ξ : Fˣ, TP (ξ : F) ∧ AtP p δ (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y) := by
  intro F _ _ _ p hp
  obtain ⟨T, hT⟩ := finite_over (F := F) p hp.ne_zero
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha, -⟩ := exists_pos_val T (fun w => WithZero.exp (-(ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)))
      (fun w _ => WithZero.exp_ne_zero)
    exact ⟨a, fun w hw => ha w ((hT w).2 hw)⟩
  · intro δ hδ y
    have hne : ∀ w ∈ T, Valued.v (pLoc F w (y : Af F)) * w.valuation F δ ≠ 0 := by
      intro w hw
      refine mul_ne_zero ?_ ?_
      · rw [Ne, map_eq_zero]
        exact ((y.map (pLoc F w).toMonoidHom).ne_zero)
      · rw [hδ w ((hT w).1 hw)]
        exact WithZero.exp_ne_zero
    obtain ⟨a, ha, hpos⟩ := exists_pos_val T (fun w => (Valued.v (pLoc F w (y : Af F)) * w.valuation F δ)⁻¹)
      (fun w hw => inv_ne_zero (hne w hw))
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    have ha0 : a ≠ 0 := by
      intro h
      have h1 := hpos (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
      rw [h, map_zero] at h1
      exact lt_irrefl _ h1
    refine ⟨Units.mk0 a ha0, fun u => ?_, fun w hw => ?_⟩
    · show 0 < (u.embedding a).re
      rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal u), Complex.ofReal_re]
      exact hpos _
    · have hw' := (hT w).2 hw
      rw [Units.val_mul, Units.coe_map, map_mul]
      show Valued.v ((a : w.adicCompletion F) * pLoc F w (y : Af F)) * w.valuation F δ = 1
      rw [map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ha w hw', mul_assoc, inv_mul_cancel₀ (hne w hw')]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_different_generator_totallyPositive_translate : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → (∃ δ : F, IsDel p δ) ∧ ∀ δ : F, IsDel p δ → ∀ y : (Af F)ˣ, ∃ ξ : Fˣ, TP (ξ : F) ∧ AtP p δ (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y) := by
  first | exact @GlobalTheory.HilbertThetaSeries.del_exists_and_move | exact GlobalTheory.HilbertThetaSeries.del_exists_and_move | (intros; apply GlobalTheory.HilbertThetaSeries.del_exists_and_move <;> assumption)
