import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.MemFixSub
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic

noncomputable section
open NumberField IsDedekindDomain HeightOneSpectrum WithZero IsLocalRing Topology Filter

namespace PI.SqPairLocal.Mdl

open PI.SqPairLocal Formalism.BasicNotions.Examples₂

theorem wz_le_of {a b : ℤᵐ⁰} (hb : b ≤ 1)
    (h : ∀ n : ℕ, b ≤ exp (-(n : ℤ)) → a ≤ exp (-(n : ℤ))) : a ≤ b := by
  rcases eq_or_ne b 0 with rfl | h0
  · have : a = 0 := by
      by_contra ha0
      obtain ⟨N, hN⟩ := wz_exists_nat_lt a ha0
      exact absurd (h N (by simp)) (not_le.2 hN)
    simp [this]
  · have hl : log b ≤ 0 := by
      rw [← exp_le_exp, exp_log h0, exp_zero]; exact hb
    have e : b = exp (-(((-(log b)).toNat : ℕ) : ℤ)) := by
      rw [Int.toNat_of_nonneg (by omega), neg_neg, exp_log h0]
    have := h ((-(log b)).toNat) (le_of_eq e)
    rwa [← e] at this

theorem wz_eq_of {a b : ℤᵐ⁰} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ exp (-(n : ℤ)) ↔ b ≤ exp (-(n : ℤ))) : a = b :=
  le_antisymm (wz_le_of hb fun n hn => (h n).2 hn) (wz_le_of ha fun n hn => (h n).1 hn)

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem cj_coe (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := rfl

theorem cj_cj (x : 𝓞 E) : cj E (cj E x) = x := by
  ext; rw [cj_coe, cj_coe, star_star]

theorem mem_pow_cj {Q : Ideal (𝓞 E)} (hQ : Q.comap (cj E) = Q) (n : ℕ) (r : 𝓞 E) :
    cj E r ∈ Q ^ n ↔ r ∈ Q ^ n := by
  have h1 : ∀ r, r ∈ Q ^ n → cj E r ∈ Q ^ n := by
    intro r hr
    have : Q ^ n ≤ (Q ^ n).comap (cj E) := by
      calc Q ^ n = (Q.comap (cj E)) ^ n := by rw [hQ]
        _ ≤ _ := Ideal.le_comap_pow _ n
    exact this hr
  exact ⟨fun h => by simpa [cj_cj] using h1 _ h, h1 r⟩

section Val

variable (v : HeightOneSpectrum (𝓞 E)) (hv : v.asIdeal.comap (cj E) = v.asIdeal)
include hv

theorem intVal_cj (r : 𝓞 E) : v.intValuation (cj E r) = v.intValuation r :=
  wz_eq_of (v.intValuation_le_one _) (v.intValuation_le_one _) fun n => by
    rw [intValuation_le_pow_iff_mem, intValuation_le_pow_iff_mem, mem_pow_cj hv]

theorem val_star (a : E) : v.valuation E (star a) = v.valuation E a := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
  have hs : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) = algebraMap (𝓞 E) E (cj E r) := fun r => rfl
  rw [star_div₀, hs, hs, map_div₀, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, intVal_cj v hv, intVal_cj v hv]

omit hv in

def tau : WithVal (v.valuation E) →+* WithVal (v.valuation E) :=
  WithVal.map (v.valuation E) (v.valuation E) (starRingEnd E)

omit hv in
theorem tau_apply (x : WithVal (v.valuation E)) :
    tau v x = WithVal.toVal (v.valuation E) (star (WithVal.ofVal x)) := rfl

omit hv in
theorem tau_tau (x : WithVal (v.valuation E)) : tau v (tau v x) = x := by
  rw [tau_apply, tau_apply, WithVal.ofVal_toVal, star_star, WithVal.toVal_ofVal]

theorem v_tau (x : WithVal (v.valuation E)) : Valued.v (tau v x) = Valued.v x := by
  rw [tau_apply, WithVal.valued_toVal, val_star v hv, WithVal.apply_ofVal]

theorem tau_cont : Continuous (tau v) := by
  apply continuous_of_continuousAt_zero (tau v)
  rw [ContinuousAt, map_zero]
  refine ((Valued.hasBasis_nhds_zero _ _).tendsto_iff (Valued.hasBasis_nhds_zero _ _)).2
    fun γ _ => ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rwa [v_tau v hv]

def sigC : (v.valuation E).Completion →+* (v.valuation E).Completion :=
  UniformSpace.Completion.mapRingHom (tau v) (tau_cont v hv)

theorem sigC_coe (x : WithVal (v.valuation E)) :
    sigC v hv (x : (v.valuation E).Completion) = (tau v x : (v.valuation E).Completion) :=
  UniformSpace.Completion.mapRingHom_coe _ x

theorem sigC_cont : Continuous (sigC v hv) := by
  rw [sigC, UniformSpace.Completion.coe_mapRingHom]
  exact UniformSpace.Completion.continuous_map

theorem sigC_sigC (y : (v.valuation E).Completion) : sigC v hv (sigC v hv y) = y := by
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq ((sigC_cont v hv).comp (sigC_cont v hv)) continuous_id
  | ih a => rw [sigC_coe, sigC_coe, tau_tau]

def sigK : v.adicCompletion E →+* v.adicCompletion E :=
  (adicCompletion.equiv E v).symm.toRingHom.comp ((sigC v hv).comp (adicCompletion.equiv E v).toRingHom)

theorem sigK_apply (x : v.adicCompletion E) :
    sigK v hv x = adicCompletion.ofCompletion (sigC v hv x.toCompletion) := rfl

theorem sigK_sigK (x : v.adicCompletion E) : sigK v hv (sigK v hv x) = x := by
  rw [sigK_apply, sigK_apply, adicCompletion.toCompletion_ofCompletion, sigC_sigC]

theorem sigK_cont : Continuous (sigK v hv) := by
  have : (sigK v hv : v.adicCompletion E → v.adicCompletion E) =
      adicCompletion.ofCompletion ∘ (sigC v hv) ∘ adicCompletion.toCompletion := rfl
  rw [this]
  exact (adicCompletion.continuous_ofCompletion E v).comp ((sigC_cont v hv).comp
    (adicCompletion.continuous_toCompletion E v))

theorem sigK_alg (a : E) :
    sigK v hv (algebraMap E (v.adicCompletion E) a) = algebraMap E (v.adicCompletion E) (star a) := by
  show adicCompletion.ofCompletion (sigC v hv _) = _
  erw [sigC_coe]
  rfl

end Val

end PI.SqPairLocal.Mdl
