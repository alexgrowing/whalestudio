import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

open MeasureTheory

namespace GlobalTheory.CompanionTheory.PeriodicInt

variable {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)}

theorem valued_algebraMap (x : E) :
    Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem valued_int_le_one (a : 𝓞 E) :
    Valued.v (algebraMap E (v.adicCompletion E) (a : E)) ≤ 1 := by
  rw [valued_algebraMap]
  exact v.valuation_le_one a

theorem valued_le_one_of_mem_valBall {m : ℕ} {x : v.adicCompletion E}
    (h : x ∈ valBall (v.adicCompletion E) (m : ℤ)) : Valued.v x ≤ 1 := by
  refine (mem_valBall_iff_valued.1 h).trans ?_
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem exists_int_close (m : ℕ) {y : v.adicCompletion E} (hy : Valued.v y ≤ 1) :
    ∃ a : 𝓞 E, y - algebraMap E (v.adicCompletion E) (a : E) ∈
      valBall (v.adicCompletion E) (m : ℤ) := by
  have hopen : IsOpen {z : v.adicCompletion E | y - z ∈ valBall (v.adicCompletion E) (m : ℤ)} :=
    (isOpen_valBall (m : ℤ)).preimage (continuous_const.sub continuous_id)
  obtain ⟨x, hx⟩ := (v.denseRange_algebraMap E).exists_mem_open hopen
    ⟨y, by simp [zero_mem]⟩
  have hx' : y - algebraMap E (v.adicCompletion E) x ∈ valBall (v.adicCompletion E) (m : ℤ) := hx
  have h1 : Valued.v (algebraMap E (v.adicCompletion E) x) ≤ 1 := by
    have e : algebraMap E (v.adicCompletion E) x =
        y - (y - algebraMap E (v.adicCompletion E) x) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le hy (valued_le_one_of_mem_valBall hx'))
  rw [valued_algebraMap] at h1
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer h1
    (Units.mk0 _ (WithZero.exp_ne_zero (a := -(m : ℤ))))
  rw [Units.val_mk0] at ha
  refine ⟨a, ?_⟩
  have e : y - algebraMap E (v.adicCompletion E) (a : E) =
      (y - algebraMap E (v.adicCompletion E) x) +
        algebraMap E (v.adicCompletion E) (x - (a : E)) := by
    rw [map_sub]; ring
  rw [e]
  refine add_mem hx' (mem_valBall_iff_valued.2 ?_)
  rw [valued_algebraMap, Valuation.map_sub_swap]
  exact ha.le

theorem sub_mem_pow_of_close {m : ℕ} {a b : 𝓞 E}
    (h : algebraMap E (v.adicCompletion E) (a : E) - algebraMap E (v.adicCompletion E) (b : E) ∈
      valBall (v.adicCompletion E) (m : ℤ)) : a - b ∈ v.asIdeal ^ m := by
  have h1 := mem_valBall_iff_valued.1 h
  rw [← map_sub, valued_algebraMap] at h1
  rw [← v.intValuation_le_pow_iff_mem, ← v.valuation_of_algebraMap (K := E)]
  simpa using h1

theorem close_of_sub_mem_pow {m : ℕ} {a b : 𝓞 E} (h : a - b ∈ v.asIdeal ^ m) :
    algebraMap E (v.adicCompletion E) (a : E) - algebraMap E (v.adicCompletion E) (b : E) ∈
      valBall (v.adicCompletion E) (m : ℤ) := by
  rw [mem_valBall_iff_valued, ← map_sub, valued_algebraMap]
  exact valuation_sub_le h

theorem integral_eq_finsum : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (g : v.adicCompletion E → ℂ), (∀ y, 1 < Valued.v y → g y = 0) → (∀ y h : v.adicCompletion E, Valued.v h ≤ WithZero.exp (-(m : ℤ)) → g (y + h) = g y) → ∫ y, g y ∂haarIntegers (v.adicCompletion E) = (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℂ))⁻¹ * ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, g (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) := by
  intro E _ _ v m g h0 hp
  classical
  have : Finite (𝓞 E ⧸ v.asIdeal ^ m) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ v.ne_bot)
  have := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal ^ m)
  let a : (𝓞 E ⧸ v.asIdeal ^ m) → v.adicCompletion E := fun r =>
    algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)
  let S : (𝓞 E ⧸ v.asIdeal ^ m) → Set (v.adicCompletion E) := fun r =>
    (fun y => y + (-a r)) ⁻¹' (valBall (v.adicCompletion E) (m : ℤ) : Set (v.adicCompletion E))
  have memS : ∀ r y, y ∈ S r ↔ y - a r ∈ valBall (v.adicCompletion E) (m : ℤ) := fun r y => by
    simp only [S, Set.mem_preimage, SetLike.mem_coe, sub_eq_add_neg]
  have hSm : ∀ r, MeasurableSet (S r) := fun r =>
    ((isOpen_valBall (m : ℤ)).preimage (continuous_id.add continuous_const)).measurableSet
  have hB : (haarIntegers (v.adicCompletion E)).real
      (valBall (v.adicCompletion E) (m : ℤ) : Set (v.adicCompletion E)) =
      (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℝ))⁻¹ := by
    rw [measureReal_def, haarIntegers_valBall, residueCard_adicCompletion, ENNReal.coe_toReal,
      NNReal.coe_zpow, NNReal.coe_natCast, zpow_neg, zpow_natCast]
    push_cast
    rfl
  have hSμ : ∀ r, (haarIntegers (v.adicCompletion E)).real (S r) =
      (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℝ))⁻¹ := fun r => by
    rw [← hB, measureReal_def, measureReal_def]
    exact congrArg ENNReal.toReal (measure_preimage_add_right _ _ _)
  have hfin : ∀ r, haarIntegers (v.adicCompletion E) (S r) ≠ ⊤ := fun r => by
    have : haarIntegers (v.adicCompletion E) (S r) =
        haarIntegers (v.adicCompletion E)
          (valBall (v.adicCompletion E) (m : ℤ) : Set (v.adicCompletion E)) :=
      measure_preimage_add_right _ _ _
    rw [this, haarIntegers_valBall]
    exact ENNReal.coe_ne_top
  have hdecomp : ∀ y, g y = ∑ r, (S r).indicator (fun _ => g (a r)) y := by
    intro y
    by_cases hy : Valued.v y ≤ 1
    · obtain ⟨b, hb⟩ := exists_int_close (v := v) m hy
      set r : 𝓞 E ⧸ v.asIdeal ^ m := Ideal.Quotient.mk _ b with hr
      have hclose : a r - algebraMap E (v.adicCompletion E) (b : E) ∈
          valBall (v.adicCompletion E) (m : ℤ) :=
        close_of_sub_mem_pow (Ideal.Quotient.eq.1 (by rw [Ideal.Quotient.mk_out]))
      have hyr : y ∈ S r := by
        rw [memS]
        have e : y - a r = (y - algebraMap E (v.adicCompletion E) (b : E)) -
            (a r - algebraMap E (v.adicCompletion E) (b : E)) := by ring
        rw [e]
        exact sub_mem hb hclose
      rw [Finset.sum_eq_single r, Set.indicator_of_mem hyr]
      · have := hp (a r) (y - a r) (mem_valBall_iff_valued.1 ((memS r y).1 hyr))
        rwa [add_sub_cancel] at this
      · intro r' _ hne
        refine Set.indicator_of_notMem (fun hyr' => hne ?_) _
        have h1 := sub_mem ((memS r y).1 hyr) ((memS r' y).1 hyr')
        have e : y - a r - (y - a r') = a r' - a r := by ring
        rw [e] at h1
        have h2 := sub_mem_pow_of_close h1
        have h3 := Ideal.Quotient.eq.2 h2
        simpa [Ideal.Quotient.mk_out] using h3
      · simp
    · rw [h0 y (not_le.1 hy)]
      refine (Finset.sum_eq_zero fun r _ => Set.indicator_of_notMem (fun hyr => hy ?_) _).symm
      have e : y = (y - a r) + a r := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans
        (max_le (valued_le_one_of_mem_valBall ((memS r y).1 hyr)) (valued_int_le_one _))
  have hint : ∀ r, Integrable ((S r).indicator (fun _ => g (a r)))
      (haarIntegers (v.adicCompletion E)) := fun r =>
    (integrable_indicator_iff (hSm r)).2 (integrableOn_const (hfin r))
  calc ∫ y, g y ∂haarIntegers (v.adicCompletion E)
      = ∫ y, ∑ r, (S r).indicator (fun _ => g (a r)) y ∂haarIntegers (v.adicCompletion E) :=
        integral_congr_ae (Filter.Eventually.of_forall hdecomp)
    _ = ∑ r, ∫ y, (S r).indicator (fun _ => g (a r)) y ∂haarIntegers (v.adicCompletion E) :=
        integral_finsetSum _ fun r _ => hint r
    _ = _ := by
        rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [integral_indicator_const _ (hSm r), hSμ r, Complex.real_smul]
        push_cast
        rfl

end GlobalTheory.CompanionTheory.PeriodicInt
