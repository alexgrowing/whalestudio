import Mathlib
import Formalism.PeriodIntegrals.AdCpctDen

namespace PI.AdCpctDenWork

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F]

def intAd (F : Type) [Field F] [NumberField F] : Set (FiniteAdeleRing (𝓞 F) F) :=
  {a | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}

theorem mem_intAd (a : FiniteAdeleRing (𝓞 F) F) :
    a ∈ intAd F ↔ ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F :=
  Iff.rfl

theorem isOpen_intAd : IsOpen (intAd F) :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

theorem natCast_mul_apply (n : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((n : FiniteAdeleRing (𝓞 F) F) * a) v = (n : v.adicCompletion F) * a v :=
  rfl

theorem natCast_mem_int (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    (n : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
  natCast_mem _ n

theorem exists_nat_local (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion F) * x ∈ v.adicCompletionIntegers F := by
  obtain ⟨b, hb, hbx⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hb0
  · have h1 : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : v.adicCompletion F)
        = algebraMap (𝓞 F) (v.adicCompletion F) c * algebraMap (𝓞 F) (v.adicCompletion F) b := by
      rw [← map_mul, hc, map_natCast]
    rw [h1, mul_assoc, mul_comm (algebraMap _ _ b) x]
    exact mul_mem (coe_mem_adicCompletionIntegers v c) hbx

theorem exists_nat_adele (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ n : ℕ, 0 < n ∧ (n : FiniteAdeleRing (𝓞 F) F) * a ∈ intAd F := by
  classical
  choose m hm0 hm using fun v => exists_nat_local (F := F) v (a v)
  have hS : {v : HeightOneSpectrum (𝓞 F) | ¬ a v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp a.2
  refine ⟨∏ v ∈ hS.toFinset, m v, Finset.prod_pos (fun v _ => hm0 v), fun w => ?_⟩
  rw [natCast_mul_apply]
  by_cases hw : w ∈ hS.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hw
    rw [hk, Nat.cast_mul, mul_comm ((m w : ℕ) : w.adicCompletion F), mul_assoc]
    exact mul_mem (natCast_mem_int w k) (hm w)
  · have hw' : a w ∈ w.adicCompletionIntegers F := by
      by_contra h
      exact hw (hS.mem_toFinset.mpr h)
    exact mul_mem (natCast_mem_int w _) hw'

end PI.AdCpctDenWork

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum PI.AdCpctDenWork in

theorem PI.adCpctDen : PI.AdCpctDen := by
  intro F _ _ C hC
  classical
  choose m hm0 hm using fun a : FiniteAdeleRing (𝓞 F) F => exists_nat_adele a
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun a => (fun x => (m a : FiniteAdeleRing (𝓞 F) F) * x) ⁻¹' intAd F)
    (fun a => isOpen_intAd.preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun f hf => ?_⟩
  obtain ⟨a, ha, hfa⟩ := Set.mem_iUnion₂.mp (ht hf)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hfa' : (m a : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈
      intAd F := hfa
  have hA : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((∏ a ∈ t, m a : ℕ) : F) * f) =
      (k : FiniteAdeleRing (𝓞 F) F) *
        ((m a : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) f) := by
    rw [map_mul, map_natCast, hk, Nat.cast_mul]
    ring
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (((∏ a ∈ t, m a : ℕ) : F) * f) ≤ 1 := by
    intro v
    rw [← valuedAdicCompletion_eq_valuation', ← mem_adicCompletionIntegers]
    have h2 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (((∏ a ∈ t, m a : ℕ) : F) * f)) v ∈
        v.adicCompletionIntegers F := by
      rw [hA, natCast_mul_apply]
      exact mul_mem (natCast_mem_int v k) ((mem_intAd _).mp hfa' v)
    rw [FiniteAdeleRing.algebraMap_apply] at h2
    exact h2
  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) _ hint
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r
