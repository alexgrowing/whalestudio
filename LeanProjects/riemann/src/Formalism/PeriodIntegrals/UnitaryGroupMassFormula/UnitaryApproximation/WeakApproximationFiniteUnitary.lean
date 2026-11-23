import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.WeakApproxF

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace PI.UnitaryApproxFinWork

variable {F : Type} [Field F] [NumberField F]

theorem wa_isOpen_lt_one (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    IsOpen {y : v.adicCompletion F | Valued.v (y - x) < 1} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [Valued.mem_nhds]
  refine ⟨1, fun z hz => ?_⟩
  have hz' : Valued.v (z - y) < 1 := by
    first
      | simpa using hz
      | exact_mod_cast hz
      | (simp only [Set.mem_setOf_eq, Units.val_one] at hz
         first
           | exact (Valuation.restrict_lt_iff _ _ _).mp hz
           | exact (Valuation.restrict_lt_one_iff _ _).mp hz
           | exact_mod_cast hz)
  simp only [Set.mem_setOf_eq] at hy ⊢
  have hzx : z - x = (z - y) + (y - x) := by abel
  rw [hzx]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hz' hy)

theorem wa_valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k := by
  first
    | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
    | simpa using IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
    | rfl

theorem wa_exists_close (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ b : F, Valued.v (x - algebraMap F (v.adicCompletion F) b) < 1 := by
  have hd : DenseRange (algebraMap F (v.adicCompletion F)) := by
    first
      | exact denseRange_algebraMap F v
      | exact UniformSpace.Completion.denseRange_coe
      | exact (UniformSpace.Completion.denseRange_coe).comp (WithVal.equiv (v.valuation F)).symm.surjective.denseRange
          (UniformSpace.Completion.continuous_coe _)
      | exact IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap_adicCompletion v
  obtain ⟨b, hb⟩ := hd.exists_mem_open (wa_isOpen_lt_one v x) ⟨x, by simp⟩
  refine ⟨b, ?_⟩
  rw [Valuation.map_sub_swap]
  exact hb

theorem wa_exists_int_approx (T : Finset (HeightOneSpectrum (𝓞 F)))
    (b : HeightOneSpectrum (𝓞 F) → F) :
    ∃ a : F, ∀ v ∈ T, v.valuation F (a - b v) ≤ 1 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) (T.image b)
  have hd0 : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hdF : algebraMap (𝓞 F) F (d : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  have hint : ∀ v ∈ T, ∃ n : 𝓞 F, algebraMap (𝓞 F) F n = algebraMap (𝓞 F) F (d : 𝓞 F) * b v := by
    intro v hv
    obtain ⟨n, hn⟩ := hd (b v) (Finset.mem_image_of_mem b hv)
    exact ⟨n, by rw [hn, Algebra.smul_def]⟩
  choose! n hn using hint
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), v.intValuation (d : 𝓞 F) ≠ 0 := by
    intro v
    first
      | exact v.intValuation_ne_zero _ hd0
      | exact (v.intValuation).ne_zero_iff.mpr hd0
      | (intro h0
         have h1 := v.valuation_of_algebraMap (K := F) (d : 𝓞 F)
         rw [h0] at h1
         exact hdF ((Valuation.zero_iff _).mp h1))
  have hexp : ∀ v : HeightOneSpectrum (𝓞 F), ∃ e : ℕ,
      WithZero.exp (-(e : ℤ)) ≤ v.intValuation (d : 𝓞 F) := by
    intro v
    obtain ⟨k, hk⟩ : ∃ k : ℤ, v.intValuation (d : 𝓞 F) = WithZero.exp k := by
      first
        | exact ⟨_, (WithZero.exp_log (hne v)).symm⟩
        | (obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp (hne v)
           exact ⟨Multiplicative.toAdd a, by rw [← ha]; rfl⟩)
    refine ⟨k.natAbs, ?_⟩
    rw [hk, WithZero.exp_le_exp]
    first
      | omega
      | (rw [Int.natCast_natAbs]; exact neg_abs_le k)
  choose e he using hexp
  obtain ⟨m, hm⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal) e
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => n v.1)
  refine ⟨algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F (d : 𝓞 F), fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem _ (e v)).mpr (hm v hv)
  have hkey : algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F (d : 𝓞 F) - b v =
      algebraMap (𝓞 F) F (m - n v) / algebraMap (𝓞 F) F (d : 𝓞 F) := by
    rw [eq_div_iff hdF, sub_mul, div_mul_cancel₀ _ hdF, map_sub, hn v hv]
    ring
  rw [hkey, map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
  have hlt : (0 : WithZero (Multiplicative ℤ)) < v.intValuation (d : 𝓞 F) := zero_lt_iff.mpr (hne v)
  first
    | exact (div_le_one₀ hlt).mpr (h1.trans (he v))
    | exact div_le_one_of_le₀ (h1.trans (he v)) hlt.le

theorem weak_approximation_finite_unitary : WeakApproxF := by
  intro F _ _ T c D hD
  have hDF : ((D : 𝓞 F) : F) ≠ 0 := by
    first
      | exact_mod_cast hD
      | exact (RingOfIntegers.coe_ne_zero_iff).mpr hD
      | (intro h; exact hD (Subtype.ext h))
  choose b hb using fun v : HeightOneSpectrum (𝓞 F) =>
    wa_exists_close v (c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹)
  obtain ⟨a', ha'⟩ := wa_exists_int_approx T b
  refine ⟨(D : F) * a', fun v hv => ?_⟩
  have hdv0 : algebraMap F (v.adicCompletion F) (D : F) ≠ 0 := (map_ne_zero _).mpr hDF
  refine ⟨c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹ - algebraMap F (v.adicCompletion F) a', ?_, ?_⟩
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    have e1 : c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹ - algebraMap F (v.adicCompletion F) a' =
        (c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹ - algebraMap F (v.adicCompletion F) (b v)) +
          algebraMap F (v.adicCompletion F) (b v - a') := by
      rw [map_sub]
      ring
    rw [e1]
    refine le_trans (Valuation.map_add _ _ _) (max_le (hb v).le ?_)
    rw [wa_valued_algebraMap, Valuation.map_sub_swap]
    exact ha' v hv
  · rw [map_mul, mul_sub, mul_comm (algebraMap F (v.adicCompletion F) (D : F)) (c v * _), mul_assoc,
      inv_mul_cancel₀ hdv0, mul_one]

end PI.UnitaryApproxFinWork

end
