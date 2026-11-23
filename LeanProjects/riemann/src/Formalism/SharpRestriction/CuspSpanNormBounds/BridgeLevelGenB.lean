import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal

noncomputable section

namespace Formalism.MainNotions.BridgeLevelGenB

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F]

theorem val_int (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) = v.intValuation a := by
  rw [PI.WAU.val_algebraMap_F, valuation_of_algebraMap]

theorem exists_int_close (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (hx : Valued.v x ≤ 1)
    {g : 𝓞 F} (hg : g ≠ 0) :
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < v.intValuation g := by
  have hγ : v.intValuation g ≠ 0 := intValuation_ne_zero v g hg
  set w : v.adicCompletion F := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F g) with hw
  have hwv : Valued.v w = v.intValuation g := val_int v g
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hwv
    exact hγ hwv.symm
  have hr0 : (Valued.v : Valuation (v.adicCompletion F) _).restrict w ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact hw0
  have hnhds : {y : v.adicCompletion F | Valued.v (y - x) < Valued.v w} ∈ 𝓝 x := by
    rw [Valued.mem_nhds]
    exact ⟨Units.mk0 _ hr0, fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩
  obtain ⟨_, hy, ⟨k, rfl⟩⟩ :=
    mem_closure_iff_nhds.mp ((denseRange_algebraMap (R := 𝓞 F) F v) x) _ hnhds
  simp only [Set.mem_ofPred_eq] at hy
  rw [hwv] at hy
  have hg1 : v.intValuation g ≤ 1 := intValuation_le_one v g
  have hk : v.valuation F k ≤ 1 := by
    rw [← PI.WAU.val_algebraMap_F]
    calc Valued.v (algebraMap F (v.adicCompletion F) k)
        = Valued.v ((algebraMap F (v.adicCompletion F) k - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap F (v.adicCompletion F) k - x)) (Valued.v x) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le (hy.le.trans hg1) hx
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hk (Units.mk0 _ hγ)
  refine ⟨a, ?_⟩
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) k -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < v.intValuation g := by
    rw [← map_sub, PI.WAU.val_algebraMap_F, ← Valuation.map_neg, neg_sub]
    simpa using ha
  calc Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
      = Valued.v ((x - algebraMap F (v.adicCompletion F) k) + (algebraMap F (v.adicCompletion F) k -
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < _ := by
      refine max_lt ?_ h2
      rw [← Valuation.map_neg, neg_sub]; exact hy

theorem dense_mod (g : ℕ) (hg : 1 ≤ g) (y : FiniteAdeleRing (𝓞 F) F) (hy : y ∈ Formalism.UG.intAd F) :
    ∃ s : 𝓞 F, ∃ c ∈ Formalism.UG.intAd F,
      y = algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F s) + (g : FiniteAdeleRing (𝓞 F) F) * c := by
  classical
  set gO : 𝓞 F := (g : 𝓞 F) with hgO
  have hg0 : gO ≠ 0 := by rw [hgO]; exact Nat.cast_ne_zero.2 (by omega)
  have hI : Ideal.span {gO} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg0
  set T := (Ideal.finite_factors hI).toFinset with hT
  have hyv : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (y v) ≤ 1 :=
    fun v => (mem_adicCompletionIntegers (𝓞 F) F v).1 (hy v)
  choose a ha using fun v : HeightOneSpectrum (𝓞 F) => exists_int_close v (y v) (hyv v) hg0
  set k : HeightOneSpectrum (𝓞 F) → ℕ :=
    fun v => (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {gO})).factors with hk
  obtain ⟨s, hs⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal) k
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => a v.1)
  have hval : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s)) ≤ v.intValuation gO := by
    intro v
    by_cases hv : v ∈ T
    · have h1 := hs v hv
      have h2 : v.intValuation (s - a v) ≤ v.intValuation gO := by
        rw [intValuation_if_neg v hg0]
        exact (intValuation_le_pow_iff_mem v _ _).2 h1
      have h3 : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a v)) -
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s)) ≤ v.intValuation gO := by
        rw [← map_sub, ← map_sub, val_int, ← Valuation.map_neg, neg_sub]
        exact h2
      calc Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))
          = Valued.v ((y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a v))) +
              (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a v)) -
                algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))) := by ring_nf
        _ ≤ max _ _ := Valuation.map_add _ _ _
        _ ≤ _ := max_le (ha v).le h3
    · have hgv : gO ∉ v.asIdeal := by
        intro hm
        apply hv
        rw [hT, Set.Finite.mem_toFinset]
        show v.asIdeal ∣ Ideal.span {gO}
        rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
        exact hm
      have h1 : v.intValuation gO = 1 :=
        le_antisymm (intValuation_le_one v gO) (not_lt.1 fun h => hgv ((intValuation_lt_one_iff_mem v gO).1 h))
      rw [h1]
      calc Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))
          ≤ max (Valued.v (y v)) (Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))) :=
            Valuation.map_sub _ _ _
        _ ≤ 1 := max_le (hyv v) (by rw [val_int]; exact intValuation_le_one v s)
  have hgF : algebraMap (𝓞 F) F gO ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)]; exact hg0
  refine ⟨s, algebraMap F _ (algebraMap (𝓞 F) F gO)⁻¹ *
    (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F s)), ?_, ?_⟩
  · intro v
    show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F gO)⁻¹ *
      (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s)) ∈ _
    rw [mem_adicCompletionIntegers, map_mul, map_inv₀, map_inv₀, val_int]
    have hne : v.intValuation gO ≠ 0 := intValuation_ne_zero v gO hg0
    calc (v.intValuation gO)⁻¹ * Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))
        ≤ (v.intValuation gO)⁻¹ * v.intValuation gO := by gcongr; exact hval v
      _ = 1 := inv_mul_cancel₀ hne
  · have e : (g : FiniteAdeleRing (𝓞 F) F) = algebraMap F _ (algebraMap (𝓞 F) F gO) := by
      rw [hgO, map_natCast, map_natCast]
    rw [e, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hgF, map_one, one_mul]
    ring

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem dense_modE (g : ℕ) (hg : 1 ≤ g) (a : E ⊗[F] Af F) (ha : a ∈ IntAf F E) :
    ∃ b ∈ Formalism.UG.intOE E, ∃ c ∈ IntAf F E, a = b ⊗ₜ[F] (1 : Af F) + (g : E ⊗[F] Af F) * c := by
  have gen1 : ∀ b ∈ Formalism.UG.intOE E, b ⊗ₜ[F] (1 : Af F) ∈ IntAf F E := fun b hb =>
    Subring.subset_closure (Or.inl ⟨⟨b, hb⟩, rfl⟩)
  have gen2 : ∀ y ∈ Formalism.UG.intAd F, (1 : E) ⊗ₜ[F] y ∈ IntAf F E := fun y hy =>
    Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  have hgI : (g : E ⊗[F] Af F) ∈ IntAf F E := natCast_mem _ g
  induction ha using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨b, hb⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · exact ⟨b, hb, 0, zero_mem _, by simp⟩
    · obtain ⟨s, c, hc, e⟩ := dense_mod g hg y hy
      have hint : IsIntegral ℤ (algebraMap F E (algebraMap (𝓞 F) F s)) :=
        (RingOfIntegers.isIntegral_coe s).algebraMap
      refine ⟨algebraMap F E (algebraMap (𝓞 F) F s), ⟨⟨_, hint⟩, rfl⟩, (1 : E) ⊗ₜ[F] c, gen2 c hc, ?_⟩
      have e1 : (g : E ⊗[F] Af F) = (1 : E) ⊗ₜ[F] (g : Af F) := by
        rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
      have e2 : algebraMap F E (algebraMap (𝓞 F) F s) ⊗ₜ[F] (1 : Af F) =
          (1 : E) ⊗ₜ[F] algebraMap F (Af F) (algebraMap (𝓞 F) F s) := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := Af F), TensorProduct.smul_tmul]
      show (1 : E) ⊗ₜ[F] y = _
      rw [e1, e2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_add, ← e]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | one => exact ⟨1, one_mem _, 0, zero_mem _, by simp [Algebra.TensorProduct.one_def]⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    obtain ⟨b', hb', c', hc', rfl⟩ := hy
    refine ⟨b + b', add_mem hb hb', c + c', add_mem hc hc', ?_⟩
    rw [TensorProduct.add_tmul]; ring
  | neg x _ hx =>
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    refine ⟨-b, neg_mem hb, -c, neg_mem hc, ?_⟩
    rw [TensorProduct.neg_tmul]; ring
  | mul x y _ _ hx hy =>
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    obtain ⟨b', hb', c', hc', rfl⟩ := hy
    refine ⟨b * b', mul_mem hb hb',
      b ⊗ₜ[F] (1 : Af F) * c' + c * b' ⊗ₜ[F] (1 : Af F) + (g : E ⊗[F] Af F) * c * c', ?_, ?_⟩
    · exact add_mem (add_mem (mul_mem (gen1 b hb) hc') (mul_mem hc (gen1 b' hb'))) (mul_mem (mul_mem hgI hc) hc')
    · rw [show (b * b') ⊗ₜ[F] (1 : Af F) = b ⊗ₜ[F] (1 : Af F) * b' ⊗ₜ[F] (1 : Af F) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
      ring

end Formalism.MainNotions.BridgeLevelGenB

end
