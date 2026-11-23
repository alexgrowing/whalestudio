import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.VanishAwayInt

theorem exists_away {F : Type} [Field F] [NumberField F] (p : Ideal (𝓞 F)) [hp : p.IsPrime] (N : 𝓞 F) (hN : N ≠ 0) :
    ∃ t : 𝓞 F, t ∉ p ∧ ∀ w : HeightOneSpectrum (𝓞 F), w.asIdeal ≠ p →
      ∃ c y : 𝓞 F, y ∉ w.asIdeal ∧ y * t = N * c := by
  classical
  have hI : Ideal.span {N} ≠ ⊥ := by simpa using hN
  have hpu : ¬ IsUnit p := by
    rw [Ideal.isUnit_iff]; exact hp.ne_top
  obtain ⟨b, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hpu hI).exists_eq_pow_mul_and_not_dvd
  have hbp : ¬ b ≤ p := fun h => hnd (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htb, htp⟩ := SetLike.not_le_iff_exists.1 hbp
  refine ⟨t, htp, fun w hw => ?_⟩
  have hpw : ¬ p ^ multiplicity p (Ideal.span {N}) ≤ w.asIdeal := by
    intro h
    rcases Nat.eq_zero_or_pos (multiplicity p (Ideal.span {N})) with h0 | hm
    · rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at h
      exact w.isPrime.ne_top h
    · have hle : p ≤ w.asIdeal := w.isPrime.le_of_pow_le h
      have hpb : p ≠ ⊥ := by
        intro h'
        apply hI
        rw [eq_bot_iff]
        calc Ideal.span {N} = p ^ multiplicity p (Ideal.span {N}) * b := hb
          _ ≤ p ^ multiplicity p (Ideal.span {N}) := Ideal.mul_le_left
          _ ≤ p := Ideal.pow_le_self hm.ne'
          _ = ⊥ := h'
      have hmax : p.IsMaximal := hp.isMaximal hpb
      exact hw (hmax.eq_of_le w.isPrime.ne_top hle).symm
  obtain ⟨y, hy, hyw⟩ := SetLike.not_le_iff_exists.1 hpw
  have hyt : y * t ∈ Ideal.span {N} := by
    rw [hb]; exact Ideal.mul_mem_mul hy htb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyt
  exact ⟨c, y, hyw, by rw [← hc, mul_comm]⟩

theorem intAtA_of_prV_eq_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    (∀ v : HeightOneSpectrum (𝓞 F), IsOver v P → prV (E := E) v z = 0) → IntAtA (F := F) P z := by
  intro F E _ _ _ _ _ P z hz
  obtain ⟨m, hm, hmz⟩ := GlobalTheory.St.G.IntAd.exists_nat_denom (F := F) (E := E) z
  haveI : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsPrime := Ideal.comap_isPrime _ _
  have hm0 : (m : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  obtain ⟨t, htp, ht⟩ := exists_away (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))) (m : 𝓞 F) hm0
  refine ⟨algebraMap (𝓞 F) (𝓞 E) t, htp, ?_⟩
  have key : iA F E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t)) =
      algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F t) := rfl
  apply GlobalTheory.St.G.IntAd.mem_of_local
  intro w
  by_cases hw : w.asIdeal = P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  · rw [map_mul, hz w hw, mul_zero]; exact zero_mem _
  · obtain ⟨c, y, hyw, hyc⟩ := ht w hw
    have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have hy0 : algebraMap (𝓞 F) F y ≠ 0 := by
      intro h0
      apply hyw
      rw [(FaithfulSMul.algebraMap_eq_zero_iff (𝓞 F) F).1 h0]
      exact zero_mem _
    set q : F := algebraMap (𝓞 F) F t / (m : F) with hqdef
    have e : iA F E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t)) * z =
        algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) q * ((m : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * z) := by
      rw [key, ← mul_assoc, ← map_natCast (algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) m, ← map_mul, hqdef,
        div_mul_cancel₀ _ hmF]
    rw [e, map_mul]
    refine mul_mem ?_ (Formalism.UG.P.afsplit_prV_int w _ hmz)
    have hc : prV (E := E) w (algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) q) =
        algebraMap F (E ⊗[F] w.adicCompletion F) q :=
      (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F w)).commutes q
    rw [hc, Algebra.TensorProduct.algebraMap_apply']
    have hq' : q = algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F y := by
      rw [hqdef, div_eq_div_iff hmF hy0]
      have := congrArg (algebraMap (𝓞 F) F) hyc
      rw [map_mul, map_mul, map_natCast] at this
      linear_combination this
    have hq : algebraMap F (w.adicCompletion F) q ∈ w.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w q]
      rw [hq', map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      have hy1 : w.intValuation y = 1 :=
        le_antisymm (w.intValuation_le_one y) (not_lt.1 fun h => hyw ((w.intValuation_lt_one_iff_mem y).1 h))
      rw [hy1, div_one]
      exact w.intValuation_le_one c
    exact Subring.subset_closure (Or.inr ⟨⟨_, hq⟩, rfl⟩)

end GlobalTheory.VanishAwayInt
