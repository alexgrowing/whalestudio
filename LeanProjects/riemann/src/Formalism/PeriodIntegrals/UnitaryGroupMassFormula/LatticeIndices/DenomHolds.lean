import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllOfParts

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting Polynomial
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem fixed_ex (a : X.B.I.E) (ha : star a = a) : ∃ f : X.B.I.F, algebraMap X.B.I.F X.B.I.E f = a := by
  obtain ⟨f, hf⟩ := (X.B.I.cm.fixed a).1 ha
  exact ⟨f, hf⟩

theorem val_le (f : X.B.I.F) (hf : iota2 X p θ (algebraMap X.B.I.F X.B.I.E f) ∈ OpX X p) :
    p.1.valuation X.B.I.F f ≤ 1 := by
  rw [secondEmbedding_algebraMap, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hf
  rwa [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem denom_holds (hθ : IsSplitEquiv X p θ) : DenomP X p θ := by
  classical
  have key : ∀ f : X.B.I.F, p.1.valuation X.B.I.F f ≤ 1 →
      ∃ s : 𝓞 X.B.I.F, s ∉ p.1.asIdeal ∧ ∃ t : 𝓞 X.B.I.F, (t : X.B.I.F) = (s : X.B.I.F) * f := by
    intro f hf
    have hS := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 X.B.I.F) f
    have hex : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F), ∃ n : ℕ, w.valuation X.B.I.F f ≤ WithZero.exp (n : ℤ) := by
      intro w
      by_cases h0 : w.valuation X.B.I.F f = 0
      · exact ⟨0, by rw [h0]; exact zero_le'⟩
      · refine ⟨(WithZero.log (w.valuation X.B.I.F f)).toNat, ?_⟩
        conv_lhs => rw [← WithZero.exp_log h0]
        exact WithZero.exp_le_exp.2 (Int.self_le_toNat _)
    choose N hN using hex
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert p.1 hS.toFinset)
      (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F) => w.asIdeal)
      (fun w => if w = p.1 then 1 else N w) (fun w _ => w.prime)
      (fun w _ w' _ hne h => hne (IsDedekindDomain.HeightOneSpectrum.ext h))
      (fun w => if w.1 = p.1 then 1 else 0)
    have hyp : y ∉ p.1.asIdeal := by
      intro hmem
      have h1 := hy p.1 (Finset.mem_insert_self _ _)
      simp only [if_true, pow_one] at h1
      have h2 : (1 : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
        have h3 : y - (y - 1) ∈ p.1.asIdeal := p.1.asIdeal.sub_mem hmem h1
        simpa using h3
      exact p.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
    have hval : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F), w.valuation X.B.I.F ((y : X.B.I.F) * f) ≤ 1 := by
      intro w
      rw [Valuation.map_mul]
      by_cases hw : w ∈ hS.toFinset
      · have hwp : w ≠ p.1 := by
          intro h
          rw [Set.Finite.mem_toFinset, h] at hw
          exact absurd hf (not_le.2 hw)
        have h1 := hy w (Finset.mem_insert_of_mem hw)
        simp only [hwp, if_false, sub_zero] at h1
        have h2 : w.valuation X.B.I.F (y : X.B.I.F) ≤ WithZero.exp (-(N w : ℤ)) := by
          rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
          exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem w y (N w)).2 h1
        calc w.valuation X.B.I.F (y : X.B.I.F) * w.valuation X.B.I.F f
            ≤ WithZero.exp (-(N w : ℤ)) * WithZero.exp (N w : ℤ) := mul_le_mul' h2 (hN w)
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      · have hfw : w.valuation X.B.I.F f ≤ 1 := by
          rw [Set.Finite.mem_toFinset] at hw
          exact not_lt.1 hw
        exact mul_le_one' (IsDedekindDomain.HeightOneSpectrum.valuation_le_one w y) hfw
    obtain ⟨t, ht⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one X.B.I.F ((y : X.B.I.F) * f) hval
    exact ⟨y, hyp, t, ht⟩
  intro e h1 h2
  obtain ⟨tf, htf⟩ := fixed_ex X (e + star e) (by rw [star_add, star_star, add_comm])
  obtain ⟨nf, hnf⟩ := fixed_ex X (e * star e) (by rw [star_mul, star_star])
  have hi : ∀ x : X.B.I.E, iota2 X p θ (star x) = iota1 X p θ x := fun x => by
    rw [secondEmbedding_eq_star X p θ hθ, star_star]
  have hvt : p.1.valuation X.B.I.F tf ≤ 1 :=
    val_le X p θ tf (by rw [htf, map_add, hi]; exact add_mem h2 h1)
  have hvn : p.1.valuation X.B.I.F nf ≤ 1 :=
    val_le X p θ nf (by rw [hnf, map_mul, hi]; exact mul_mem h2 h1)
  obtain ⟨s1, hs1, t1, ht1⟩ := key tf hvt
  obtain ⟨s2, hs2, t2, ht2⟩ := key nf hvn
  refine ⟨s1 * s2, fun h => (p.1.isPrime.mem_or_mem h).elim hs1 hs2, ?_⟩
  have f1 : algebraMap X.B.I.F X.B.I.E (t1 : X.B.I.F) = algebraMap X.B.I.F X.B.I.E (s1 : X.B.I.F) * (e + star e) := by
    rw [ht1, map_mul, htf]
  have f2 : algebraMap X.B.I.F X.B.I.E (t2 : X.B.I.F) = algebraMap X.B.I.F X.B.I.E (s2 : X.B.I.F) * (e * star e) := by
    rw [ht2, map_mul, hnf]
  have hrel : (algebraMap X.B.I.F X.B.I.E ((s1 * s2 : 𝓞 X.B.I.F) : X.B.I.F) * e) ^ 2 -
      ((liftE X (s2 * t1) : 𝓞 X.B.I.E) : X.B.I.E) * (algebraMap X.B.I.F X.B.I.E ((s1 * s2 : 𝓞 X.B.I.F) : X.B.I.F) * e) +
      ((liftE X (s1 * s1 * s2 * t2) : 𝓞 X.B.I.E) : X.B.I.E) = 0 := by
    rw [liftE_coe, liftE_coe]
    push_cast
    try simp only [map_mul]
    linear_combination (-(algebraMap X.B.I.F X.B.I.E (s1 : X.B.I.F) * algebraMap X.B.I.F X.B.I.E (s2 : X.B.I.F) ^ 2 * e)) * f1 +
      (algebraMap X.B.I.F X.B.I.E (s1 : X.B.I.F) ^ 2 * algebraMap X.B.I.F X.B.I.E (s2 : X.B.I.F)) * f2
  have hint : IsIntegral (𝓞 X.B.I.E) (algebraMap X.B.I.F X.B.I.E ((s1 * s2 : 𝓞 X.B.I.F) : X.B.I.F) * e) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (liftE X (s2 * t1)) * Polynomial.X +
      Polynomial.C (liftE X (s1 * s1 * s2 * t2)), by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    exact hrel
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact ⟨c, hc⟩

end Loc

end MassDataIdxSteps
