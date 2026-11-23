import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.Den

theorem local_exponent {F : Type} [Field F] [NumberField F] (v : Pl F) {y : F} (hy : y ≠ 0) :
    ∃ e : ℕ, v.valuation F y ≤ WithZero.exp (e : ℤ) ∧
      max 1 ‖algebraMap F (Fv F v) y‖₊ = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ e := by
  have ha : v.valuation F y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hq : (1 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have hnorm : ‖algebraMap F (Fv F v) y‖₊ =
      WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (v.valuation F y) :=
    NNReal.eq (FinitePlace.norm_embedding' v y)
  obtain ⟨n, hn⟩ : ∃ n : ℤ, v.valuation F y = WithZero.exp n := ⟨_, (WithZero.exp_log ha).symm⟩
  have hval : WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : ℝ≥0) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    simp [WithZero.exp]
  refine ⟨n.toNat, ?_, ?_⟩
  · rw [hn]
    exact WithZero.exp_le_exp.2 (Int.self_le_toNat n)
  · rw [hnorm, hn, hval]
    rcases le_total n 0 with h | h
    · rw [Int.toNat_of_nonpos h, pow_zero]
      exact max_eq_left (zpow_le_one_of_nonpos₀ hq.le h)
    · have h1 : (Ideal.absNorm v.asIdeal : ℝ≥0) ^ n = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ n.toNat := by
        rw [← zpow_natCast, Int.toNat_of_nonneg h]
      rw [h1]
      exact max_eq_right (one_le_pow₀ hq.le)

theorem finite_mulSupport {F : Type} [Field F] [NumberField F] {y : F} (hy : y ≠ 0) :
    (Function.mulSupport fun v : Pl F => max 1 ‖algebraMap F (Fv F v) y‖₊).Finite := by
  have h := (FinitePlace.hasFiniteMulSupport hy).comp_of_injective
    (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective
  refine Set.Finite.subset h ?_
  intro v hv
  simp only [Function.mem_mulSupport] at hv ⊢
  intro h1
  apply hv
  have h2 : ‖algebraMap F (Fv F v) y‖₊ = 1 := by
    apply NNReal.eq
    have h3 : ‖FinitePlace.embedding v y‖ = 1 := by
      simpa [FinitePlace.equivHeightOneSpectrum_symm_apply] using h1
    exact h3
  rw [h2, max_self]

theorem denominator_le (F : Type) [Field F] [NumberField F] (y : F) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ≥0) ≤ ∏ᶠ v : Pl F, max 1 ‖algebraMap F (Fv F v) y‖₊ ∧
      IsIntegral ℤ ((m : F) * y) := by
  classical
  by_cases hy : y = 0
  · subst hy
    exact ⟨1, one_pos, by simp, by simpa using isIntegral_zero⟩
  choose e he1 he2 using fun v : Pl F => local_exponent v hy
  have hfin := finite_mulSupport hy
  set S : Finset (Pl F) := hfin.toFinset with hS
  set b : Ideal (𝓞 F) := ∏ v ∈ S, v.asIdeal ^ e v with hb
  have hb0 : b ≠ ⊥ := by
    rw [hb, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro v _
    exact pow_ne_zero _ v.ne_bot
  have hm : 0 < Ideal.absNorm b :=
    Nat.pos_of_ne_zero fun h => hb0 (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm b, hm, le_of_eq ?_, ?_⟩
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS])]
    simp only [he2]
    simp [hb, map_prod, map_pow]
  · have key : ∀ v : Pl F, v.valuation F ((Ideal.absNorm b : F) * y) ≤ 1 := by
      intro v
      have hmem : ((Ideal.absNorm b : ℕ) : 𝓞 F) ∈ v.asIdeal ^ e v := by
        by_cases hv : v ∈ S
        · exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv) (Ideal.absNorm_mem b)
        · have h1 : max 1 ‖algebraMap F (Fv F v) y‖₊ = 1 := by
            simpa [hS] using hv
          have h0 : e v = 0 := by
            by_contra hne
            have hq : (1 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) :=
              HeightOneSpectrum.one_lt_absNorm_nnreal v
            have := one_lt_pow₀ hq hne
            rw [← he2 v, h1] at this
            exact lt_irrefl _ this
          simp [h0]
      have h2 := (v.intValuation_le_pow_iff_mem _ (e v)).2 hmem
      have h3 : v.valuation F (Ideal.absNorm b : F) ≤ WithZero.exp (-(e v : ℤ)) := by
        have : (Ideal.absNorm b : F) = algebraMap (𝓞 F) F ((Ideal.absNorm b : ℕ) : 𝓞 F) := by simp
        rw [this, HeightOneSpectrum.valuation_of_algebraMap]
        exact h2
      rw [map_mul]
      calc _ ≤ WithZero.exp (-(e v : ℤ)) * WithZero.exp (e v : ℤ) := mul_le_mul' h3 (he1 v)
        _ = 1 := by rw [← WithZero.exp_add]; simp
    obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ key
    rw [← hc]
    exact c.isIntegral_coe

end GlobalTheory.CompanionTheory.GodementH.Den

end
