import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdemEvalAndDualDiffIff
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuesOfDiscrFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.TBIdemDen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open Classical

namespace GlobalTheory.IdemDenominatorCp

open GlobalTheory.IndefiniteRowSideFullHecke.IntegralPartDecomposition GlobalTheory.IdemCompare

theorem val_p_lt_one (p : ℕ) [hp : Fact p.Prime] :
    (𝓞_ℂ_[p]).valuation (p : ℂ_[p]) < 1 := by
  by_contra h
  push_neg at h
  have hp0 : (p : ℂ_[p]) ≠ 0 := by
    intro h0
    have := GlobalTheory.PadicComplexHost.norm_p p
    rw [h0, norm_zero] at this
    have : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hp.out.pos)
    linarith
  have h1 : (𝓞_ℂ_[p]).valuation ((p : ℂ_[p])⁻¹) ≤ 1 := by
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ h
  have h2 := ((𝓞_ℂ_[p]).valuation_le_one_iff _).1 h1
  rw [GlobalTheory.PadicComplexHost.mem_iff_norm, norm_inv, GlobalTheory.PadicComplexHost.norm_p, inv_inv] at h2
  have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  linarith

theorem idem_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime] (φ : E →+* ℂ_[p]), ∃ (d : ℂ_[p]) (n : ℕ) (r : Fin n → 𝓞_ℂ_[p]) (a : Fin n → 𝓞 E), (p : ℝ) ^ (-((padicValNat p (discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ))) ≤ ‖d‖ ∧ ∀ σ : E →+* ℂ_[p], ∑ k, algebraMap 𝓞_ℂ_[p] ℂ_[p] (r k) * σ (a k) = if σ = φ then d else 0 := by
  intro E _ _ _ p _ φ
  have hp : p.Prime := Fact.out
  set n := Module.finrank ℚ E with hn_def
  set a := padicValNat p (discr E).natAbs with ha_def
  have hn : n ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℂ_[p]) ^ a) (Nat.pos_of_ne_zero hn)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hnorm : ‖d‖ = (p : ℝ) ^ (-((a : ℝ) / n)) := by
    have h1 : ‖d‖ ^ n = ((p : ℝ) ^ (-((a : ℝ) / n))) ^ n := by
      rw [← norm_pow, hd, norm_pow, GlobalTheory.PadicComplexHost.norm_p, ← Real.rpow_natCast _ n,
        ← Real.rpow_mul hp0.le]
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      rw [show -((a : ℝ) / n) * n = -(a : ℝ) by field_simp]
      rw [Real.rpow_neg hp0.le, Real.rpow_natCast, inv_pow]
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) hn).1 h1
  let b := Module.finBasis ℤ (𝓞 E)
  let O : ValuationSubring ℂ_[p] := 𝓞_ℂ_[p]
  have hint : ∀ x : 𝓞 E, φ (x : E) ∈ O := fun x => integer_mem O φ x.isIntegral_coe
  let ψ : 𝓞 E →+* O := (φ.comp (algebraMap (𝓞 E) E)).codRestrict O hint
  have hψ : ∀ x : 𝓞 E, x ∈ (IsLocalRing.maximalIdeal O).comap ψ ↔
      O.valuation (φ (x : E)) < 1 := fun x => by
    rw [Ideal.mem_comap, O.valuation_lt_one_iff]; rfl
  have hpw : (p : 𝓞 E) ∈ (IsLocalRing.maximalIdeal O).comap ψ :=
    (hψ _).2 (by simpa using val_p_lt_one p)
  let w : HeightOneSpectrum (𝓞 E) := ⟨(IsLocalRing.maximalIdeal O).comap ψ, inferInstance,
    fun h0 => hp.ne_zero (by rw [h0] at hpw; simpa using hpw)⟩
  have hw : Induces O φ w := hψ
  obtain ⟨m, hm, hdisc⟩ := (GlobalTheory.DifferentExponentCompare.exists_cofactor_iff (E := E) hp a).mpr rfl
  have hexp : differentExp_vw w * n = a * ramExp p w :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E p a m hp hm hdisc w.asIdeal w.isPrime hpw
  have hv : ValGeDifferent_vp O p w d := by
    unfold ValGeDifferent_vp
    have key : (O.valuation d ^ ramExp p w) ^ n = (O.valuation (p : ℂ_[p]) ^ differentExp_vw w) ^ n := by
      rw [← pow_mul, ← pow_mul, hexp, mul_comm (ramExp p w), pow_mul, ← map_pow, hd, map_pow,
        ← pow_mul]
    by_contra hh
    push_neg at hh
    exact (pow_lt_pow_left₀ hh zero_le' hn).ne' key
  have hmem := (dualDiffSt_iff_vp.1 dual_difference) E ℂ_[p] _ b φ p hp O (val_p_lt_one p) w hw d hv
  rw [mul_idem_mem_iff] at hmem
  have hev := (idemEvalSt_iff.1 idempotent_evaluation) E ℂ_[p] _ b φ
  refine ⟨d, _, fun i => ⟨d * φ (dualBasis b i), hmem i⟩, fun i => b i, ?_, fun σ => ?_⟩
  · rw [hnorm]
  · have hsum : ∑ k, algebraMap 𝓞_ℂ_[p] ℂ_[p] ⟨d * φ (dualBasis b k), hmem k⟩ * σ ((b k : 𝓞 E) : E) =
        d * evalAt σ (GlobalTheory.IndefiniteRowSideFullHecke.IntegralPartDecomposition.idem b φ) := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.IntegralPartDecomposition.idem, map_sum, evalAt_tmul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      change d * φ (dualBasis b k) * σ ((b k : 𝓞 E) : E) = _
      ring
    rw [hsum]
    split_ifs with h
    · subst h; rw [hev.1, _root_.mul_one]
    · rw [hev.2 σ h, MulZeroClass.mul_zero]

end GlobalTheory.IdemDenominatorCp
