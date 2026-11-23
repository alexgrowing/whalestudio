import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEisensteinImageTeichmullerPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerDistinguishedSpanIsPrimeAndNotMemStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem dvd_pow_of_ne_zero_untilt (l : ℕ) [Fact l.Prime] (y : Formalism.Per.OC l) (hy : y ≠ 0) :
    ∃ n : ℕ, y ∣ (l : Formalism.Per.OC l) ^ n := by
  have hy' : (y : ℂ_[l]) ≠ 0 := fun h => hy (Subtype.ext h)
  have hpos : 0 < ‖(y : ℂ_[l])‖ := norm_pos_iff.2 hy'
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (GlobalTheory.RingBasics.norm_p_lt (p := l))
  refine ⟨n, ⟨(l : ℂ_[l]) ^ n / y, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div, norm_pow, div_le_one hpos]
    exact hn.le
  · push_cast
    exact (mul_div_cancel₀ _ hy').symm

theorem constantCoeff_natCast_untilt (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [CharP O l] :
    WittVector.constantCoeff ((l : ℕ) : WittVector l O) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

theorem exists_untilt_map : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∃ θ' : OC l →+* (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}), (∀ a : Ainf l, θ' (Per.θ l a) = Ideal.Quotient.mk _ (WittVector.map ψ a)) ∧ Function.Injective θ' ∧ IsDomain (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) ∧ ∀ a : WittVector l O, ((l : ℕ) : WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) ∣ Ideal.Quotient.mk _ a → ψ bk.flat ^ bk.Ep.natDegree ∣ a.coeff 0 := by
  intro l _ K bk O _ _ _ _ _ ψ h0 hu hc
  obtain ⟨w, hw, hE⟩ := GlobalTheory.T.breuilKisin_eisenstein_image_teichmuller_pow l K bk O ψ hu
  obtain ⟨hp, hl⟩ := GlobalTheory.T.teichmullerDistinguished_span_isPrime_and_not_mem l O _ h0 hu hc _ w _ bk.deg_pos hw hE
  have hdom : IsDomain (WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)}) :=
    Ideal.Quotient.isDomain _
  have hker : RingHom.ker (Per.θ l) ≤ RingHom.ker ((Ideal.Quotient.mk
      (Ideal.span {WittVector.map ψ (bk.ev bk.E)})).comp (WittVector.map ψ)) := by
    rw [← bk.span_ev, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  refine ⟨(Per.θ l).liftOfSurjective (theta_onto l) ⟨_, hker⟩, fun a => ?_, ?_, hdom, ?_⟩
  · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ a
  · rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hne
    obtain ⟨n, z, hz⟩ := dvd_pow_of_ne_zero_untilt l y hne
    have h := congrArg ((Per.θ l).liftOfSurjective (theta_onto l) ⟨_, hker⟩) hz
    rw [map_mul, hy, zero_mul, map_pow, map_natCast] at h
    have h2 := eq_zero_of_pow_eq_zero h
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem] at h2
    exact hl h2
  · rintro a ⟨b, hb⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hb
    obtain ⟨c, hc⟩ := hb
    have h := congrArg WittVector.constantCoeff hc
    rw [hE, map_mul, map_add, map_mul, map_sub, map_mul, constantCoeff_natCast_untilt, zero_mul, zero_mul,
      add_zero, sub_zero, map_pow, WittVector.constantCoeff_apply (WittVector.teichmuller _ _),
      WittVector.teichmuller_coeff_zero] at h
    exact ⟨_, h.symm.trans (mul_comm _ _)⟩

end GlobalTheory.BSP
