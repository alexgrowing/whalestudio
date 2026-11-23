import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfEnvelopeModPrimePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdAllPowOfFrobeniusEqKilledByPerfectPointsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopePointFactorsThroughSectionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

set_option maxHeartbeats 1000000 in

theorem l_dvd_of_galois_sections : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, En.inl.f (bk.ev bk.E) ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)), s.comp En.inl = Hom.id _ → s.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ s.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  intro l _ K bk En κ _ x c h hx hs
  obtain ⟨-, -, -, -, -, -, hA7⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  obtain ⟨-, hM2, hM3⟩ := GlobalTheory.T.ainf_envelope_mod_prime_properties l K bk En
  let I : Ideal En.Q.A := Ideal.span {((l : ℕ) : En.Q.A)}
  let π : En.Q.A →+* En.Q.A ⧸ I := Ideal.Quotient.mk I
  have hπ : ∀ y, π y = 0 ↔ ((l : ℕ) : En.Q.A) ∣ y := fun y =>
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hl0 : ((l : ℕ) : En.Q.A ⧸ I) = 0 := by
    rw [← map_natCast π]; exact (hπ _).2 dvd_rfl
  have hreg : π (En.inl.f (bk.ev X)) ∈ nonZeroDivisors (En.Q.A ⧸ I) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : π (En.inl.f (bk.ev X) * y) = 0 := by rw [map_mul, mul_comm]; exact hy
    exact (hπ _).2 (hM2 y ((hπ _).1 this))
  have hE : π (En.inl.f (bk.ev bk.E)) = π (En.inl.f (bk.ev X)) ^ bk.Ep.natDegree := by
    let ι : Ainf l →+* En.Q.A := En.inl.f
    have h1 : ((l : ℕ) : En.Q.A) ∣ ι (bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree) := by
      have := map_dvd ι hA7
      rwa [map_natCast] at this
    have h2 := (hπ _).2 h1
    rw [map_sub, map_pow, map_sub, map_pow, sub_eq_zero] at h2
    exact h2
  have hl1 : π ((l : ℕ) : En.Q.A) = 0 := (hπ _).2 dvd_rfl
  have hφ : ∀ y, π (En.Q.D.φ y) = π y ^ l := fun y => by
    have e : π (En.Q.D.φ y - y ^ l) = 0 := (hπ _).2 ⟨En.Q.D.δ y, by rw [En.Q.D.φ_eq y]; ring⟩
    rwa [map_sub, map_pow, sub_eq_zero] at e
  have heq : ∀ j, π (En.inl.f (bk.ev X)) ^ (bk.Ep.natDegree * h) * π (x j) =
      ∑ i, π (x i) ^ l * π (c i j) := fun j => by
    have := congrArg π (hx j)
    rw [map_mul π, map_pow π, hE, ← pow_mul, map_sum π] at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul π, hφ]
  have hpts : ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (f : En.Q.A ⧸ I →+* O), f (π (En.inl.f (bk.ev X))) ≠ 0 → ¬ IsUnit (f (π (En.inl.f (bk.ev X)))) →
      IsAdicComplete (Ideal.span {f (π (En.inl.f (bk.ev X)))}) O → ∀ j, f (π (x j)) = 0 := by
    intro O _ _ _ _ _ f hf0 hfu hfc j
    obtain ⟨g, s, ψ, h1, h2, h3⟩ := GlobalTheory.T.breuilKisinEnvelope_point_factors_through_section l K bk En O (f.comp π) hf0 hfu hfc
    obtain ⟨z, hz⟩ := hs g s h1 h2 j
    have e := h3 (x j)
    rw [RingHom.comp_apply] at e
    rw [e, hz]
    have : WittVector.coeff (p := l) (R := OCb l) (((l : ℕ) : (ainfObj K).A) * z) 0 = 0 := by
      rw [mul_comm]; exact WittVector.mul_charP_coeff_zero (p := l) (R := OCb l) z
    rw [this, map_zero]
  have key := GlobalTheory.T.dvd_all_pow_of_frobenius_eq_killed_by_perfect_points l (En.Q.A ⧸ I) (π (En.inl.f (bk.ev X))) hl0 hreg κ (fun i => π (x i))
    (fun i j => π (c i j)) (bk.Ep.natDegree * h) heq (fun O _ _ _ _ _ f hf0 hfu hfc j => hpts O f hf0 hfu hfc j)
  intro j
  refine hM3 (x j) fun m => ?_
  obtain ⟨w, hw⟩ := key m j
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨z, (hπ _).1 ?_⟩
  change π (x j) = π (En.inl.f (bk.ev X)) ^ m * π z at hw
  rw [map_sub π, map_mul π, map_pow π, hw, sub_self]

end GlobalTheory.BSP
