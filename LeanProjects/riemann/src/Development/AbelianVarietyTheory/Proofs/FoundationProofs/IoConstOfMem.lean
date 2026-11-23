import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsModularFunctionTowerAlgebraicCoefficients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspInhabited
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReparametrizationByTowerParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalValueOfQuotientAddOfCommonDenominator

noncomputable section

namespace GlobalTheory.Glue.IoInh

open GlobalTheory.K5 GlobalTheory.KZ

section Local

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

theorem ev_single (ψ : O0 p →+* Ωl) (e : Ωl) (h1 : IsInt p e) (h2 : IsAlgZp p e) (a : Lau p) (c : ℤ → Ωl)
    (hc : ∀ r, c r = e * zp Ωl (a.coeff r)) :
    Ev ψ c (e * ψ (algebraMap (Lau p) (O0 p) a)) (e * ψ (algebraMap (Lau p) (O0 p) (thL a))) :=
  ⟨1, fun _ => e, fun _ => a, fun _ => ⟨h1, h2⟩, fun r => by simp [hc], by simp, by simp⟩

theorem zp_intCast (m : ℤ) : zp Ωl (m : ℤ_[p]) = (m : Ωl) := by
  rw [zp, ← HahnSeries.C_apply, map_intCast, map_intCast, map_intCast]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem const_mem (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (c : Ω) : algebraMap Ω X.K c ∈ KT X L :=
  (X.sl _).commutes c

theorem exp_const (X : GlobalTheory.KZ.Tower Ω ε) (c : Ω) (r : ℚ) :
    (X.exp (algebraMap Ω X.K c)).coeff r = if r = 0 then c else 0 := by
  rw [AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs <;> rfl

variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ}
  {ψ : O0 p →+* Ωl} {io : KT X (p ^ n) →+* Ωl}

theorem io_const_of_mem (h : IsClo p Ωl) (hc : IsCusp ε A T j) (hψ : IsReb T n ψ) (hio : IsIo X A T j n ψ io)
    (c : Ω) (hA : c ∈ A) : io ⟨algebraMap Ω X.K c, const_mem X _ c⟩ = j c := by
  classical
  obtain ⟨x', hx⟩ := hio.ev ⟨algebraMap Ω X.K c, const_mem X _ c⟩ {c} (fun r => by
    simp only [exp_const]
    split_ifs
    · exact ⟨hA, IntermediateField.subset_adjoin _ _ (by simp)⟩
    · exact ⟨zero_mem _, zero_mem _⟩)
  have hp0 : (p : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have h2 := ev_single ψ (j c) ((hc.int c).1 hA) (hc.alg c) 1
    (fun r : ℤ => j ((X.exp (algebraMap Ω X.K c)).coeff ((r : ℚ) / (p : ℚ) ^ n))) (fun r => by
      simp only [exp_const]
      by_cases hr : r = 0
      · subst hr
        have : zp Ωl (1 : ℤ_[p]) = 1 := by simpa using zp_intCast (p := p) (Ωl := Ωl) 1
        simp [this]
      · have : zp Ωl (0 : ℤ_[p]) = 0 := by simpa using zp_intCast (p := p) (Ωl := Ωl) 0
        have h3 : (r : ℚ) / (p : ℚ) ^ n ≠ 0 := div_ne_zero (by exact_mod_cast hr) hp0
        simp [this, h3, HahnSeries.coeff_one, hr])
  have := (GlobalTheory.EvUniq.ev_unique p Ωl h T n ψ hψ _ _ _ _ _ hx h2).1
  rwa [map_one, map_one, mul_one] at this

theorem io_const (h : IsClo p Ωl) (hc : IsCusp ε A T j) (hψ : IsReb T n ψ) (hio : IsIo X A T j n ψ io)
    (c : Ω) : io ⟨algebraMap Ω X.K c, const_mem X _ c⟩ = j c := by
  rcases A.mem_or_inv_mem c with hA | hA
  · exact io_const_of_mem h hc hψ hio c hA
  · have h1 := io_const_of_mem h hc hψ hio c⁻¹ hA
    have h2 : (⟨algebraMap Ω X.K c⁻¹, const_mem X _ c⁻¹⟩ : KT X (p ^ n)) = ⟨algebraMap Ω X.K c, const_mem X _ c⟩⁻¹ :=
      Subtype.ext (map_inv₀ _ _)
    rw [h2, map_inv₀, map_inv₀] at h1
    exact inv_injective h1

end Local

end GlobalTheory.Glue.IoInh
