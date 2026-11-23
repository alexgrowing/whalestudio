import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesCongIffCoeffAndIsUnitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePadicSpanOfPowPMulMemStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

noncomputable section

namespace GlobalTheory.GeoFix.Divide

theorem divide_ev : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p),
    (∀ t, IsInt p (e t) ∧ IsAlgZp p (e t)) → ∀ (v : ℕ) (o : Ω), IsInt p o →
    ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) = (p : Ω) ^ v * o → ∃ (c : ℤ → Ω) (x' : Ω), Ev ψ c o x' := by
  intro p _ Ω _ _ hc T n ψ h d e a he v o ho hsum
  classical
  haveI := Basic.charZero_of_isClo hc
  set c : ℤ → Ω := fun r => ∑ t, e t * zp Ω ((a t).coeff r) with hcdef
  have hev : Ev ψ c (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)))
      (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t)))) :=
    ⟨d, e, a, he, fun r => rfl, rfl, rfl⟩
  have hcong : Cong p v (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) 0 :=
    ⟨o, ho, by rw [sub_zero, hsum]⟩
  have hcr := ((GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ω hc T n ψ h v c _ _ hev).1.1 hcong)
  choose y hy hcy using hcr
  obtain ⟨m, f, hf, hlat⟩ := GlobalTheory.T.exists_finite_padic_span_of_pow_p_mul_mem p Ω hc d e he v
  have hμ : ∀ r, ∃ μ : Fin m → ℤ_[p], y r = ∑ j, zp Ω (μ j) * f j := by
    intro r
    refine hlat (fun t => (a t).coeff r) (y r) (hy r) ?_
    have := hcy r
    rw [sub_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  choose μ hμ using hμ
  let μ' : ℤ → Fin m → ℤ_[p] := fun r => if ∀ t, (a t).coeff r = 0 then 0 else μ r
  have hsupp : ∀ j, (Function.support fun r => μ' r j) ⊆ ⋃ t ∈ (Finset.univ : Finset (Fin d)), (a t).support := by
    intro j r hr
    simp only [Function.mem_support] at hr
    by_cases h0 : ∀ t, (a t).coeff r = 0
    · exact absurd (by simp [μ', h0]) hr
    · push_neg at h0
      obtain ⟨t, ht⟩ := h0
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ t)) ht
  have hpwo : (⋃ t ∈ (Finset.univ : Finset (Fin d)), (a t).support).IsPWO :=
    (Finset.univ.isPWO_bUnion).2 fun t _ => (a t).isPWO_support
  let Λ : Fin m → Lau p := fun j => ⟨fun r => μ' r j, hpwo.mono (hsupp j)⟩
  have hΛ : ∀ j r, (Λ j).coeff r = μ' r j := fun _ _ => rfl

  let Λp : Fin m → Lau p := fun j => HahnSeries.C ((p : ℤ_[p]) ^ v) * Λ j
  have hzpp : zp Ω ((p : ℤ_[p]) ^ v) = (p : Ω) ^ v := by
    rw [← GlobalTheory.EvUniq.zpHom_apply, map_pow, map_natCast]
  have hcoef : ∀ r, c r = ∑ j, f j * zp Ω ((Λp j).coeff r) := by
    intro r
    have hc1 : ∀ j, zp Ω ((Λp j).coeff r) = (p : Ω) ^ v * zp Ω (μ' r j) := by
      intro j
      simp only [Λp, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, hΛ]
      rw [← GlobalTheory.EvUniq.zpHom_apply, map_mul, GlobalTheory.EvUniq.zpHom_apply, GlobalTheory.EvUniq.zpHom_apply, hzpp]
    simp only [hc1]
    by_cases h0 : ∀ t, (a t).coeff r = 0
    · have hμ0 : μ' r = 0 := by simp [μ', h0]
      have hz : zp Ω (0 : ℤ_[p]) = 0 := by rw [← GlobalTheory.EvUniq.zpHom_apply, map_zero]
      simp [hcdef, h0, hμ0, hz]
    · have hμr : μ' r = μ r := by simp [μ', h0]
      have := hcy r
      rw [sub_zero] at this
      rw [this, hμ r, hμr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hev2 : Ev ψ c (∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λp j)))
      (∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (thL (Λp j)))) :=
    ⟨m, f, Λp, hf, hcoef, rfl, rfl⟩
  have heq := (GlobalTheory.EvUniq.ev_unique p Ω hc T n ψ h c _ _ _ _ hev hev2).1
  have hval : ∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λp j)) =
      (p : Ω) ^ v * ∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λ j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Λp, map_mul, GlobalTheory.EvUniq.psi_C h, hzpp]
    ring
  have hp0 : (p : Ω) ^ v ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have ho' : o = ∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λ j)) := by
    rw [hsum, hval] at heq
    exact mul_left_cancel₀ hp0 heq
  exact ⟨fun r => ∑ j, f j * zp Ω ((Λ j).coeff r), _, m, f, Λ, hf, fun r => rfl, ho', rfl⟩

end GlobalTheory.GeoFix.Divide
