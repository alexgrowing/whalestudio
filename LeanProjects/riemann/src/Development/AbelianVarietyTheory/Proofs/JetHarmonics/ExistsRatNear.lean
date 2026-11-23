import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership GlobalTheory.PlaceComponents GlobalTheory.QuadSubfield

namespace GlobalTheory.PlaceApprox

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem exists_rat_near (h : ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε) (c : D.host.K) (η : ℝ) (hη : 0 < η) :
    ∃ t : ℚ, ‖homP D lam c - (t : ℂ_[p])‖ < η := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  set S := ‖homP D lam c‖ + ‖homPbar D lam c‖ + 1 with hS
  have hS0 : 0 < S := by positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hη hS0) (inv_lt_one_of_one_lt₀ hp)
  obtain ⟨ε, hε⟩ := h m
  rw [isIdem_iff, zpow_neg, zpow_natCast, ← inv_pow] at hε
  obtain ⟨t, -, ht, -⟩ := exists_trace_norm D ((ε : D.host.K) * c)
  refine ⟨t, ?_⟩
  have h1 := congrArg (homP D lam) ht
  rw [map_add, homP_conjK, map_mul, map_mul, map_ratCast] at h1
  have h2 : homP D lam c - (t : ℂ_[p]) =
      -((homP D lam (ε : D.host.K) - 1) * homP D lam c + homPbar D lam (ε : D.host.K) * homPbar D lam c) := by
    rw [← h1]; ring
  rw [h2, norm_neg]
  rw [lt_div_iff₀ hS0] at hm
  have hq : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ m := by positivity
  calc _ ≤ ‖homP D lam (ε : D.host.K) - 1‖ * ‖homP D lam c‖ +
        ‖homPbar D lam (ε : D.host.K)‖ * ‖homPbar D lam c‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ (p : ℝ)⁻¹ ^ m * ‖homP D lam c‖ + (p : ℝ)⁻¹ ^ m * ‖homPbar D lam c‖ := by
        gcongr
        exacts [hε.1, hε.2]
    _ ≤ (p : ℝ)⁻¹ ^ m * S := by rw [hS]; nlinarith
    _ < η := hm

theorem exists_padic (h : ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε) (c : D.host.K) :
    ∃ x : ℚ_[p], algebraMap ℚ_[p] ℂ_[p] x = homP D lam c := by
  have hc : IsClosed (Set.range (algebraMap ℚ_[p] ℂ_[p])) :=
    (algebraMap_isometry ℚ_[p] ℂ_[p]).isClosedEmbedding.isClosed_range
  have : homP D lam c ∈ closure (Set.range (algebraMap ℚ_[p] ℂ_[p])) := by
    rw [Metric.mem_closure_iff]
    intro η hη
    obtain ⟨t, ht⟩ := exists_rat_near D lam h c η hη
    exact ⟨t, ⟨t, map_ratCast _ t⟩, by rwa [dist_eq_norm]⟩
  rwa [hc.closure_eq] at this

theorem exists_padicInt (h : ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε) (c : D.host.K)
    (hc : ‖homP D lam c‖ ≤ 1) : ∃ z : ℤ_[p], zc z = homP D lam c := by
  obtain ⟨x, hx⟩ := exists_padic D lam h c
  rw [← hx, norm_algebraMap'] at hc
  exact ⟨⟨x, hc⟩, hx⟩

theorem approx : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    (∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε) → ∀ c : D.host.K,
      (‖atP D lam c‖ ≤ 1 → ∀ n : ℕ, ∃ k : ℕ, k < p ^ n ∧ ‖atP D lam c - (k : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ))) ∧
      (‖atPbar D lam c‖ ≤ 1 → ∃ z : ℤ_[p], zc z = atPbar D lam c) := by
  intro D p _ lam h c
  rw [atP₂, atPbar_eq]
  refine ⟨fun hc n => ?_, fun hc => exists_padicInt D lam h (conjK D c) hc⟩
  obtain ⟨z, hz⟩ := exists_padicInt D lam h c hc
  refine ⟨z.appr n, z.appr_lt n, ?_⟩
  have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (z.appr_spec n)
  have h2 : homP D lam c - (z.appr n : ℂ_[p]) =
      algebraMap ℚ_[p] ℂ_[p] ((z - (z.appr n : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) := by
    rw [← hz, PadicInt.coe_sub, map_sub, PadicInt.coe_natCast, map_natCast]; rfl
  rw [h2, norm_algebraMap']
  exact h1

end GlobalTheory.PlaceApprox
