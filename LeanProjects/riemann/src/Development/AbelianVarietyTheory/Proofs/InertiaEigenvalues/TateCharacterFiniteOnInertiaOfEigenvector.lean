import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaPadicComplexFixedElementApproximationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicAlgHomSubDvdOfXDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEstimateGaloisEigenvectorCLTateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormInertiaPartialTraceGeometricLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowPrimePowSubOneStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.TateEigen

variable {l : ℕ} [Fact l.Prime]

theorem norm_l_pos : 0 < ‖((l : ℕ) : ℤ_[l])‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem norm_l_lt_one : ‖((l : ℕ) : ℤ_[l])‖ < 1 := by
  rw [PadicInt.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem exists_pow_near_one (k : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ u : ℤ_[l]ˣ, ‖((u ^ N : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ k := by
  have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨Nat.card (ZMod (l ^ k))ˣ, Nat.card_pos, fun u => ?_⟩
  have h : (Units.map (PadicInt.toZModPow (p := l) k).toMonoidHom u) ^ Nat.card (ZMod (l ^ k))ˣ = 1 :=
    pow_card_eq_one'
  have h2 : ((u ^ Nat.card (ZMod (l ^ k))ˣ : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈
      RingHom.ker (PadicInt.toZModPow (p := l) k) := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
    rw [← map_pow] at h
    exact congrArg Units.val h
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨w, hw⟩ := h2
  rw [hw, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one w)

theorem exists_norm_eq_pow (x : ℤ_[l]) (hx : x ≠ 0) : ∃ k : ℕ, ‖x‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k := by
  refine ⟨x.valuation, ?_⟩
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [norm_mul, PadicInt.norm_units, one_mul, norm_pow]

theorem finite_on_inertia : ∀ (l : ℕ) [Fact l.Prime] (η : GQ l →* ℤ_[l]ˣ) (y : ℂ_[l]), y ≠ 0 →
    (∀ g : GQ l, Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y) →
    ∃ N : ℕ, 0 < N ∧ ∀ γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup, η γ ^ N = 1 := by
  intro l _ η y hy hη
  obtain ⟨c, hc, hax⟩ := GlobalTheory.T.axLemma_padicComplex_fixed_element_approximation l
  have hτ0 := norm_l_pos (l := l)
  have hτ1 := norm_l_lt_one (l := l)
  set τ := ‖((l : ℕ) : ℤ_[l])‖ with hτ
  obtain ⟨k₁, hk₁⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hc) hτ1
  obtain ⟨N, hN, hNu⟩ := exists_pow_near_one (l := l) (k₁ + 2)
  refine ⟨N, hN, fun γ₀ hγ₀ => ?_⟩
  by_contra hne
  set γ := γ₀ ^ N with hγdef
  have hγ : γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup := pow_mem hγ₀ N
  have hηγ : η γ = η γ₀ ^ N := map_pow _ _ _
  have hne' : (η γ : ℤ_[l]) - 1 ≠ 0 := by
    intro h
    apply hne
    rw [← hηγ]
    exact Units.ext (sub_eq_zero.1 h)
  obtain ⟨k, hk⟩ := exists_norm_eq_pow _ hne'
  have hkk : k₁ + 2 ≤ k := by
    have := hNu (η γ₀)
    rw [← hηγ, hk] at this
    exact (pow_le_pow_iff_right_of_lt_one₀ hτ0 hτ1).1 this
  have hk2 : 2 ≤ k := by omega
  obtain ⟨H, hmem, hnorm, hidx, hidx', hpow, hgen⟩ := GlobalTheory.T.exists_normal_subgroup_filtration_index_bounded l η γ k hk2 hk
  obtain ⟨ρ, hρ0, hρ1, hgain⟩ := GlobalTheory.T.norm_inertia_partialTrace_geometric_le l γ hγ H k hnorm hidx hidx' hpow hgen
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hc) hρ1
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hr : 0 < τ ^ (k + n) * ‖y‖ := by positivity
  obtain ⟨z, hz, hyz⟩ := hax (H n) y (τ ^ (k + n) * ‖y‖) hr (by
    intro g hg
    have e : Per.σC g y - y = algebraMap ℚ_[l] ℂ_[l] ((((η g : ℤ_[l]) - 1 : ℤ_[l])) : ℚ_[l]) * y := by
      rw [hη g, PadicInt.coe_sub, PadicInt.coe_one, map_sub, map_one]; ring
    rw [e, norm_mul, norm_algebraMap']
    exact mul_le_mul_of_nonneg_right ((hmem n g).1 hg) hy0.le)
  have hv : ∀ g ∈ H n, g (γ z - algebraMap ℚ_[l] (Om l) ((η γ : ℤ_[l]) : ℚ_[l]) * z) =
      γ z - algebraMap ℚ_[l] (Om l) ((η γ : ℤ_[l]) : ℚ_[l]) * z := by
    intro g hg
    have h1 := hz _ ((hnorm n).conj_mem' g hg γ)
    have h2 : g (γ z) = γ z := by
      have := congrArg γ h1
      simpa [mul_assoc] using this
    rw [map_sub, map_mul, h2, hz g hg, AlgEquiv.commutes]
  have hest := GlobalTheory.T.tate_estimate_galois_eigenvector_cLTate l γ ((η γ : ℤ_[l]) : ℚ_[l]) y z (l ^ n) (c * (τ ^ (k + n) * ‖y‖)) (ρ ^ n)
    (hη γ) (PadicInt.norm_units (η γ)) (hz _ (hpow n)) hyz (hgain n _ hv) (by positivity)
  have hlte := GlobalTheory.T.norm_pow_prime_pow_sub_one_of_norm_sub_one l (η γ : ℤ_[l]) k hk2 hk n
  have e1 : ‖((η γ : ℤ_[l]) : ℚ_[l]) ^ l ^ n - 1‖ = τ ^ (k + n) := by
    rw [hτ, ← hlte, PadicInt.norm_def]; push_cast; rfl
  have e2 : ‖((η γ : ℤ_[l]) : ℚ_[l]) - 1‖ = τ ^ k := by
    rw [hτ, ← hk, PadicInt.norm_def]; push_cast; rfl
  rw [e1, e2] at hest
  have hk' : τ ^ k < c⁻¹ := lt_of_le_of_lt (pow_le_pow_of_le_one hτ0.le hτ1.le (by omega)) hk₁
  have key : ∀ a : ℝ, a < c⁻¹ → a * (c * (τ ^ (k + n) * ‖y‖)) < τ ^ (k + n) * ‖y‖ := by
    intro a ha
    have : a * c < 1 := by
      have := mul_lt_mul_of_pos_right ha hc
      rwa [inv_mul_cancel₀ hc.ne'] at this
    rw [← mul_assoc]
    exact mul_lt_of_lt_one_left hr this
  exact absurd hest (not_le.2 (max_lt (key _ hk') (key _ hn)))

end GlobalTheory.TateEigen
