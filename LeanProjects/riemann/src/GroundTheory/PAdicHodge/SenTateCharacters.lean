import Mathlib
import GroundTheory.PAdicHodge.SenTateCharTrace
import GroundTheory.PAdicHodge.SenTateCharQp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open CyclNorms GroundTheory.LocalField ValuativeRel SenTateChar

variable {p : ℕ} [hp : Fact p.Prime]

namespace SenTateChar

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]
  {η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ}

theorem eq_zero_of_mem_inertiaGal (hη : Continuous η) {τ : Gal(PadicAlgCl p/K)}
    (hτ : τ ∈ inertiaGal K) (hτ2 : η τ ∈ unitsOneAdd p 2) (hτ1 : η τ ≠ 1) {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), algebraMap ℚ_[p] ℂ_[p] ((η σ : ℤ_[p]) : ℚ_[p]) * (σ • x) = x) :
    x = 0 := by
  have hA := artinImage_ne_bot hη hτ hτ2 hτ1
  have hfin : ∀ k, FiniteDimensional K (charTower η k) := fun k => finiteDimensional_charTower hη k
  have : IsAbelianGalois K (charTower η 2) := isAbelianGalois_charTower hη 2

  have h2 : ∀ n, conductor (charTower η 2) ≤ n → 2 ≤ artinLevel K η n := by
    intro n hn
    obtain ⟨-, a, ha, ha'⟩ := artinLevel_spec (hA n)
    have ha2 := artinImage_le_of_conductor_le hη hn ha
    by_contra hlt
    push Not at hlt
    exact ha' (unitsOneAdd_antitone (by omega) ha2)

  obtain ⟨n₁, hn₁⟩ := exists_map_pow_unitFiltrationUnits (K := K) p
  set n₀ := max (conductor (charTower η 2)) n₁
  have hper : ∀ n, n₀ ≤ n →
      artinLevel K η (n + absRamificationIndex K) = artinLevel K η n + 1 :=
    fun n hn => artinLevel_add hη hA (h2 n (le_of_max_le_left hn)) (hn₁ n (le_of_max_le_right hn))
  have h2₀ : 2 ≤ artinLevel K η n₀ := h2 n₀ (le_max_left _ _)

  obtain ⟨b, hb, hb'⟩ := exists_level hτ1
  have hb2 : 2 ≤ b := by
    by_contra hlt
    push Not at hlt
    exact hb' (unitsOneAdd_antitone (by omega) hτ2)

  set π : PadicAlgCl p := algebraMap K (PadicAlgCl p) (baseUnif K : K)
  set C : ℝ := ‖π ^ (-(2 * absRamificationIndex K : ℤ))‖
  have hbound : ∀ n, max (artinLevel K η n₀) b ≤ n → ∀ m, ∀ y ∈ charTower η m,
      ‖normTrace (charTower η n) y‖ ≤ C * ‖y‖ := by
    intro n hn m y hy
    have h := nrm_normTrace_charTower_le hη hA le_rfl h2₀ hper hb2 hb hb'
      (le_of_max_le_right hn) (le_of_max_le_left hn) hy
    have e : baseUnifNrm K (PadicAlgCl p) ^ (-(2 * absRamificationIndex K : ℝ)) =
        nrm K (π ^ (-(2 * absRamificationIndex K : ℤ))) := by
      rw [nrm_zpow, ← Real.rpow_intCast]
      push_cast
      rfl
    rw [e, ← nrm_mul, nrm_le_nrm_iff_norm_le', norm_mul] at h
    exact h
  refine eq_zero_of_tower K η (charTower η) (charTower_mono η)
    (fun σ k y hy => map_mem_charTower hη σ hy) (fun σ hσ => ?_) C (max (artinLevel K η n₀) b)
    hbound (fun n hn => ?_) hx
  · refine eq_one_of_forall_mem_unitsOneAdd fun k => ?_
    have := hσ k
    rwa [fixingSubgroup_charTower hη, mem_charTowerGal] at this
  · obtain ⟨h1, h1'⟩ := pow_prime_pow_mem_not_mem hb2 hb hb' (n - b)
    rw [Nat.add_sub_cancel' (le_of_max_le_right hn)] at h1 h1'
    refine ⟨τ ^ p ^ (n - b), ?_, ?_⟩
    · rw [fixingSubgroup_charTower hη, mem_charTowerGal, map_pow]
      exact h1
    · rw [map_pow]
      intro h
      exact h1' (h ▸ one_mem _)

end SenTateChar

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]

theorem finite_image_inertiaGal_of_invariant (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ)
    (hη : Continuous η)
    (hx : ∃ x : ℂ_[p], x ≠ 0 ∧ ∀ σ : Gal(PadicAlgCl p/K),
      algebraMap ℚ_[p] ℂ_[p] ((η σ : ℤ_[p]) : ℚ_[p]) * (σ • x) = x) :
    (η '' (inertiaGal K : Set Gal(PadicAlgCl p/K))).Finite := by
  by_contra hinf
  obtain ⟨τ, hτ, hτ2, hτ1⟩ := exists_mem_inertiaGal_unitsOneAdd_two K η hη hinf
  obtain ⟨x, hx0, hx⟩ := hx
  exact hx0 (eq_zero_of_mem_inertiaGal hη hτ hτ2 hτ1 hx)

theorem finite_image_inertiaGal_of_invariant_padic (η : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ)
    (hη : Continuous η)
    (hx : ∃ x : ℂ_[p], x ≠ 0 ∧ ∀ σ : Gal(PadicAlgCl p/K),
      algebraMap ℚ_[p] ℂ_[p] (η σ : ℚ_[p]) * (σ • x) = x) :
    (η '' (inertiaGal K : Set Gal(PadicAlgCl p/K))).Finite := by
  obtain ⟨η', hη', hηη'⟩ := exists_continuous_units_padicInt_lift η hη
  have h := finite_image_inertiaGal_of_invariant K η' hη' (by
    obtain ⟨x, hx0, hx⟩ := hx
    exact ⟨x, hx0, fun σ => by rw [hηη']; exact hx σ⟩)
  refine (h.image (Units.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom)).subset ?_
  rintro _ ⟨σ, hσ, rfl⟩
  refine ⟨η' σ, ⟨σ, hσ, rfl⟩, ?_⟩
  ext
  rw [Units.coe_map, ← hηη' σ]
  rfl

end GroundTheory.PAdicHodge
