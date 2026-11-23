import Mathlib
import Formalism.PeriodIntegrals.DiscrNe

open ModularForm EisensteinSeries UpperHalfPlane

noncomputable section

namespace DiscrNeWork

lemma lin_inj (τ : ℍ) {m n m' n' : ℤ} (h : (m : ℂ) * τ + n = (m' : ℂ) * τ + n') :
    m = m' ∧ n = n' := by
  have him := congrArg Complex.im h
  first
    | simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im] at him
    | simp at him
  have key : ((m : ℝ) - m') * (τ : ℂ).im = 0 := by
    first
      | linear_combination him
      | linarith
  have hpos : 0 < (τ : ℂ).im := τ.im_pos
  have hsub : (m : ℝ) - m' = 0 := (mul_eq_zero.mp key).resolve_right hpos.ne'
  have hm : m = m' := by exact_mod_cast sub_eq_zero.mp hsub
  subst hm
  refine ⟨rfl, ?_⟩
  have hn : (n : ℂ) = n' := add_left_cancel h
  exact_mod_cast hn

lemma lin_ne (τ : ℍ) (v : Fin 2 → ℤ) (hv : v ≠ 0) : ((v 0 : ℂ) * τ + v 1) ≠ 0 := by
  intro h0
  apply hv
  have h' : ((v 0 : ℤ) : ℂ) * τ + ((v 1 : ℤ) : ℂ) = ((0 : ℤ) : ℂ) * τ + ((0 : ℤ) : ℂ) := by
    first
      | (rw [h0]; simp)
      | simpa using h0
  obtain ⟨h1, h2⟩ := lin_inj τ h'
  funext i
  fin_cases i
  · exact h1
  · exact h2

def nz : Set (Fin 2 → ℤ) := {v | v ≠ 0}

def toLat (a : ℂ) (ha : a ≠ 0) (τ : ℍ) (v : nz) :
    {w : ℂ // w ∈ PI.lat2 a (a * τ) ∧ w ≠ 0} :=
  ⟨a * ((v.1 0 : ℂ) * τ + v.1 1), by
    refine ⟨?_, mul_ne_zero ha (lin_ne τ v.1 v.2)⟩
    rw [PI.lat2, AddSubgroup.mem_closure_pair]
    exact ⟨v.1 1, v.1 0, by simp only [zsmul_eq_mul]; ring⟩⟩

lemma toLat_bij (a : ℂ) (ha : a ≠ 0) (τ : ℍ) : Function.Bijective (toLat a ha τ) := by
  constructor
  · intro v v' hvv
    have h1 : a * ((v.1 0 : ℂ) * τ + v.1 1) = a * ((v'.1 0 : ℂ) * τ + v'.1 1) :=
      congrArg Subtype.val hvv
    have h2 := mul_left_cancel₀ ha h1
    obtain ⟨e0, e1⟩ := lin_inj τ h2
    apply Subtype.ext
    funext i
    fin_cases i
    · exact e0
    · exact e1
  · rintro ⟨w, hw, hw0⟩
    have hw' := hw
    rw [PI.lat2, AddSubgroup.mem_closure_pair] at hw'
    obtain ⟨m, n, hmn⟩ := hw'
    have hv : (![n, m] : Fin 2 → ℤ) ∈ nz := by
      intro h
      apply hw0
      have hn : n = 0 := congrFun h 0
      have hm : m = 0 := congrFun h 1
      rw [← hmn, hn, hm]
      simp
    refine ⟨⟨![n, m], hv⟩, ?_⟩
    apply Subtype.ext
    show a * ((((![n, m] : Fin 2 → ℤ) 0 : ℤ) : ℂ) * (τ : ℂ) + (((![n, m] : Fin 2 → ℤ) 1 : ℤ) : ℂ)) = w
    have e0 : (![n, m] : Fin 2 → ℤ) 0 = n := rfl
    have e1 : (![n, m] : Fin 2 → ℤ) 1 = m := rfl
    rw [e0, e1, ← hmn, zsmul_eq_mul, zsmul_eq_mul]
    ring

theorem eisG_eq (a : ℂ) (ha : a ≠ 0) (τ : ℍ) (k : ℕ) (hk : 1 ≤ k) :
    PI.eisG (PI.lat2 a (a * τ)) k =
      (a ^ (2 * k))⁻¹ * ∑' v : Fin 2 → ℤ, eisSummand ((2 * k : ℕ) : ℤ) v τ := by
  have hk2 : 2 * k ≠ 0 := by omega
  let e := Equiv.ofBijective _ (toLat_bij a ha τ)
  have hterm : ∀ v : nz, 1 / ((e v : ℂ)) ^ (2 * k) =
      (a ^ (2 * k))⁻¹ * eisSummand ((2 * k : ℕ) : ℤ) v.1 τ := by
    intro v
    have hX : eisSummand ((2 * k : ℕ) : ℤ) v.1 τ =
        1 / ((v.1 0 : ℂ) * (τ : ℂ) + (v.1 1 : ℂ)) ^ (2 * k) := by
      first
        | ((simp only [eisSummand, zpow_neg, zpow_natCast, one_div]) <;> rfl)
        | (simp [eisSummand, zpow_natCast, one_div])
        | (rw [eisSummand, zpow_neg, zpow_natCast, one_div])
        | (unfold eisSummand; done)
    show 1 / (a * ((v.1 0 : ℂ) * (τ : ℂ) + (v.1 1 : ℂ))) ^ (2 * k) = _
    rw [hX]
    first
      | (rw [mul_pow, one_div, one_div, mul_inv])
      | ring
  have hsupp : Function.support (fun v : Fin 2 → ℤ => eisSummand ((2 * k : ℕ) : ℤ) v τ) ⊆
      nz := by
    intro v hv
    show v ≠ 0
    rintro rfl
    apply hv
    first
      | (simp only [eisSummand, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, zpow_neg,
          zpow_natCast, zero_pow hk2, inv_zero, one_div])
      | (simp [eisSummand, hk2])
      | (unfold eisSummand; done)
  calc PI.eisG (PI.lat2 a (a * τ)) k
      = ∑' w : {w : ℂ // w ∈ PI.lat2 a (a * τ) ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k) := rfl
    _ = ∑' v : nz, 1 / ((e v : ℂ)) ^ (2 * k) :=
        (e.tsum_eq (fun w : {w : ℂ // w ∈ PI.lat2 a (a * τ) ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k))).symm
    _ = ∑' v : nz, (a ^ (2 * k))⁻¹ * eisSummand ((2 * k : ℕ) : ℤ) v.1 τ :=
        tsum_congr hterm
    _ = (a ^ (2 * k))⁻¹ * ∑' v : nz, eisSummand ((2 * k : ℕ) : ℤ) v.1 τ :=
        tsum_mul_left
    _ = (a ^ (2 * k))⁻¹ * ∑' v : Fin 2 → ℤ, eisSummand ((2 * k : ℕ) : ℤ) v τ := by
        rw [tsum_subtype_eq_of_support_subset
          (f := fun v : Fin 2 → ℤ => eisSummand ((2 * k : ℕ) : ℤ) v τ) hsupp]

end DiscrNeWork

end
