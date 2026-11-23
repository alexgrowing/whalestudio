import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast

noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.DegCnt
open scoped Pointwise nonZeroDivisors

namespace GlobalTheory.RowStab

section Gen
variable {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def gen (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) : V →ₗ[K] V :=
  LinearMap.id + ∑ b ∈ J, ((H.B.flip (e b)).smulRight (ρ b) - (H.B.flip (ρ b)).smulRight (e b) +
    ∑ a ∈ J, (c a b • H.B.flip (e b)).smulRight (e a))

theorem gen_apply (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) (v : V) :
    gen H J e ρ c v = v + ∑ b ∈ J, (H.B v (e b) • ρ b - H.B v (ρ b) • e b +
      ∑ a ∈ J, (c a b * H.B v (e b)) • e a) := by
  simp [gen, LinearMap.sum_apply, mul_smul]

end Gen

section Ideal
variable {K : Type} [Field K] [NumberField K]

theorem ipow_mul_mem {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m n : ℤ} {x y : K} (hx : x ∈ ipow 𝔡 m)
    (hy : y ∈ ipow 𝔡 n) : x * y ∈ ipow 𝔡 (m + n) := by
  have h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
    simpa using h𝔡
  unfold ipow at *
  rw [zpow_add₀ h0, FractionalIdeal.coe_mul]
  exact Submodule.mul_mem_mul hx hy

theorem one_mem_ipow_mul {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) (m : ℤ) :
    (1 : K) ∈ ipow 𝔡 m * ipow 𝔡 (-m) := by
  have h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
    simpa using h𝔡
  unfold ipow
  rw [← FractionalIdeal.coe_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, FractionalIdeal.coe_one]
  exact Submodule.one_le.mp le_rfl

theorem ipow_zero (𝔡 : Ideal (𝓞 K)) : ipow 𝔡 0 = 1 := by
  simp [ipow]

theorem mem_ipow_of_mul {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m n : ℤ} {x : K}
    (h : ∀ t ∈ ipow 𝔡 (-m), t * x ∈ ipow 𝔡 n) : x ∈ ipow 𝔡 (m + n) := by
  have key : ∀ y ∈ ipow 𝔡 m * ipow 𝔡 (-m), y * x ∈ ipow 𝔡 (m + n) := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha t ht
      rw [mul_assoc]
      exact ipow_mul_mem h𝔡 ha (h t ht)
    · intro a b ha hb
      rw [add_mul]
      exact Submodule.add_mem _ ha hb
  simpa using key 1 (one_mem_ipow_mul h𝔡 m)

end Ideal

section Smul
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem smul_mem_of_mem_ipow_smul {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m : ℤ} {M : Submodule (𝓞 K) V} {v : V}
    (hv : v ∈ ipow 𝔡 m • M) {t : K} (ht : t ∈ ipow 𝔡 (-m)) : t • v ∈ M := by
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro a ha n hn
    have h1 : t * a ∈ ipow 𝔡 0 := by
      simpa [add_comm] using ipow_mul_mem h𝔡 ht ha
    rw [ipow_zero] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.mp h1
    rw [smul_smul, ← ho, algebraMap_smul]
    exact M.smul_mem o hn
  · intro x y hx hy
    rw [smul_add]
    exact M.add_mem hx hy

theorem mem_ipow_smul_of_smul_mem {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m : ℤ} {M : Submodule (𝓞 K) V} {v : V}
    (h : ∀ t ∈ ipow 𝔡 (-m), t • v ∈ M) : v ∈ ipow 𝔡 m • M := by
  have key : ∀ y ∈ ipow 𝔡 m * ipow 𝔡 (-m), y • v ∈ ipow 𝔡 m • M := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha t ht
      rw [mul_smul]
      exact Submodule.smul_mem_smul ha (h t ht)
    · intro a b ha hb
      rw [add_smul]
      exact Submodule.add_mem _ ha hb
  simpa using key 1 (one_mem_ipow_mul h𝔡 m)

end Smul

section Star
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem star_integral (y : 𝓞 K) : ∃ y' : 𝓞 K, (y' : K) = star (y : K) := by
  have h : IsIntegral ℤ (star (y : K)) := by
    exact (RingOfIntegers.isIntegral_coe y).map ((starRingEnd K).toIntAlgHom)
  exact ⟨⟨star (y : K), h⟩, rfl⟩

theorem star_pow_mem {𝔡 : Ideal (𝓞 K)} (h𝔡s : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (k : ℕ) :
    ∀ x ∈ 𝔡 ^ k, ∃ y ∈ 𝔡 ^ k, (y : K) = star (x : K) := by
  induction k with
  | zero =>
    intro x _
    obtain ⟨y, hy⟩ := star_integral x
    exact ⟨y, by simp, hy⟩
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨a', ha', ea⟩ := ih a ha
      obtain ⟨b', hb', eb⟩ := h𝔡s b hb
      refine ⟨a' * b', ?_, ?_⟩
      · rw [pow_succ]; exact Submodule.mul_mem_mul ha' hb'
      · simp [ea, eb, star_mul']
    · rintro a b ⟨a', ha', ea⟩ ⟨b', hb', eb⟩
      exact ⟨a' + b', Submodule.add_mem _ ha' hb', by simp [ea, eb]⟩

theorem star_mem_one {x : K} (hx : x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    star x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.mem_one_iff] at *
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y', hy'⟩ := star_integral y
  exact ⟨y', hy'⟩

theorem star_mem_ipow {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥)
    (h𝔡s : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℤ) {x : K} (hx : x ∈ ipow 𝔡 n) :
    star x ∈ ipow 𝔡 n := by
  have hA : ∀ k : ℕ, ∀ x : K, x ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ k) →
      star x ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ k) := by
    intro k x hx
    rw [← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coeIdeal] at *
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', e⟩ := star_pow_mem h𝔡s k y hy
    exact ⟨y', hy', e⟩
  unfold ipow at *
  rw [FractionalIdeal.mem_coe] at *
  rcases n with k | k
  · simp only [Int.ofNat_eq_coe, zpow_natCast] at *
    exact hA k x hx
  · have h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ^ (k + 1) ≠ 0 := by
      apply pow_ne_zero; simpa using h𝔡
    rw [zpow_negSucc, FractionalIdeal.mem_inv_iff h0] at *
    intro y hy
    have := star_mem_one (hx (star y) (hA _ y hy))
    simpa [star_mul', mul_comm] using this

end Star

end GlobalTheory.RowStab
