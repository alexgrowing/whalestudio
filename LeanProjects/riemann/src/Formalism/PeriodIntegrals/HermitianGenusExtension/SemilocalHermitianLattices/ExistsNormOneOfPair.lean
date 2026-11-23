import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3.WA

variable {K : Type*} [Field K] [StarRing K]

def IsUnitIn (S : Subring K) (a : K) : Prop := a ≠ 0 ∧ a ∈ S ∧ a⁻¹ ∈ S

structure IsHermSemilocal (S : Subring K) : Prop where
  star_mem : ∀ a ∈ S, star a ∈ S
  frac : ∀ a : K, ∃ t ∈ S, t ≠ 0 ∧ t * a ∈ S
  unram : ∃ θ ∈ S, IsUnitIn S (θ - star θ)
  principal : ∀ A : AddSubgroup K, (∀ s ∈ S, ∀ a ∈ A, s * a ∈ A) → (∃ a ∈ A, a ≠ 0) →
    (∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S) → ∃ α ∈ A, α ≠ 0 ∧ ∀ a ∈ A, a * α⁻¹ ∈ S
  unit_or : ∀ a ∈ S, ∀ κ ∈ S, ∀ μ : K, a⁻¹ ∉ S → IsUnitIn S μ →
    IsUnitIn S (1 - κ * a) ∨ IsUnitIn S (1 - (κ + μ) * a)

variable {S : Subring K}

theorem exists_trace_eq (hS : IsHermSemilocal S) {s : K} (hs : s ∈ S) (hss : star s = s) :
    ∃ c ∈ S, c + star c = s := by
  obtain ⟨θ, hθ, hμ0, -, hμi⟩ := hS.unram
  refine ⟨s * θ * (θ - star θ)⁻¹, S.mul_mem (S.mul_mem hs hθ) hμi, ?_⟩
  have h2 : star θ - θ ≠ 0 := by
    intro h
    apply hμ0
    rw [← neg_sub, h, neg_zero]
  simp only [star_mul', star_inv₀, star_sub, star_star, hss]
  have h3 : (star θ - θ)⁻¹ = -(θ - star θ)⁻¹ := by
    rw [← neg_sub, neg_inv]
  rw [h3]
  field_simp
  ring

theorem exists_norm_one_mul_mem (hS : IsHermSemilocal S) {a : K} (ha : star a * a ∈ S) :
    ∃ b : K, star b * b = 1 ∧ a * b ∈ S := by
  let A : AddSubgroup K :=
    { carrier := {z | ∃ x ∈ S, ∃ y ∈ S, z = x + y * a}
      zero_mem' := ⟨0, S.zero_mem, 0, S.zero_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
        exact ⟨x + x', S.add_mem hx hx', y + y', S.add_mem hy hy', by ring⟩
      neg_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        exact ⟨-x, S.neg_mem hx, -y, S.neg_mem hy, by ring⟩ }
  have h1A : (1 : K) ∈ A := ⟨1, S.one_mem, 0, S.zero_mem, by simp⟩
  have haA : a ∈ A := ⟨0, S.zero_mem, 1, S.one_mem, by simp⟩
  have hAS : ∀ s ∈ S, ∀ z ∈ A, s * z ∈ A := by
    rintro s hs _ ⟨x, hx, y, hy, rfl⟩
    exact ⟨s * x, S.mul_mem hs hx, s * y, S.mul_mem hs hy, by ring⟩
  obtain ⟨t, htS, ht0, hta⟩ := hS.frac a
  have htA : ∀ z ∈ A, t * z ∈ S := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have : t * (x + y * a) = t * x + y * (t * a) := by ring
    rw [this]
    exact S.add_mem (S.mul_mem htS hx) (S.mul_mem hy hta)
  obtain ⟨δ, ⟨x, hx, y, hy, hδ⟩, hδ0, hdiv⟩ :=
    hS.principal A hAS ⟨1, h1A, one_ne_zero⟩ ⟨t, ht0, htA⟩
  have hsS : δ⁻¹ ∈ S := by simpa using hdiv 1 h1A
  have hrS : a * δ⁻¹ ∈ S := hdiv a haA
  generalize hsdef : δ⁻¹ = s at hsS hrS
  have hs0 : s ≠ 0 := by rw [← hsdef]; exact inv_ne_zero hδ0
  have h1 : x * s + y * (a * s) = 1 := by
    rw [← mul_assoc, ← add_mul, ← hδ, ← hsdef]
    exact mul_inv_cancel₀ hδ0
  have hss0 : star s ≠ 0 := star_ne_zero.mpr hs0
  refine ⟨s / star s, ?_, ?_⟩
  · rw [star_div₀, star_star]
    field_simp
  · have hq : (x * star (a * s) + y * (star a * a) * star s) * s = star (a * s) := by
      calc (x * star (a * s) + y * (star a * a) * star s) * s
          = star (a * s) * (x * s + y * (a * s)) := by rw [star_mul']; ring
        _ = star (a * s) := by rw [h1, mul_one]
    have : a * (s / star s) = star (x * star (a * s) + y * (star a * a) * star s) := by
      rw [← mul_div_assoc, div_eq_iff hss0, ← star_mul', hq, star_star]
    rw [this]
    exact hS.star_mem _ (S.add_mem (S.mul_mem hx (hS.star_mem _ hrS))
      (S.mul_mem (S.mul_mem hy ha) (hS.star_mem _ hsS)))

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_norm_one_of_pair (hS : IsHermSemilocal S) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {y w : V} {a : K} (ha : a ∈ S) (ha0 : a ≠ 0) (hy : h y y = star a * a) (hyw : h y w = 1)
    (hw : h w w ∈ S) :
    ∃ c ∈ S, ∃ d ∈ S, h (c • w + d • y) (c • w + d • y) = 1 := by
  have hwy : h w y = 1 := by
    have := hs.eq y w
    rw [hyw, map_one] at this
    exact this.symm
  have hH : star (h w w) = h w w := hs.eq w w
  have key : ∀ c d : K, h (c • w + d • y) (c • w + d • y) =
      star c * c * h w w + star c * d + star d * c + star d * d * (star a * a) := by
    intro c d
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hy, hyw, hwy, starRingEnd_apply, RingHom.id_apply]
    ring
  by_cases hu : a⁻¹ ∈ S
  · refine ⟨0, S.zero_mem, a⁻¹, hu, ?_⟩
    have hsa : star a ≠ 0 := star_ne_zero.mpr ha0
    rw [key, star_inv₀]
    field_simp
    simp
  · obtain ⟨θ, hθ, hμ⟩ := hS.unram
    have h1a : 1 + a ∈ S := S.add_mem S.one_mem ha
    obtain ⟨κ, hκ, hκt⟩ : ∃ κ ∈ S, κ + star κ = star (1 + a) * (1 + a) * h w w - 1 := by
      apply exists_trace_eq hS
      · exact S.sub_mem (S.mul_mem (S.mul_mem (hS.star_mem _ h1a) h1a) hw) S.one_mem
      · simp only [star_sub, star_mul', star_star, hH, star_one]
        ring
    have fin : ∀ κ' ∈ S, κ' + star κ' = star (1 + a) * (1 + a) * h w w - 1 →
        IsUnitIn S (1 - κ' * a) →
        ∃ c ∈ S, ∃ d ∈ S, h (c • w + d • y) (c • w + d • y) = 1 := by
      rintro κ' hκ' ht ⟨h0, -, h2⟩
      refine ⟨star (1 + a) * (1 - κ' * a)⁻¹, S.mul_mem (hS.star_mem _ h1a) h2,
        -κ' * (1 - κ' * a)⁻¹, S.mul_mem (S.neg_mem hκ') h2, ?_⟩
      have h0' : star (1 - κ' * a) ≠ 0 := star_ne_zero.mpr h0
      have hb : star (1 + a) * (1 + a) * h w w = κ' + star κ' + 1 := by rw [ht]; ring
      rw [key]
      have e : star (star (1 + a) * (1 - κ' * a)⁻¹) * (star (1 + a) * (1 - κ' * a)⁻¹) * h w w +
          star (star (1 + a) * (1 - κ' * a)⁻¹) * (-κ' * (1 - κ' * a)⁻¹) +
          star (-κ' * (1 - κ' * a)⁻¹) * (star (1 + a) * (1 - κ' * a)⁻¹) +
          star (-κ' * (1 - κ' * a)⁻¹) * (-κ' * (1 - κ' * a)⁻¹) * (star a * a) =
          (star (1 - κ' * a))⁻¹ * (1 - κ' * a)⁻¹ * (star (1 + a) * (1 + a) * h w w
            - (1 + a) * κ' - star κ' * star (1 + a) + star κ' * κ' * (star a * a)) := by
        simp only [star_mul', star_inv₀, star_star, star_neg]
        ring
      rw [e, hb]
      have e2 : κ' + star κ' + 1 - (1 + a) * κ' - star κ' * star (1 + a) +
          star κ' * κ' * (star a * a) = star (1 - κ' * a) * (1 - κ' * a) := by
        simp only [star_sub, star_add, star_mul', star_one]
        ring
      rw [e2]
      field_simp
    rcases hS.unit_or a ha κ hκ (θ - star θ) hu hμ with h1 | h1
    · exact fin κ hκ hκt h1
    · refine fin (κ + (θ - star θ)) (S.add_mem hκ hμ.2.1) ?_ h1
      rw [← hκt]
      simp only [star_add, star_sub, star_star]
      ring

end ReciprocityTheory.ChartRestriction.L3.WA
