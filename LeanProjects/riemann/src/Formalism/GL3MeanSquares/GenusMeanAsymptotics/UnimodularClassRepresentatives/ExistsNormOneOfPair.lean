import Mathlib

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

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
  obtain ⟨θ, hθ, hu0, -, hui⟩ := hS.unram
  refine ⟨s * θ * (θ - star θ)⁻¹, S.mul_mem (S.mul_mem hs hθ) hui, ?_⟩
  have hst : star (θ - star θ) = -(θ - star θ) := by
    rw [star_sub, star_star]
    ring
  have hn : -(θ - star θ) ≠ 0 := neg_ne_zero.mpr hu0
  rw [star_mul, star_mul, star_inv₀, hst, hss]
  field_simp
  try ring

theorem exists_norm_one_mul_mem (hS : IsHermSemilocal S) {a : K} (ha : star a * a ∈ S) :
    ∃ b : K, star b * b = 1 ∧ a * b ∈ S := by
  let A : AddSubgroup K :=
    { carrier := {w | ∃ x ∈ S, ∃ y ∈ S, w = x + y * a}
      add_mem' := by
        rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
        exact ⟨x + x', S.add_mem hx hx', y + y', S.add_mem hy hy', by ring⟩
      zero_mem' := ⟨0, S.zero_mem, 0, S.zero_mem, by ring⟩
      neg_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        exact ⟨-x, S.neg_mem hx, -y, S.neg_mem hy, by ring⟩ }
  have hmem : ∀ w, w ∈ A ↔ ∃ x ∈ S, ∃ y ∈ S, w = x + y * a := fun w => Iff.rfl
  have h1 : ∀ s ∈ S, ∀ w ∈ A, s * w ∈ A := by
    intro s hs w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := (hmem w).1 hw
    exact (hmem _).2 ⟨s * x, S.mul_mem hs hx, s * y, S.mul_mem hs hy, by ring⟩
  have h2 : ∃ w ∈ A, w ≠ 0 := ⟨1, (hmem 1).2 ⟨1, S.one_mem, 0, S.zero_mem, by ring⟩, one_ne_zero⟩
  obtain ⟨t, ht, ht0, hta⟩ := hS.frac a
  have h3 : ∃ t : K, t ≠ 0 ∧ ∀ w ∈ A, t * w ∈ S := by
    refine ⟨t, ht0, fun w hw => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := (hmem w).1 hw
    have e : t * (x + y * a) = t * x + y * (t * a) := by ring
    rw [e]
    exact S.add_mem (S.mul_mem ht hx) (S.mul_mem hy hta)
  obtain ⟨α, hαA, hα0, hαdiv⟩ := hS.principal A h1 h2 h3
  have h1inv : 1 * α⁻¹ ∈ S := hαdiv 1 ((hmem 1).2 ⟨1, S.one_mem, 0, S.zero_mem, by ring⟩)
  have haα : a * α⁻¹ ∈ S := hαdiv a ((hmem a).2 ⟨0, S.zero_mem, 1, S.one_mem, by ring⟩)
  obtain ⟨x, hx, y, hy, hαxy⟩ := (hmem α).1 hαA
  have hsα0 : star α ≠ 0 := star_ne_zero.mpr hα0
  have hsα : star α = star x + star a * star y := by
    rw [hαxy, star_add, star_mul]
  refine ⟨star α / α, ?_, ?_⟩
  · rw [star_div₀, star_star, div_mul_div_comm, mul_comm α (star α), div_self (mul_ne_zero hsα0 hα0)]
  · have e : a * (star α / α) = star x * (a * α⁻¹) + star y * (star a * a) * (1 * α⁻¹) := by
      rw [hsα]
      field_simp
      try ring
    rw [e]
    exact S.add_mem (S.mul_mem (hS.star_mem x hx) haα)
      (S.mul_mem (S.mul_mem (hS.star_mem y hy) ha) h1inv)

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

end Formalism.HermitianLattices.Ext.L3.WA
