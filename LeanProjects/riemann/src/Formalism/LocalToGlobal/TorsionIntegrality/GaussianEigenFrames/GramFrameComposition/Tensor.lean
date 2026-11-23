import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementG

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.GD

theorem sum_sum_prod_two {K : Type} [CommRing K] {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]
    (A : J₁ → J₁ → K) (B : J₂ → J₂ → K) :
    ∑ j : J₁ × J₂, ∑ k : J₁ × J₂, A j.1 k.1 * B j.2 k.2 =
      (∑ a, ∑ a', A a a') * (∑ l, ∑ l', B l l') := by
  simp only [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul]

theorem sum_sum_prod_three {K : Type} [CommRing K] {J₁ J₂ J₃ : Type} [Fintype J₁] [Fintype J₂] [Fintype J₃]
    (A : J₁ → J₁ → K) (B : J₂ → J₂ → K) (C : J₃ → J₃ → K) :
    ∑ j : J₁ × J₂ × J₃, ∑ k : J₁ × J₂ × J₃, A j.1 k.1 * (B j.2.1 k.2.1 * C j.2.2 k.2.2) =
      (∑ a, ∑ a', A a a') * ((∑ l, ∑ l', B l l') * (∑ r, ∑ r', C r r')) := by
  rw [sum_sum_prod_two A (fun j k : J₂ × J₃ => B j.1 k.1 * C j.2 k.2), sum_sum_prod_two B C]

theorem tripleTensorAlmostOrthonormal : TensorBlock := by
  intro K _ _ E _ H _ _ emb Ja Jl Jr _ _ _ hA hl hr N0 N1 Gc P P' th u hth hvan hu hun hL hR t ab ab'
  obtain ⟨a, b⟩ := ab
  obtain ⟨a', b'⟩ := ab'
  obtain ⟨e₁, he₁, hE₁⟩ := hL t a a'
  obtain ⟨e₂, he₂, hE₂⟩ := hR t b b'

  have hsep : ∑ j : Ja × Jl × Jr, ∑ k : Ja × Jl × Jr,
        (Gc (false, t) j.1 * P (false, t) j.2.1 a * P' (false, t) j.2.2 b) *
          (∑ ρ : Bool × H, emb ρ (hA j.1 k.1 * hl j.2.1 k.2.1 * hr j.2.2 k.2.2)) *
          (Gc (true, t) k.1 * P (true, t) k.2.1 a' * P' (true, t) k.2.2 b') =
      ∑ ρ : Bool × H, (∑ α, ∑ α', Gc (false, t) α * emb ρ (hA α α') * Gc (true, t) α') *
        ((∑ l, ∑ l₂, P (false, t) l a * emb ρ (hl l l₂) * P (true, t) l₂ a') *
          (∑ r, ∑ r₂, P' (false, t) r b * emb ρ (hr r r₂) * P' (true, t) r₂ b')) := by
    simp_rw [← sum_sum_prod_three]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [map_mul, map_mul]
    ring
  have hzero : ∀ ρ : Bool × H, ρ ≠ (false, t) →
      ∑ α, ∑ α', Gc (false, t) α * emb ρ (hA α α') * Gc (true, t) α' = 0 := by
    intro ρ hρ
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun α' _ => ?_
    rw [← Finset.sum_mul, hvan (false, t) ρ hρ α', zero_mul]
  have hsingle : ∑ ρ : Bool × H, (∑ α, ∑ α', Gc (false, t) α * emb ρ (hA α α') * Gc (true, t) α') *
        ((∑ l, ∑ l₂, P (false, t) l a * emb ρ (hl l l₂) * P (true, t) l₂ a') *
          (∑ r, ∑ r₂, P' (false, t) r b * emb ρ (hr r r₂) * P' (true, t) r₂ b')) =
      u t * ((((if a = a' then 1 else 0) + th * e₁)) * ((if b = b' then 1 else 0) + th * e₂)) := by
    rw [Finset.sum_eq_single (false, t) (fun ρ _ hρ => by rw [hzero ρ hρ, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), ← hu t, hE₁, hE₂]
  have hda : ‖(if a = a' then (1 : K) else 0)‖ ≤ 1 := by split_ifs <;> simp
  have hdb : ‖(if b = b' then (1 : K) else 0)‖ ≤ 1 := by split_ifs <;> simp
  have mul1 : ∀ x y : K, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x * y‖ ≤ 1 := by
    intro x y hx hy
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  have add1 : ∀ x y : K, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x + y‖ ≤ 1 := by
    intro x y hx hy
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  refine ⟨u t * ((if a = a' then (1 : K) else 0) * e₂ + e₁ * (if b = b' then (1 : K) else 0) + th * (e₁ * e₂)), ?_, ?_⟩
  · exact mul1 _ _ (hun t) (add1 _ _ (add1 _ _ (mul1 _ _ hda he₂) (mul1 _ _ he₁ hdb))
      (mul1 _ _ hth (mul1 _ _ he₁ he₂)))
  · show ∑ j : Ja × Jl × Jr, ∑ k : Ja × Jl × Jr,
        (Gc (false, t) j.1 * P (false, t) j.2.1 a * P' (false, t) j.2.2 b) *
          (∑ ρ : Bool × H, emb ρ (hA j.1 k.1 * hl j.2.1 k.2.1 * hr j.2.2 k.2.2)) *
          (Gc (true, t) k.1 * P (true, t) k.2.1 a' * P' (true, t) k.2.2 b') = _
    rw [hsep, hsingle]
    have hif : (if (a, b) = (a', b') then u t else 0) =
        u t * ((if a = a' then (1 : K) else 0) * (if b = b' then (1 : K) else 0)) := by
      by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> simp [Prod.mk.injEq, h1, h2]
    rw [hif]
    ring

end Formalism.L2.Th1.GD
