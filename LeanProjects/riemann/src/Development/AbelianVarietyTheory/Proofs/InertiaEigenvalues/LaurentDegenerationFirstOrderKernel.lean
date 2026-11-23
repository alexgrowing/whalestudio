import Mathlib
open Polynomial

namespace GlobalTheory

theorem laurent_degeneration_abstract (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (σ : K)
    (O : K → Prop) (π0 π1 : K →ₗ[k] k) (h0 : ∀ z, O z → π0 (σ * z) = 0)
    (h1 : ∀ z, π1 (σ * z) = π0 z) (hone : π0 1 = 1)
    (hnorm : ∀ (a : ℕ) (y : Fin a → K), y ≠ 0 → ∃ (f : K) (c0 : Fin a), f * y c0 = 1 ∧ ∀ c, O (f * y c))
    (a e : ℕ) (V : Submodule k (Fin a → k)) (U : Type) [AddCommGroup U] [Module k U]
    (t u : V →ₗ[k] U) (he : e ≤ 1)
    (H : ∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) →
      ¬ LinearIndependent k x0)
    (y : Fin (e + 1) → Fin a → K)
    (hy : ∀ j (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (y j c)) ∧
      (∀ c, x'.1 c = π (σ * y j c)) ∧ t x = u x') :
    ¬ LinearIndependent K y := by
  let P : (Fin a → K) → Prop := fun z => ∀ (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (z c)) ∧
      (∀ c, x'.1 c = π (σ * z c)) ∧ t x = u x'
  have Psmul : ∀ (f : K) z, P z → P (f • z) := by
    intro f z hz π
    obtain ⟨x, x', h, h', h''⟩ := hz (π ∘ₗ LinearMap.mulLeft k f)
    refine ⟨x, x', fun c => by simpa using h c, fun c => ?_, h''⟩
    rw [h' c]
    simp [mul_left_comm]
  have Psub : ∀ z w, P z → P w → P (z - w) := by
    intro z w hz hw π
    obtain ⟨x, x', h, h', h''⟩ := hz π
    obtain ⟨v, v', g, g', g''⟩ := hw π
    refine ⟨x - v, x' - v', fun c => by simp [h c, g c], fun c => by simp [h' c, g' c, mul_sub],
      by simp [h'', g'']⟩
  have key : ∀ z, P z → z ≠ 0 → ∃ (f : K) (c0 : Fin a) (x0 x1 : V), f * z c0 = 1 ∧
      (∀ c, x0.1 c = π0 (f * z c)) ∧ t x0 = 0 ∧ t x1 = u x0 := by
    intro z hz hz0
    obtain ⟨f, c0, hf, hO⟩ := hnorm a z hz0
    have hP := Psmul f z hz
    obtain ⟨x, x', h, h', h''⟩ := hP π0
    obtain ⟨v, v', g, g', g''⟩ := hP π1
    have hx' : x' = 0 := by
      ext c
      rw [h' c]
      simpa using h0 _ (hO c)
    have hv' : v' = x := by
      ext c
      rw [g' c, h c, h1]
    refine ⟨f, c0, x, v, hf, fun c => by simpa using h c, by rw [h'', hx', map_zero],
      by rw [g'', hv']⟩
  intro hli
  obtain rfl | rfl : e = 0 ∨ e = 1 := by omega
  · obtain ⟨f, c0, x0, x1, hf, hx, ht, ht'⟩ := key (y 0) (hy 0) (hli.ne_zero 0)
    refine H (fun _ => x0) (fun _ => x1) (fun _ => ⟨ht, ht'⟩) ?_
    have hne : x0 ≠ 0 := by
      intro h
      have := hx c0
      rw [h, hf, hone] at this
      simp at this
    exact (linearIndependent_unique_iff (ι := Fin 1) (v := fun _ => x0)).2 hne
  · obtain ⟨f, c0, x0, x1, hf, hx, ht, ht'⟩ := key (y 0) (hy 0) (hli.ne_zero 0)
    have hw : y 1 - (y 1 c0 * f) • y 0 ≠ 0 := by
      intro h
      have hy2 : y = ![y 0, y 1] := by
        ext i : 1
        fin_cases i <;> rfl
      rw [hy2, LinearIndependent.pair_iff] at hli
      have := (hli (-(y 1 c0 * f)) 1 (by rw [← h]; simp [sub_eq_neg_add])).2
      exact one_ne_zero this
    obtain ⟨g, c1, z0, z1, hg, hz, hs, hs'⟩ :=
      key _ (Psub _ _ (hy 1) (Psmul (y 1 c0 * f) _ (hy 0))) hw
    have e1 : x0.1 c0 = 1 := by rw [hx, hf, hone]
    have e2 : z0.1 c0 = 0 := by
      rw [hz]
      simp [mul_assoc, hf]
    have e3 : z0.1 c1 = 1 := by rw [hz, hg, hone]
    refine H ![x0, z0] ![x1, z1] (fun j => by fin_cases j <;> simp [ht, ht', hs, hs']) ?_
    rw [LinearIndependent.pair_iff]
    intro s r h
    have a0 := congrArg (fun v : V => v.1 c0) h
    have a1 := congrArg (fun v : V => v.1 c1) h
    simp [e1, e2] at a0
    simp [a0, e3] at a1
    exact ⟨a0, a1⟩

theorem laurent_vector_normalise (k : Type) [Field k] (a : ℕ) (y : Fin a → HahnSeries ℤ k)
    (hy : y ≠ 0) : ∃ (f : HahnSeries ℤ k) (c0 : Fin a), f * y c0 = 1 ∧
      ∀ c, (f * y c).coeff (-1) = 0 := by
  classical
  have hne : (Finset.univ.filter fun c => y c ≠ 0).Nonempty := by
    obtain ⟨c, hc⟩ := Function.ne_iff.1 hy
    exact ⟨c, by simpa using hc⟩
  obtain ⟨c0, hc0, hmin⟩ := Finset.exists_min_image _ (fun c => (y c).order) hne
  have h0 : y c0 ≠ 0 := by simpa using hc0
  refine ⟨(y c0)⁻¹, c0, inv_mul_cancel₀ h0, fun c => ?_⟩
  by_cases hc : y c = 0
  · simp [hc]
  · have h1 := hmin c (by simpa using hc)
    have h2 := HahnSeries.order_mul (inv_ne_zero h0) h0
    rw [inv_mul_cancel₀ h0, HahnSeries.order_one] at h2
    apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [HahnSeries.order_mul (inv_ne_zero h0) hc]
    omega

noncomputable def laurentCoeffForm (k : Type) [Field k] (n : ℤ) :
    letI : Algebra k (HahnSeries ℤ k) := HahnSeries.instAlgebra
    HahnSeries ℤ k →ₗ[k] k :=
  HahnSeries.coeff.linearMap n

theorem laurent_degeneration : ∀ (k : Type) [Field k], ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ : K), ∀ (a e : ℕ) (V : Submodule k (Fin a → k)) (U : Type) [AddCommGroup U] [Module k U] (t u : V →ₗ[k] U), e ≤ 1 → (∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → ∀ y : Fin (e + 1) → Fin a → K, (∀ j (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (y j c)) ∧ (∀ c, x'.1 c = π (σ * y j c)) ∧ t x = u x') → ¬ LinearIndependent K y := by
  intro k _
  letI : Algebra k (HahnSeries ℤ k) := HahnSeries.instAlgebra
  refine ⟨HahnSeries ℤ k, inferInstance, this, HahnSeries.single 1 1, ?_⟩
  intro a e V U _ _ t u
  have hs : ∀ (z : HahnSeries ℤ k) (n : ℤ),
      (HahnSeries.single (1 : ℤ) (1 : k) * z).coeff (n + 1) = z.coeff n := by
    intro z n
    rw [HahnSeries.coeff_single_mul_add, one_mul]
  refine laurent_degeneration_abstract k (HahnSeries ℤ k) (HahnSeries.single 1 1)
    (fun z => z.coeff (-1) = 0) (laurentCoeffForm k 0) (laurentCoeffForm k 1) ?_ ?_ ?_
    (laurent_vector_normalise k) a e V U t u
  · intro z hz
    exact (hs z (-1)).trans hz
  · intro z
    exact hs z 0
  · show (1 : HahnSeries ℤ k).coeff 0 = 1
    simp

end GlobalTheory
