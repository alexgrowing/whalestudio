import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory

theorem finsupp_coord_ideal_eq_top {R : Type} [CommRing R] (u : ℕ →₀ R) (g : (ℕ →₀ R) →ₗ[R] R)
    (hg : g u = 1) (K : Ideal R) (hK : ∀ i, u i ∈ K) : K = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← hg]
  rw [show g u = g (u.sum Finsupp.single) by rw [Finsupp.sum_single]]
  rw [Finsupp.sum, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (hK i)

theorem finsupp_exists_form_of_span {R : Type} [CommRing R] (u : ℕ →₀ R)
    (h : Ideal.span (Set.range fun i => u i) = ⊤) : ∃ g : (ℕ →₀ R) →ₗ[R] R, g u = 1 := by
  have h1 : (1 : R) ∈ Ideal.span (Set.range fun i => u i) := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h1
  refine ⟨∑ i ∈ c.support, c i • Finsupp.lapply i, ?_⟩
  rw [← hc]
  simp [Finsupp.sum, LinearMap.sum_apply]

private theorem linearMap_apply_mem_span_range_coeffs {R : Type} [CommRing R] (w : ℕ →₀ R)
    (g : (ℕ →₀ R) →ₗ[R] R) : g w ∈ Ideal.span (Set.range fun i => w i) := by
  have e : g w = ∑ i ∈ w.support, w i * g (Finsupp.single i 1) := by
    conv_lhs => rw [← Finsupp.sum_single w]
    rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
  rw [e]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem unimodular_partner_aff : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n j : ℕ), s ≤ n →
    n ≤ j → ∀ v : ℕ →₀ R, [v] ∈ uniM R (ℕ →₀ R) → ∃ x ∈ aff R n j, [v, x] ∈ uniM R (ℕ →₀ R) := by
  intro R _ s hs n j hsn hnj v hv
  obtain ⟨f, hf⟩ := hv
  obtain ⟨f0, hf0⟩ : ∃ f0 : (ℕ →₀ R) →ₗ[R] R, f0 v = 1 :=
    ⟨f ⟨0, by simp⟩, by simpa using hf ⟨0, by simp⟩ ⟨0, by simp⟩⟩
  let a : ℕ → R := fun i => f0 (Finsupp.single i 1)
  let φ : (ℕ →₀ R) →ₗ[R] R :=
    f0 - ∑ i ∈ Finset.range n, a i • Finsupp.lapply i - a j • Finsupp.lapply j
  have hφ : ∀ w, φ w = f0 w - ∑ i ∈ Finset.range n, a i * w i - a j * w j := by
    intro w
    simp [φ, LinearMap.sum_apply]
  have hφs : ∀ k c, k < n → φ (Finsupp.single k c) = 0 := by
    intro k c hk
    have h1 : f0 (Finsupp.single k c) = c * a k := by
      rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
    rw [hφ, h1, Finset.sum_eq_single k
      (fun b _ hb => by simp [Finsupp.single_apply, Ne.symm hb])
      (fun h => absurd (Finset.mem_range.2 hk) h)]
    simp only [Finsupp.single_eq_same, Finsupp.single_apply, if_neg (show k ≠ j by omega), mul_zero,
      sub_zero]
    ring
  have hφj : φ (Finsupp.single j 1) = 0 := by
    rw [hφ, Finset.sum_eq_zero (fun i hi => by
      have := Finset.mem_range.1 hi
      simp [Finsupp.single_apply, show j ≠ i by omega])]
    simp [a]
  let b' : R := φ v + a j * v j
  let r : Fin (n + 1) → R := fun i => if (i : ℕ) < n then v i else b'
  have hrc : ∀ i : Fin n, r i.castSucc = v i := fun i => by simp [r, i.isLt]
  have hrl : r (Fin.last n) = b' := by simp [r]
  have hr : Unimodular R r := by
    show Ideal.span (Set.range r) = ⊤
    rw [Ideal.eq_top_iff_one]
    have key : (1 : R) = ∑ i : Fin n, a i * r i.castSucc + 1 * r (Fin.last n) := by
      simp only [hrc, hrl, one_mul, b']
      rw [hφ, ← hf0, ← Finset.sum_range (fun i => a i * v i)]
      ring
    rw [key]
    exact Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨t, ht⟩ := hs n hsn r hr
  have ht' : Ideal.span (Set.range fun i => r i.castSucc + t i * r (Fin.last n)) = ⊤ := ht
  let y : ℕ →₀ R := ∑ i : Fin n, Finsupp.single (i : ℕ) (-(t i * a j))
  have hy0 : ∀ m, n ≤ m → y m = 0 := by
    intro m hm
    simp only [y, Finsupp.finset_sum_apply]
    exact Finset.sum_eq_zero fun i _ => by
      have := i.isLt
      simp [Finsupp.single_apply, show (i : ℕ) ≠ m by omega]
  have hyi : ∀ i : Fin n, y i = -(t i * a j) := by
    intro i
    simp only [y, Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, Fin.val_ne_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  let x : ℕ →₀ R := Finsupp.single j 1 + y
  have hxj : x j = 1 := by simp [x, hy0 j hnj]
  have hxaff : x ∈ aff R n j := by
    simp only [aff, low, Set.mem_setOf_eq]
    intro m hm
    simp [x, hy0 m hm]
  have hφx : φ x = 0 := by
    simp only [x, map_add, hφj, zero_add, y, map_sum]
    exact Finset.sum_eq_zero fun i _ => hφs _ _ i.isLt
  let v' : ℕ →₀ R := v - v j • x
  have hv'i : ∀ i : Fin n, v' i = v i + v j * (t i * a j) := by
    intro i
    simp only [v', x, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply, hyi,
      Finsupp.single_apply, if_neg (show j ≠ (i : ℕ) by have := i.isLt; omega)]
    ring
  have hφv' : φ v' = φ v := by simp [v', hφx]
  have hspan : Ideal.span (Set.range fun i => v' i) = ⊤ := by
    rw [eq_top_iff, ← ht', Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have he : r i.castSucc + t i * r (Fin.last n) = v' i + t i * φ v' := by
      rw [hrc, hrl, hv'i, hφv']
      simp only [b']
      ring
    simp only [he]
    exact Ideal.add_mem _ (Ideal.subset_span ⟨(i : ℕ), rfl⟩)
      (Ideal.mul_mem_left _ _ (linearMap_apply_mem_span_range_coeffs v' φ))
  obtain ⟨h, hh⟩ := finsupp_exists_form_of_span v' hspan
  let f1 : (ℕ →₀ R) →ₗ[R] R := h - h x • Finsupp.lapply j
  let f2 : (ℕ →₀ R) →ₗ[R] R := Finsupp.lapply j - v j • f1
  have hvdec : v = v' + v j • x := by simp [v']
  have hhv : h v = 1 + v j * h x := by
    conv_lhs => rw [hvdec]
    rw [map_add, map_smul, hh, smul_eq_mul]
  have hf1x : f1 x = 0 := by
    simp only [f1, LinearMap.sub_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul, hxj]
    ring
  have hf1v : f1 v = 1 := by
    simp only [f1, LinearMap.sub_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul, hhv]
    ring
  have hf2x : f2 x = 1 := by
    simp only [f2, LinearMap.sub_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul, hf1x, hxj]
    ring
  have hf2v : f2 v = 0 := by
    simp only [f2, LinearMap.sub_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul, hf1v]
    ring
  refine ⟨x, hxaff, ?_⟩
  simp only [uniM, Set.mem_setOf_eq]
  refine ⟨![f1, f2], ?_⟩
  intro p q
  fin_cases p <;> fin_cases q <;> simp [hf1x, hf1v, hf2x, hf2v]

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_mem_translate_unimodular_pair_of_stableRangeLe : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n j : ℕ), s ≤ n → n ≤ j → ∀ v : ℕ →₀ R, [v] ∈ uniM R (ℕ →₀ R) → ∃ x ∈ aff R n j, [v, x] ∈ uniM R (ℕ →₀ R) := by
  first
  | exact @GlobalTheory.unimodular_partner_aff
  | exact @GlobalTheory.finsupp_exists_form_of_span
  | exact @GlobalTheory.finsupp_coord_ideal_eq_top
end
