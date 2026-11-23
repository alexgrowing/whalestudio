import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreRepresentatives
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAvoidFormFinite
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreRepresentatives

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in

theorem isMultiHomog_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {f : MRingOver R ι}
    {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (map φ f : MRingOver S ι) a :=
  fun m hm => hf m (support_map_subset φ f hm)

omit [Fintype K] in

theorem isMultiHomog_lincomb {f g : MRingOver ℂ ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) (c d : ℂ) : IsMultiHomog (C c * f - C d * g) a := by
  classical
  intro m hm
  rw [C_mul', C_mul'] at hm
  rcases Finset.mem_union.1 (support_sub _ _ _ hm) with h | h
  · exact hf m (support_smul h)
  · exact hg m (support_smul h)

theorem eval_smul {s : MRingOver ℂ ι} {a : K → ℕ} (hs : IsMultiHomog s a) (r : K → ℂ)
    (z : (Σ k, ι k) → ℂ) : eval (fun p => r p.1 * z p) s = (∏ k, r k ^ a k) * eval z s := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ p : (Σ k, ι k), r p.1 ^ d p) = ∏ k, r k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, r k ^ d ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem eval_eq_zero_of_homog {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ f ∈ mCoordIdeal y, (∃ a, IsMultiHomog f a) → eval z (map (Int.castRingHom ℂ) f) = 0)
    (f : MRing ι) (hf : f ∈ mCoordIdeal y) : eval z (map (Int.castRingHom ℂ) f) = 0 := by
  rw [eq_sum_multihomogeneous_components f, map_sum, map_sum]
  refine Finset.sum_eq_zero fun b _ => hz _ ?_ ⟨b, isMultiHomog_i2comp b f⟩
  exact i2comp_mem (CoordinateConeArithVar.isMultiHomogIdeal y) b hf

end FibreRepresentatives

open FibreRepresentatives in

theorem FibreRepresentatives.proof (h : AvoidFormFinite.Statement) : FibreRepresentatives.Statement := by
  intro K _ ι _ Ω _ y D e L he hL hL0 ζ
  classical
  set Lc : Fin (D + 1) → MRingOver ℂ ι := fun j => map (Int.castRingHom ℂ) (L j) with hLc
  by_cases hζ : ζ = 0
  · refine ⟨∅, by simp, fun z hz ⟨t, ht⟩ => ?_⟩
    obtain ⟨j, hj⟩ := hL0 z hz
    exact absurd (by simpa [hζ] using ht j) hj
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ζ j₀ ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hζ (funext hne)
  let S : Set (MRingOver ℂ ι) :=
    {g | ∃ f ∈ mCoordIdeal y, (∃ a, IsMultiHomog f a) ∧ g = map (Int.castRingHom ℂ) f} ∪
      Set.range fun j => C (ζ j₀) * Lc j - C (ζ j) * Lc j₀

  have key : ∀ z : (Σ k, ι k) → ℂ, ((∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ s ∈ S, eval z s = 0) ↔
      (z ∈ mcPts (mCoordIdeal y) ∧ ∃ t : ℂ, ∀ j, eval z (Lc j) = t * ζ j) := by
    intro z
    constructor
    · rintro ⟨hb, hS⟩
      refine ⟨⟨hb, eval_eq_zero_of_homog y z fun f hf ha => hS _ (Or.inl ⟨f, hf, ha, rfl⟩)⟩,
        eval z (Lc j₀) / ζ j₀, fun j => ?_⟩
      have h1 := hS _ (Or.inr ⟨j, rfl⟩)
      simp only [map_sub, map_mul, eval_C] at h1
      field_simp
      linear_combination h1
    · rintro ⟨hz, t, ht⟩
      refine ⟨hz.1, fun s hs => ?_⟩
      rcases hs with ⟨f, hf, -, rfl⟩ | ⟨j, rfl⟩
      · exact hz.2 f hf
      · simp only [map_sub, map_mul, eval_C, ht]
        ring
  have hSh : ∀ s ∈ S, ∃ a, IsMultiHomog s a := by
    rintro s (⟨f, -, ⟨a, ha⟩, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨a, isMultiHomog_map _ ha⟩
    · exact ⟨e, isMultiHomog_lincomb (isMultiHomog_map _ (hL j)) (isMultiHomog_map _ (hL j₀)) _ _⟩
  have hG : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) →
      eval z (Lc j₀) ≠ 0 := by
    intro z hb hS h0
    obtain ⟨hz, t, ht⟩ := (key z).1 ⟨hb, hS⟩
    have ht0 : t = 0 := by
      have := ht j₀
      rw [h0] at this
      exact (mul_eq_zero.1 this.symm).resolve_right hj₀
    obtain ⟨j, hj⟩ := hL0 z hz
    exact hj (by simpa [hLc, ht0] using ht j)
  obtain ⟨T, hT⟩ := h K ι S (Lc j₀) e he (isMultiHomog_map _ (hL j₀)) hSh hG
  refine ⟨T.filter fun t => (∀ k, ∃ i, t ⟨k, i⟩ ≠ 0) ∧ ∀ s ∈ S, eval t s = 0, fun z hz => ?_,
    fun z hz hfib => ?_⟩
  · exact (key z).1 (Finset.mem_filter.1 hz).2
  · obtain ⟨hb, hS⟩ := (key z).2 ⟨hz, hfib⟩
    obtain ⟨t, htT, r, hr, rfl⟩ := hT z hb hS
    have hinv : t = fun p => (r p.1)⁻¹ * (r p.1 * t p) := by
      funext p
      rw [← mul_assoc, inv_mul_cancel₀ (hr p.1), one_mul]
    refine ⟨t, Finset.mem_filter.2 ⟨htT, fun k => ?_, fun s hs => ?_⟩, r, hr, rfl⟩
    · obtain ⟨i, hi⟩ := hb k
      exact ⟨i, fun h0 => hi (by simp [h0])⟩
    · obtain ⟨a, ha⟩ := hSh s hs
      rw [hinv, eval_smul ha (fun k => (r k)⁻¹), hS s hs, mul_zero]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
