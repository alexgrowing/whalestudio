import Mathlib
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.HermitianLatticesTheory

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem nz_sum_normSq (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) {ι : Type} [Fintype ι]
    (x : ι → 𝓞 E) (h : ∑ i, star ((x i : 𝓞 E) : E) * ((x i : 𝓞 E) : E) = 1) (φ : E →+* ℂ) :
    ∑ i, Complex.normSq (φ ((x i : 𝓞 E) : E)) = 1 := by
  have h1 := congrArg φ h
  rw [map_sum, map_one] at h1
  have h2 : ((∑ i, Complex.normSq (φ ((x i : 𝓞 E) : E)) : ℝ) : ℂ) = 1 := by
    rw [← h1, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hconj, Complex.normSq_eq_conj_mul_self]
  exact_mod_cast h2

theorem nz_two_zero (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) {ι : Type} [Fintype ι]
    (x : ι → 𝓞 E) (h : ∑ i, star ((x i : 𝓞 E) : E) * ((x i : 𝓞 E) : E) = 1) {a b : ι} (hab : a ≠ b)
    (ha : x a ≠ 0) : x b = 0 := by
  classical
  by_contra hb
  have hy : x a * x b ≠ 0 := mul_ne_zero ha hb
  have key : ∀ v : InfinitePlace E, v (((x a * x b : 𝓞 E)) : E) < 1 := by
    intro v
    have h1 := nz_sum_normSq hconj x h v.embedding
    have h2 : Complex.normSq (v.embedding ((x a : 𝓞 E) : E)) + Complex.normSq (v.embedding ((x b : 𝓞 E) : E)) ≤ 1 := by
      rw [← h1, ← Finset.sum_pair (f := fun i => Complex.normSq (v.embedding ((x i : 𝓞 E) : E))) hab]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => Complex.normSq_nonneg _
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq,
      InfinitePlace.norm_embedding_eq] at h2
    have h3 : v (((x a * x b : 𝓞 E)) : E) = v ((x a : 𝓞 E) : E) * v ((x b : 𝓞 E) : E) := by
      rw [show (((x a * x b : 𝓞 E)) : E) = ((x a : 𝓞 E) : E) * ((x b : 𝓞 E) : E) from
        map_mul (algebraMap (𝓞 E) E) _ _, map_mul]
    rw [h3]
    nlinarith [sq_nonneg (v ((x a : 𝓞 E) : E) - v ((x b : 𝓞 E) : E))]
  obtain ⟨v0⟩ : Nonempty (InfinitePlace E) := inferInstance
  have := InfinitePlace.one_le_of_lt_one (w := v0) hy fun z _ => key z
  exact absurd (key v0) (not_lt.mpr this)

theorem nz_mono (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) {ι : Type} [Fintype ι]
    (x : ι → 𝓞 E) (h : ∑ i, star ((x i : 𝓞 E) : E) * ((x i : 𝓞 E) : E) = 1) :
    ∃ i, star ((x i : 𝓞 E) : E) * ((x i : 𝓞 E) : E) = 1 ∧ ∀ j, j ≠ i → x j = 0 := by
  classical
  have hex : ∃ i, x i ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [Finset.sum_eq_zero (fun i _ => by rw [hc i]; simp)] at h
    exact zero_ne_one h
  obtain ⟨i, hi⟩ := hex
  have hz : ∀ j, j ≠ i → x j = 0 := fun j hj => nz_two_zero hconj x h (Ne.symm hj) hi
  refine ⟨i, ?_, hz⟩
  rw [← h]
  symm
  apply Finset.sum_eq_single i
  · intro j _ hj
    rw [hz j hj]
    simp
  · intro hn
    exact absurd (Finset.mem_univ i) hn

theorem nz_exists_star (z : 𝓞 E) : ∃ z' : 𝓞 E, ((z' : 𝓞 E) : E) = star ((z : 𝓞 E) : E) := by
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp (star_coe_mem_one z)
  exact ⟨r, hr⟩

theorem nz_exists_inv {z : 𝓞 E} (hz : star ((z : 𝓞 E) : E) * ((z : 𝓞 E) : E) = 1) :
    ∃ z' : 𝓞 E, z' * z = 1 ∧ ((z' : 𝓞 E) : E) = star ((z : 𝓞 E) : E) := by
  obtain ⟨z', hz'⟩ := nz_exists_star z
  refine ⟨z', ?_, hz'⟩
  apply RingOfIntegers.coe_injective
  have e1 : ((z' * z : 𝓞 E) : E) = ((z' : 𝓞 E) : E) * ((z : 𝓞 E) : E) := map_mul (algebraMap (𝓞 E) E) z' z
  have e2 : ((1 : 𝓞 E) : E) = 1 := map_one (algebraMap (𝓞 E) E)
  show ((z' * z : 𝓞 E) : E) = ((1 : 𝓞 E) : E)
  rw [e1, e2, hz', hz]

theorem nz_unit_notMem {z : 𝓞 E} (hz : star ((z : 𝓞 E) : E) * ((z : 𝓞 E) : E) = 1) (w : HeightOneSpectrum (𝓞 E)) :
    z ∉ w.asIdeal := by
  intro hw
  obtain ⟨z', h1, -⟩ := nz_exists_inv hz
  have : (1 : 𝓞 E) ∈ w.asIdeal := h1 ▸ w.asIdeal.mul_mem_left z' hw
  exact one_notMem w this

theorem nz_one_of_congr (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    {w : Ideal (𝓞 E)} (hw : w ≠ ⊤) {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w) (hbig : finrank ℚ E + 1 < g)
    {z : 𝓞 E} (hz : star ((z : 𝓞 E) : E) * ((z : 𝓞 E) : E) = 1) (h1 : z - 1 ∈ w) : z = 1 := by
  have hz0 : ((z : 𝓞 E) : E) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hz
    exact zero_ne_one hz
  obtain ⟨z', hz'1, hz'⟩ := nz_exists_inv hz
  set γ : Sp E 1 ≃ₗ[E] Sp E 1 := LinearEquiv.smulOfNeZero E (Sp E 1) ((z : 𝓞 E) : E) hz0 with hγdef
  have hγx : ∀ x : Sp E 1, γ x = ((z : 𝓞 E) : E) • x := fun x => rfl
  have hγo : ∀ x : Sp E 1, γ x = z • x := fun x => by
    rw [hγx]
    exact (algebraMap_smul E z x)
  have hiso : γ ∈ isom (hStd E 1) := by
    intro x y
    rw [hγx, hγx, hStd_apply, hStd_apply, ← one_mul (∑ i, star (x i) * y i), ← hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, star_mul']
    ring
  have haut : γ ∈ autLat (stdLat E 1) := by
    rw [mem_autLat]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show γ x ∈ stdLat E 1
      rw [hγo]
      exact (stdLat E 1).smul_mem z hx
    · intro x hx
      refine ⟨z' • x, (stdLat E 1).smul_mem z' hx, ?_⟩
      show γ (z' • x) = x
      rw [hγo, smul_smul, mul_comm, hz'1, one_smul]
  have huni : UnipMod w (stdLat E 1) γ := by
    refine ⟨haut, 1, fun x hx => ?_⟩
    rw [pow_one]
    have : ((((γ : Sp E 1 →ₗ[E] Sp E 1) : Module.End E (Sp E 1)) - 1) : Module.End E (Sp E 1)) x = (z - 1) • x := by
      show γ x - x = (z - 1) • x
      rw [hγo, sub_smul, one_smul]
    rw [this]
    exact Submodule.smul_mem_smul h1 hx
  have hfr : finrank E (Sp E 1) = 1 := by simp
  have hone : γ = 1 := isometry_unipotent_mod_eq_one (hStd E 1) hStd_isSymm (hStd_trace_pos hconj) stdLat_lattice hw hg hgw
    (by rw [hfr, mul_one]; exact hbig) hiso huni
  have h2 := congrArg (fun e : Sp E 1 ≃ₗ[E] Sp E 1 => e (fun _ => 1) 0) hone
  have h3 : ((z : 𝓞 E) : E) = 1 := by simpa [hγx] using h2
  apply RingOfIntegers.coe_injective
  show ((z : 𝓞 E) : E) = ((1 : 𝓞 E) : E)
  rw [h3]
  exact (map_one (algebraMap (𝓞 E) E)).symm

end Gen

theorem nz_root_one {X : Fields} (hX : X.Ok) (w : HeightOneSpectrum (𝓞 X.E)) {g : ℕ} (hg : g.Prime)
    (hgw : (g : 𝓞 X.E) ∈ w.asIdeal) (hbig : 2 * X.f + 1 < g) {z : 𝓞 X.E}
    (hz : star ((z : 𝓞 X.E) : X.E) * ((z : 𝓞 X.E) : X.E) = 1) (h1 : z - 1 ∈ w.asIdeal) : z = 1 :=
  nz_one_of_congr hX.conjE w.isPrime.ne_top hg hgw (by rw [hX.finrank_E]; exact hbig) hz h1

end Formalism.L2.Col
