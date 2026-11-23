import Mathlib
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

noncomputable def gaussRed {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (V : ValuationSubring U) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    MvPolynomial σ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) :=
  ∑ α ∈ p.support, monomial α (IsLocalRing.residue _ ⟨p.coeff α, hc α⟩)

theorem gaussRed_coeff {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (V : ValuationSubring U) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) (α : σ →₀ ℕ) :
    (gaussRed V p hc).coeff α = IsLocalRing.residue _ ⟨p.coeff α, hc α⟩ := by
  classical
  unfold gaussRed
  rw [MvPolynomial.coeff_sum]
  by_cases h : α ∈ p.support
  · rw [Finset.sum_eq_single α]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg hb]
    · intro h'
      exact absurd h h'
  · have h0 : p.coeff α = 0 := by simpa [MvPolynomial.mem_support_iff] using h
    have hz : (⟨p.coeff α, hc α⟩ : V.comap (algebraMap Ω U)) = 0 := Subtype.ext h0
    rw [Finset.sum_eq_zero, hz, map_zero]
    intro b hb
    rw [MvPolynomial.coeff_monomial, if_neg]
    rintro rfl
    exact h hb

theorem gaussRed_eval {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    letI := residueAlgebra V (algebraMap Ω U)
    ∃ h : aeval t p ∈ V, IsLocalRing.residue V ⟨aeval t p, h⟩ =
      aeval (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) (gaussRed V p hc) := by
  try dsimp only
  letI := residueAlgebra V (algebraMap Ω U)
  classical
  obtain ⟨y, hydef⟩ : ∃ y : V, y = ∑ α ∈ p.support,
      comapInclusion V (algebraMap Ω U) ⟨p.coeff α, hc α⟩ *
        ∏ s ∈ α.support, (⟨t s, ht s⟩ : V) ^ α s := ⟨_, rfl⟩
  have hy : (y : U) = aeval t p := by
    change V.subtype y = _
    rw [hydef, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    simp only [map_sum, map_mul, map_prod, map_pow]
    rfl
  have hmem : aeval t p ∈ V := by
    rw [← hy]
    exact y.2
  refine ⟨hmem, ?_⟩
  have hyy : (⟨aeval t p, hmem⟩ : V) = y := Subtype.ext hy.symm
  rw [hyy, hydef, map_sum]
  unfold gaussRed
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.aeval_monomial]
  simp only [map_mul, map_prod, map_pow]
  congr 1

private theorem residue_ne_zero_of_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {x : R}
    (hx : IsUnit x) : IsLocalRing.residue R x ≠ 0 := by
  intro h
  have hm : x ∈ IsLocalRing.maximalIdeal R := by
    exact (IsLocalRing.residue_eq_zero_iff x).1 h
  exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal x).1 hm) hx

private theorem isUnit_of_residue_ne_zero' {R : Type*} [CommRing R] [IsLocalRing R] {x : R}
    (h : IsLocalRing.residue R x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  have hm : x ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal x).2 (mem_nonunits_iff.2 hx)
  exact (IsLocalRing.residue_eq_zero_iff x).2 hm

private theorem eq_zero_of_aeval_eq_zero_of_algebraicIndependent {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {x : ι → A} (hx : AlgebraicIndependent R x) {q : MvPolynomial ι R}
    (h : MvPolynomial.aeval x q = 0) : q = 0 := by
  exact (algebraicIndependent_iff.1 hx) q h

theorem gauss_unit {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (p : MvPolynomial σ Ω) (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U))
    (α₀ : σ →₀ ℕ) (hα₀ : (p.coeff α₀)⁻¹ ∈ V.comap (algebraMap Ω U)) (h0 : p.coeff α₀ ≠ 0) :
    V.valuation (aeval t p) = 1 := by
  letI := residueAlgebra V (algebraMap Ω U)
  have hind' : AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
      (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) := hind
  obtain ⟨hmem, hres⟩ := gaussRed_eval t V ht p hc
  have hu0 : IsUnit (⟨p.coeff α₀, hc α₀⟩ : V.comap (algebraMap Ω U)) :=
    isUnit_iff_exists_inv.mpr ⟨⟨(p.coeff α₀)⁻¹, hα₀⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  have hq : gaussRed V p hc ≠ 0 := by
    intro h
    have h1 := gaussRed_coeff V p hc α₀
    rw [h, MvPolynomial.coeff_zero] at h1
    exact residue_ne_zero_of_isUnit hu0 h1.symm
  have hne : IsLocalRing.residue V ⟨aeval t p, hmem⟩ ≠ 0 := by
    rw [hres]
    intro h
    exact hq (eq_zero_of_aeval_eq_zero_of_algebraicIndependent hind' h)
  have hunit := isUnit_of_residue_ne_zero' hne
  exact (V.valuation_eq_one_iff _).1 hunit

private theorem gaussValuation_of_mem_valuationSubring {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (p : MvPolynomial σ Ω) (hp : p ≠ 0) :
    ∃ α₀ ∈ p.support, (∀ α ∈ p.support, V.valuation (algebraMap Ω U (p.coeff α)) ≤
        V.valuation (algebraMap Ω U (p.coeff α₀))) ∧
      V.valuation (aeval t p) = V.valuation (algebraMap Ω U (p.coeff α₀)) := by
  have hne : p.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 fun h => hp (MvPolynomial.support_eq_empty.1 h)
  obtain ⟨α₀, hα₀, hmax⟩ := Finset.exists_max_image p.support
    (fun α => V.valuation (algebraMap Ω U (p.coeff α))) hne
  refine ⟨α₀, hα₀, hmax, ?_⟩
  have hc0 : p.coeff α₀ ≠ 0 := MvPolynomial.mem_support_iff.1 hα₀
  have hv0 : V.valuation (algebraMap Ω U (p.coeff α₀)) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact (map_ne_zero _).2 hc0
  obtain ⟨q, hqdef⟩ : ∃ q : MvPolynomial σ Ω, q = MvPolynomial.C (p.coeff α₀)⁻¹ * p := ⟨_, rfl⟩
  have hqcoeff : ∀ α, q.coeff α = (p.coeff α₀)⁻¹ * p.coeff α := by
    intro α
    rw [hqdef]
    exact MvPolynomial.coeff_C_mul _ _ _
  have hqc : ∀ α, q.coeff α ∈ V.comap (algebraMap Ω U) := by
    intro α
    rw [hqcoeff, ValuationSubring.mem_comap]
    apply (V.valuation_le_one_iff _).1
    simp only [map_mul, map_inv₀]
    by_cases hα : α ∈ p.support
    · have hle : V.valuation (algebraMap Ω U (p.coeff α)) ≤
          V.valuation (algebraMap Ω U (p.coeff α₀)) := hmax α hα
      calc (V.valuation (algebraMap Ω U (p.coeff α₀)))⁻¹ * V.valuation (algebraMap Ω U (p.coeff α))
          ≤ (V.valuation (algebraMap Ω U (p.coeff α₀)))⁻¹ *
              V.valuation (algebraMap Ω U (p.coeff α₀)) := by
            exact mul_le_mul_of_nonneg_left hle zero_le'
        _ = 1 := inv_mul_cancel₀ hv0
    · have h0 : p.coeff α = 0 := by simpa [MvPolynomial.mem_support_iff] using hα
      rw [h0]
      simp
  have hα₀' : (q.coeff α₀)⁻¹ ∈ V.comap (algebraMap Ω U) := by
    rw [hqcoeff, inv_mul_cancel₀ hc0, inv_one]
    exact one_mem _
  have h0' : q.coeff α₀ ≠ 0 := by
    rw [hqcoeff, inv_mul_cancel₀ hc0]
    exact one_ne_zero
  have h1 := gauss_unit t V ht hind q hqc α₀ hα₀' h0'
  have hq : aeval t q = algebraMap Ω U (p.coeff α₀)⁻¹ * aeval t p := by
    rw [hqdef, map_mul, MvPolynomial.aeval_C]
  rw [hq] at h1
  simp only [map_mul, map_inv₀] at h1
  calc V.valuation (aeval t p)
      = V.valuation (algebraMap Ω U (p.coeff α₀)) *
          ((V.valuation (algebraMap Ω U (p.coeff α₀)))⁻¹ * V.valuation (aeval t p)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hv0, one_mul]
    _ = V.valuation (algebraMap Ω U (p.coeff α₀)) := by rw [h1, mul_one]

theorem gauss_val {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (p : MvPolynomial σ Ω) :
    V.valuation (aeval t p) = p.support.sup fun α => V.valuation (algebraMap Ω U (p.coeff α)) := by
  by_cases hp : p = 0
  · subst hp
    rw [map_zero, MvPolynomial.support_zero, Finset.sup_empty]
    exact V.valuation.map_zero
  · obtain ⟨α₀, hα₀, hmax, hv⟩ := gaussValuation_of_mem_valuationSubring t V ht hind p hp
    rw [hv]
    exact le_antisymm
      (Finset.le_sup (f := fun α => V.valuation (algebraMap Ω U (p.coeff α))) hα₀)
      (Finset.sup_le hmax)

end ReciprocityTheory.MultiplicativeHeights
