import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField Module GroundTheory.Global GroundTheory.Global.Elliptic GroundTheory.Arith.Abelian WeierstrassCurve
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem PrimeDiscriminant.nrComplexPlaces_eq_one (S : PrimeDiscriminant K) :
    InfinitePlace.nrComplexPlaces K = 1 := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [Algebra.IsQuadraticExtension.finrank_eq_two ℚ K] at h1
  have h2 := sign_discr (K := K)
  have hd : (0 : ℤ) < S.d := by exact_mod_cast S.prime.pos
  rw [S.discr_eq, Int.sign_neg, Int.sign_eq_one_of_pos hd] at h2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (show InfinitePlace.nrComplexPlaces K ≤ 1 by omega)
    with h | h
  · rw [h] at h2
    norm_num at h2
  · exact h

theorem PrimeDiscriminant.isTotallyComplex (S : PrimeDiscriminant K) : IsTotallyComplex K := by
  rw [← nrRealPlaces_eq_zero_iff]
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [Algebra.IsQuadraticExtension.finrank_eq_two ℚ K, S.nrComplexPlaces_eq_one] at h1
  omega

theorem PrimeDiscriminant.eq_or_eq_conjugate (S : PrimeDiscriminant K) (σ τ : K →+* ℂ) :
    τ = σ ∨ τ = ComplexEmbedding.conjugate σ := by
  have hreal : InfinitePlace.nrRealPlaces K = 0 :=
    nrRealPlaces_eq_zero_iff.2 S.isTotallyComplex
  have hcard : Fintype.card (InfinitePlace K) ≤ 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hreal, S.nrComplexPlaces_eq_one]
  have hsub := Fintype.card_le_one_iff_subsingleton.1 hcard
  rcases InfinitePlace.mk_eq_iff.1 (Subsingleton.elim (InfinitePlace.mk σ) (InfinitePlace.mk τ))
    with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

omit [Algebra.IsQuadraticExtension ℚ K] in

theorem idealLattice_conjugate (σ : K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K) :
    idealLattice (ComplexEmbedding.conjugate σ) I = conjLattice (idealLattice σ I) := by
  ext z
  rw [conjLattice, Submodule.mem_map, mem_idealLattice]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨σ x, map_mem_idealLattice σ hx, by simp [ComplexEmbedding.conjugate_coe_eq]⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ).1 hw
    exact ⟨x, hx, by simp [ComplexEmbedding.conjugate_coe_eq]⟩

omit [Algebra.IsQuadraticExtension ℚ K] in

theorem exists_idealLattice_of_cmRing_le (hK : finrank ℚ K = 2) [IsTotallyComplex K]
    (σ : K →+* ℂ) (L : PeriodPair) (hL : cmRing σ ≤ latticeEnd L) :
    ∃ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ℂ), c ≠ 0 ∧
      (L.lattice : Set ℂ) = (c * ·) '' idealLattice σ I := by
  have hω : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  obtain ⟨θ, hθ⟩ := exists_ringOfIntegers_not_rat hK (K := K)
  have hθL : σ (algebraMap (𝓞 K) K θ) ∈ latticeEnd L := hL ⟨θ, rfl⟩
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 (hθL _ L.ω₁_mem_lattice)
  have hn : n ≠ 0 := by
    rintro rfl
    apply hθ m
    apply σ.injective
    simp only [Int.cast_zero, zero_mul, add_zero] at hmn
    have h0 : (σ (algebraMap (𝓞 K) K θ) - m) * L.ω₁ = 0 := by linear_combination -hmn
    have h2 : σ (algebraMap (𝓞 K) K θ) = m := by
      linear_combination (mul_eq_zero.1 h0).resolve_right hω
    rw [h2]
    simp
  set y : K := (algebraMap (𝓞 K) K θ - m) / n
  have hy : σ y * L.ω₁ = L.ω₂ := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [show σ y = (σ (algebraMap (𝓞 K) K θ) - m) / n by simp [y], div_mul_eq_mul_div,
      div_eq_iff hn']
    linear_combination -hmn
  let M : Submodule (𝓞 K) K :=
    { carrier := {x | σ x * L.ω₁ ∈ L.lattice}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_ofPred_eq, map_add, add_mul] at *
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a x hx ↦ by
        simp only [Set.mem_ofPred_eq] at *
        rw [Algebra.smul_def, map_mul, mul_assoc]
        exact (hL ⟨a, rfl⟩ : σ (algebraMap (𝓞 K) K a) ∈ latticeEnd L) _ hx }
  have hmem : ∀ x : K, x ∈ M ↔ σ x * L.ω₁ ∈ L.lattice := fun _ ↦ Iff.rfl
  have h1 : (1 : K) ∈ M := by rw [hmem, map_one, one_mul]; exact L.ω₁_mem_lattice
  have hyM : y ∈ M := by rw [hmem, hy]; exact L.ω₂_mem_lattice
  have hM : ∀ x ∈ M, ∃ a b : ℤ, x = a + b * y := by
    intro x hx
    obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 ((hmem x).1 hx)
    refine ⟨a, b, σ.injective ?_⟩
    apply mul_right_cancel₀ hω
    rw [← hab, map_add, map_mul, map_intCast, map_intCast, add_mul, mul_assoc, hy]
  have hspan : M = Submodule.span (𝓞 K) {1, y} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, b, rfl⟩ := hM x hx
      refine add_mem ?_ ?_
      · rw [← mul_one (a : K), ← zsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ a (Submodule.subset_span (by simp))
      · rw [← zsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ b (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      rintro z (rfl | rfl)
      · exact h1
      · exact hyM
  have hfg : M.FG := by
    rw [hspan]
    exact Submodule.fg_span (Set.toFinite _)
  let I₀ : FractionalIdeal (𝓞 K)⁰ K := ⟨M, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI₀ : I₀ ≠ 0 := by
    intro h
    have : (1 : K) ∈ I₀ := h1
    rw [h, FractionalIdeal.mem_zero_iff] at this
    exact one_ne_zero this
  refine ⟨Units.mk0 I₀ hI₀, L.ω₁, hω, ?_⟩
  ext z
  simp only [SetLike.mem_coe, Set.mem_image]
  constructor
  · intro hz
    obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
    refine ⟨σ (a + b * y), map_mem_idealLattice σ (x := a + b * y) ?_, ?_⟩
    · show (a + b * y : K) ∈ M
      rw [hspan]
      refine add_mem ?_ ?_
      · rw [← mul_one (a : K), ← zsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ a (Submodule.subset_span (by simp))
      · rw [← zsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ b (Submodule.subset_span (by simp))
    · rw [map_add, map_mul, map_intCast, map_intCast]
      linear_combination (b : ℂ) * hy
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ).1 hw
    rw [mul_comm]
    exact (hmem x).1 hx

theorem CMFamily.exists_periodLattice_eq (S : PrimeDiscriminant K) (F : CMFamily K)
    (s : F.k →+* ℂ) :
    ∃ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ℂ), c ≠ 0 ∧
      (F.periodLattice s : Set ℂ) = (c * ·) '' idealLattice (F.restrict s) I := by
  classical
  have := S.isTotallyComplex
  obtain ⟨L, C, hC, hΛ⟩ := F.isPeriodLattice s
  have hle : cmRing (F.restrict s) ≤ latticeEnd L := by
    rintro z ⟨a, rfl⟩
    by_cases ha : a = 0
    · subst ha
      simp only [map_zero]
      exact (latticeEnd L).zero_mem
    obtain ⟨φ, hφ⟩ := F.normalised a ha
    rw [← range_endConst (inv_smul_eq_of_smul_eq C hC)]
    refine ⟨((φ.map s).toHom : isogEnd (F.E.map s)), ?_⟩
    rw [endConst_apply, homConst_toHom, invConst_map, hφ]
    rfl
  obtain ⟨I, c, hc, h⟩ := exists_idealLattice_of_cmRing_le
    (Algebra.IsQuadraticExtension.finrank_eq_two ℚ K) (F.restrict s) L hle
  refine ⟨I, (C.u : ℂ) * c, mul_ne_zero C.u.ne_zero hc, ?_⟩
  rw [hΛ, scaleLattice, Submodule.map_coe, h, Set.image_image]
  simp only [LinearMap.mulLeft_apply, mul_assoc]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
