import Mathlib

open scoped IntermediateField.algebraAdjoinAdjoin
open Cardinal

namespace GlobalTheory

theorem trdeg_le_of_map_mem_closure_algebraic_union
    {k K K' A : Type} [Field k] [Field K] [Field K'] [CommRing A] (ρ : k →+* K) (σ : K →+* K')
    (φ : A →+* K) (hφ : Subfield.closure (Set.range φ) = ⊤) (L₀ : Subfield K')
    (hL : ∀ z ∈ L₀, @IsAlgebraic k K' _ _ (σ.comp ρ).toAlgebra z) {d : ℕ} (cf : Fin d → K')
    (hcf : ∀ r, σ (φ r) ∈ Subfield.closure ((L₀ : Set K') ∪ Set.range cf)) :
    @Algebra.trdeg k K _ _ ρ.toAlgebra ≤ (d : Cardinal) := by
  letI : Algebra k K := ρ.toAlgebra
  letI : Algebra k K' := (σ.comp ρ).toAlgebra
  let S := Algebra.adjoin k (Set.range cf)
  let E := IntermediateField.adjoin k (Set.range cf)
  have hS : Algebra.trdeg k S ≤ d := by
    let g : MvPolynomial (Fin d) k →ₐ[k] S := (MvPolynomial.aeval cf).codRestrict S (fun p => by
      show _ ∈ Algebra.adjoin k (Set.range cf)
      rw [Algebra.adjoin_range_eq_range_aeval k cf]; exact ⟨p, rfl⟩)
    have hg : Function.Surjective g := by
      rintro ⟨y, hy⟩
      have hy' : y ∈ (MvPolynomial.aeval (R := k) cf).range := by
        rw [← Algebra.adjoin_range_eq_range_aeval k cf]; exact hy
      obtain ⟨p, hp⟩ := hy'
      exact ⟨p, Subtype.ext hp⟩
    have h1 := lift_trdeg_le_of_surjective g hg
    simpa [MvPolynomial.trdeg_of_isDomain] using h1
  have hE : Algebra.trdeg k E ≤ d := by
    haveI : FaithfulSMul k S := (faithfulSMul_iff_algebraMap_injective k S).mpr (algebraMap k S).injective
    have h := trdeg_add_eq k S (A := E)
    rw [trdeg_eq_zero (R := S) (A := E), add_zero] at h
    rw [← h]; exact hS
  let F := IntermediateField.adjoin E (L₀ : Set K')
  have hint : ∀ z ∈ (L₀ : Set K'), IsIntegral E z := fun z hz =>
    (IsAlgebraic.tower_top E (hL z hz)).isIntegral
  haveI : Algebra.IsAlgebraic E F := IntermediateField.isAlgebraic_adjoin hint
  have hF : Algebra.trdeg k F = Algebra.trdeg k E := by
    haveI : FaithfulSMul E F := (faithfulSMul_iff_algebraMap_injective E F).mpr (algebraMap E F).injective
    have h := trdeg_add_eq k E (A := F)
    rw [trdeg_eq_zero (R := E) (A := F), add_zero] at h
    exact h.symm
  have hcl : Subfield.closure ((L₀ : Set K') ∪ Set.range cf) ≤ F.toSubfield := by
    rw [Subfield.closure_le]
    refine Set.union_subset (fun z hz => IntermediateField.subset_adjoin E _ hz) ?_
    rintro _ ⟨i, rfl⟩
    exact F.algebraMap_mem (⟨cf i, IntermediateField.subset_adjoin k _ ⟨i, rfl⟩⟩ : E)
  have hmem : ∀ x : K, σ x ∈ F := by
    have hle : Subfield.closure (Set.range φ) ≤ F.toSubfield.comap σ := by
      rw [Subfield.closure_le]
      rintro _ ⟨r, rfl⟩
      exact hcl (hcf r)
    intro x
    have hx : x ∈ Subfield.closure (Set.range φ) := by rw [hφ]; exact Subfield.mem_top x
    exact hle hx
  let f : K →ₐ[k] F :=
    { toRingHom := σ.codRestrict F hmem
      commutes' := fun r => Subtype.ext rfl }
  have hf : Function.Injective f := fun x y hxy => σ.injective (congrArg Subtype.val hxy)
  calc Algebra.trdeg k K ≤ Algebra.trdeg k F := trdeg_le_of_injective f hf
    _ = Algebra.trdeg k E := hF
    _ ≤ d := hE

end GlobalTheory
