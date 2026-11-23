import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem isClosed_setOf_algEquiv_apply_eq {K L : Type} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] (a b : L) : IsClosed {g : L ≃ₐ[K] L | g a = b} := by
  by_cases h : ∃ g₀ : L ≃ₐ[K] L, g₀ a = b
  · obtain ⟨g₀, hg₀⟩ := h
    have hc : IsClosed ((MulAction.stabilizer (L ≃ₐ[K] L) a : Subgroup _) : Set (L ≃ₐ[K] L)) :=
      Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral a)
    have hp := hc.preimage (continuous_const_mul g₀⁻¹)
    convert hp using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      mul_smul, inv_smul_eq_iff]
    simp only [AlgEquiv.smul_def, hg₀]
  · have : {g : L ≃ₐ[K] L | g a = b} = ∅ := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hg => h ⟨g, hg⟩
    rw [this]
    exact isClosed_empty

theorem exists_primitive_for_finset (k : Type) {Ω : Type} [Field k] [CharZero k] [Field Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    (u : Finset Ω) : ∃ x : Ω, ∀ {L : Type} [Field L] (φ ψ : Ω →+* L),
      φ.comp (algebraMap k Ω) = ψ.comp (algebraMap k Ω) → φ x = ψ x →
      ∀ y ∈ u, φ y = ψ y := by
  let F : IntermediateField k Ω := IntermediateField.adjoin k (u : Set Ω)
  haveI : FiniteDimensional k F :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k F
  refine ⟨α, fun {L} _ φ ψ hk hx y hy => ?_⟩
  have key : ∀ z : F, z ∈ IntermediateField.adjoin k {α} → φ z = ψ z := by
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx' =>
      rw [Set.mem_singleton_iff.mp hx']
      exact hx
    | algebraMap q =>
      exact DFunLike.congr_fun hk q
    | add x y _ _ hx hy => simp [hx, hy]
    | inv x _ hx => simp [hx]
    | mul x y _ _ hx hy => simp [hx, hy]
  exact key ⟨y, IntermediateField.subset_adjoin k _ hy⟩ (by rw [hα]; trivial)

theorem exists_algEquiv_inducing_of_forall_conj :
    ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L]
      [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L)
      (s : Ω ≃ₐ[ℚ] Ω), (∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x)) →
      ∃ g : L ≃ₐ[K] L, ∀ x : Ω, g (j x) = j (s x) := by
  intro Ω L K _ _ _ _ _ _ _ _ _ j s h
  haveI : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois K L := {}
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hne := (isCompact_univ (X := L ≃ₐ[K] L)).inter_iInter_nonempty
    (fun x : Ω => {g : L ≃ₐ[K] L | g (j x) = j (s x)})
    (fun x => isClosed_setOf_algEquiv_apply_eq _ _)
    (fun u => by
      obtain ⟨x, hx⟩ := exists_primitive_for_finset ℚ u
      obtain ⟨g, hg⟩ := h x
      refine ⟨g, Set.mem_univ _, ?_⟩
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro y hy
      exact hx ((g : L →+* L).comp j) (j.comp (s : Ω →+* Ω)) (RingHom.ext_rat _ _) hg y hy)
  obtain ⟨g, -, hg⟩ := hne
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hg
  exact ⟨g, hg⟩

end GlobalTheory
