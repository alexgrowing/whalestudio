import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIdempotentDecompositionMixedSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsAutomorphicFormOfBddSubmodule
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicSaturationSubmodule
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalOfBddCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingFiniteAdelicGLCompatContinuous
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsConstantTermLinearMapEquivariantUniversalE
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceTypesOfBdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceCentreOfBdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceAutomorphicProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgebraicModuleOfVanishingBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SiegelLeviBlockAevalStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SlSpPreservesGrowthAndLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalSlSpReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalOfFiniteDimensionalLeviSlices

noncomputable section

open NumberField NumberField.mixedEmbedding Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Af.Fin

variable {K : Type} [Field K] [NumberField K]

private theorem slLeft {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
    (S : Submodule ℂ (archSmooth K n))
    (h : ∀ ψ ∈ S, ∀ g ∈ Γ, ∀ γ m, ψ.1 (g * emb e (AdelicGLn.diagonal K a γ * m)) = ψ.1 (g * emb e m)) :
    ∀ f ∈ slSp e Γ S, IsLeftInvariant f.1 := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ψ, hψ, g, hg, hf⟩ := hf
    intro γ m
    rw [hf, hf, h ψ hψ g hg]
  | zero => exact isLeftInvariant_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

theorem ctFin {r s : ℕ} (h₁ : FinAt K r) (h₂ : FinAt K s) {S : Submodule ℂ (archSmooth K (r + s))} (hS : Bdd S)
    (hK : Sat S) : FiniteDimensional ℂ (ctSp r S) := by
  obtain ⟨ι, _, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  obtain ⟨hN, hG, hL, hSat, hinv⟩ := UpperTheory.constantTermSpace_automorphic_properties K r s S hS hK
  have hT := UpperTheory.constantTermSpace_types_of_bdd K (r + s) r S hS
  have hC := UpperTheory.constantTermSpace_centre_of_bdd K (r + s) r S hS
  have hcap := UpperTheory.algebraic_module_of_vanishing_block K r s (ctSp r S) hN hC ι D
  have hb1 : ∀ γ : GL (Fin r) K, emb (e1 r s) γ = blk γ (1 : GL (Fin s) K) := by
    intro γ
    simp [blk]
  have hb2 : ∀ γ : GL (Fin s) K, emb (e2 r s) γ = blk (1 : GL (Fin r) K) γ := by
    intro γ
    simp [blk]
  refine UpperTheory.finiteDimensional_of_finiteDimensional_levi_slices K r s (ctSp r S) hN hSat hL hT ?_ ?_
  · refine h₁ _ ⟨?_, (UpperTheory.slSp_preserves_growth_and_level K r (r + s) (e1 r s) _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K r (r + s) (e1 r s) _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K r (r + s) (e1 r s) _ _ hT, ?_⟩
    · apply slLeft
      rintro ψ hψ _ ⟨m₂, rfl⟩ γ m
      rw [map_mul, ← mul_assoc, ← emb_comm, mul_assoc, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K r (r + s) (e1 r s)).2.1 γ, hb1,
        hinv ψ hψ]
    · refine UpperTheory.siegelLevi_block_aeval_stable K r (r + s) (e1 r s) _ (ctSp r S) (Van K r s) ι D ?_ (fun τ u => (hcap τ u).1)
      rintro ψ hψ _ ⟨m₂, rfl⟩ m
      rw [← emb_comm]
      exact hψ m m₂
  · refine h₂ _ ⟨?_, (UpperTheory.slSp_preserves_growth_and_level K s (r + s) (e2 r s) _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K s (r + s) (e2 r s) _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K s (r + s) (e2 r s) _ _ hT, ?_⟩
    · apply slLeft
      rintro ψ hψ _ ⟨m₁, rfl⟩ γ m
      rw [map_mul, ← mul_assoc, emb_comm m₁ (AdelicGLn.diagonal K s γ), mul_assoc,
        (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K s (r + s) (e2 r s)).2.1 γ, hb2, hinv ψ hψ]
    · refine UpperTheory.siegelLevi_block_aeval_stable K s (r + s) (e2 r s) _ (ctSp r S) (Van K r s) ι D ?_ (fun τ u => (hcap τ u).2)
      rintro ψ hψ _ ⟨m₁, rfl⟩ m
      exact hψ m₁ m

private theorem fin_of_ker {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N)
    (h1 : FiniteDimensional ℂ (LinearMap.range f)) (h2 : FiniteDimensional ℂ (LinearMap.ker f)) :
    FiniteDimensional ℂ M := by
  apply Module.rank_lt_aleph0_iff.mp
  rw [← LinearMap.rank_range_add_rank_ker f]
  exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 ℂ _) (Module.rank_lt_aleph0 ℂ _)

theorem finAt_of {n : ℕ} (ih : ∀ m < n, FinAt K m) : FinAt K n := by
  intro S hS
  obtain ⟨S', hSS', hB', hSat'⟩ := UpperTheory.exists_automorphic_saturation_submodule K n S hS
  have hct : ∀ r, 0 < r → r < n → FiniteDimensional ℂ (ctSp r S') := by
    intro r hr0 hrn
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn.le
    exact ctFin (ih r hrn) (ih s (by omega)) hB' hSat'
  choose F hF1 _ using fun r => UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping K n r
  let ι : S' →ₗ[ℂ] automorphicForms K n :=
    LinearMap.codRestrict _ ((archSmooth K n).subtype ∘ₗ S'.subtype)
      (fun φ => UpperTheory.isAutomorphicForm_of_bdd_submodule K n S' hB' φ.1 φ.2)
  let I := {r : Fin n // 0 < r.val}
  have hmem : ∀ (i : I) (φ : S'), F i.1.val (ι φ) ∈ ctSp i.1.val S' := fun i φ =>
    Submodule.subset_span ⟨φ.1, φ.2, hF1 _ _⟩
  let G : S' →ₗ[ℂ] ((i : I) → ctSp i.1.val S') :=
    LinearMap.pi (fun i => LinearMap.codRestrict _ ((F i.1.val).comp ι) (hmem i))
  haveI : ∀ i : I, FiniteDimensional ℂ (ctSp i.1.val S') := fun i => hct _ i.2 i.1.2
  haveI : FiniteDimensional ℂ S' := by
    refine fin_of_ker G inferInstance ?_
    have hW : FiniteDimensional ℂ ((LinearMap.ker G).map S'.subtype) := by
      refine UpperTheory.finiteDimensional_of_bdd_cuspidal K n _ (hB'.mono (Submodule.map_subtype_le _ _)) ?_
      rintro _ ⟨x, hx, rfl⟩ r hr0 hrn g
      have h0 : F r (ι x) = 0 := by
        have := congrFun (LinearMap.mem_ker.mp hx) ⟨⟨r, hrn⟩, hr0⟩
        exact congrArg Subtype.val this
      have h1 := congrArg (fun ψ : archSmooth K n => (ψ : AdelicGLn.AdelicGL K n → ℂ) g) h0
      simp only [hF1] at h1
      exact h1
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ S'.injective_subtype _).symm
  exact Submodule.finiteDimensional_of_le hSS'

theorem formsFinite : FormsFinite := fun _ _ _ n => Nat.strong_induction_on n fun _ ih => finAt_of ih

end UpperTheory.V.Af.Fin
