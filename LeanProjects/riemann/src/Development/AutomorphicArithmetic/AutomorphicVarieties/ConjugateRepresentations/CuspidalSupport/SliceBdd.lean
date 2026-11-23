import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRestrictionBlockEmbeddingIntertwinesLie
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermArchSmooth

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin

variable {K : Type} [Field K] [NumberField K]

private theorem left_slSp {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
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

private theorem bdd_slices {r s : ℕ} {S : Submodule ℂ (archSmooth K (r + s))} (hS : Bdd S) (hK : Sat S) :
    Bdd (slSp (e1 r s) (Set.range (emb (e2 r s))) (ctSp r S)) ∧
      Bdd (slSp (e2 r s) (Set.range (emb (e1 r s))) (ctSp r S)) := by
  obtain ⟨ι, _, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  obtain ⟨hN, hG, hL, hK', hM⟩ := UpperTheory.constantTermSpace_automorphic_properties K r s S hS hK
  have hT := UpperTheory.constantTermSpace_types_of_bdd K _ r S hS
  have hA := UpperTheory.algebraic_module_of_vanishing_block K r s _ hN (UpperTheory.constantTermSpace_centre_of_bdd K _ r S hS) ι D
  refine ⟨⟨left_slSp _ _ _ ?_, (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K _ _ _ _ _ hT,
      UpperTheory.siegelLevi_block_aeval_stable K _ _ _ _ _ (Van K r s) ι D ?_ fun τ u => (hA τ u).1⟩,
    ⟨left_slSp _ _ _ ?_, (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K _ _ _ _ _ hT,
      UpperTheory.siegelLevi_block_aeval_stable K _ _ _ _ _ (Van K r s) ι D ?_ fun τ u => (hA τ u).2⟩⟩
  · rintro ψ hψ _ ⟨m₂, rfl⟩ γ m
    rw [← hM ψ hψ γ 1 (emb (e2 r s) m₂ * emb (e1 r s) m), map_mul, ← mul_assoc, ← emb_comm, blk, map_one, mul_one,
      ← (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K _ _ _).2.1, mul_assoc]
  · rintro ψ hψ _ ⟨m₂, rfl⟩ m
    rw [← emb_comm]
    exact hψ m m₂
  · rintro ψ hψ _ ⟨m₁, rfl⟩ γ m
    rw [← hM ψ hψ 1 γ (emb (e1 r s) m₁ * emb (e2 r s) m), map_mul, ← mul_assoc, emb_comm, blk, map_one, one_mul,
      ← (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K _ _ _).2.1, mul_assoc]
  · rintro ψ hψ _ ⟨m₁, rfl⟩ m
    exact hψ m₁ m

private theorem exists_slice {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
    (S : Submodule ℂ (archSmooth K n)) {ψ : archSmooth K n} (hψ : ψ ∈ S) {g : AdelicGLn.AdelicGL K n} (hg : g ∈ Γ) :
    ∃ f ∈ slSp e Γ S, ∀ m, f.1 m = ψ.1 (g * emb e m) := by
  obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K a n e g
  exact ⟨f ψ, Submodule.subset_span ⟨ψ, hψ, g, hg, hf ψ⟩, hf ψ⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.sliceBdd :
    UpperTheory.V.Cj.S.SingleBdd → UpperTheory.V.Cj.S.SliceBdd := by
  intro hB E _ _ _ r s φ hφ
  obtain ⟨S, hle, hS, hK⟩ := UpperTheory.exists_automorphic_saturation_submodule E (r + s) _ (hB E (r + s) φ hφ)
  have hmem : UpperTheory.V.Cm.smEq E (r + s) φ ∈ S :=
    hle (Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self φ))
  obtain ⟨hs, -⟩ := UpperTheory.constantTerm_archSmooth E (r + s) r (UpperTheory.V.Cm.smEq E (r + s) φ) (UpperTheory.isAutomorphicForm_of_bdd_submodule E _ S hS _ hmem)
  have hψ : (⟨_, hs⟩ : GroundTheory.Automorphic.AutomorphicForm.archSmooth E (r + s)) ∈ UpperTheory.V.Af.Fin.ctSp r S :=
    Submodule.subset_span ⟨_, hmem, rfl⟩
  obtain ⟨h₁, h₂⟩ := bdd_slices hS hK
  refine ⟨Submodule.comap (UpperTheory.V.Cm.smEq E r).toLinearMap _, Submodule.comap (UpperTheory.V.Cm.smEq E s).toLinearMap _,
    h₁.mono (Submodule.map_comap_le _ _), h₂.mono (Submodule.map_comap_le _ _), fun y => ?_, fun x => ?_⟩
  · obtain ⟨f, hf, hf'⟩ := exists_slice (e1 r s) (Set.range (emb (e2 r s))) _ hψ ⟨y, rfl⟩
    refine ⟨(UpperTheory.V.Cm.smEq E r).symm f, by simpa using hf, funext fun x => (hf' x).trans ?_⟩
    rw [← UpperTheory.V.Af.Fin.emb_comm]
    rfl
  · obtain ⟨f, hf, hf'⟩ := exists_slice (e2 r s) (Set.range (emb (e1 r s))) _ hψ ⟨x, rfl⟩
    exact ⟨(UpperTheory.V.Cm.smEq E s).symm f, by simpa using hf, funext fun y => hf' y⟩
