import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueAnnihilatorOfNotStandardColumnFormAStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueTopFactorThroughBottomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrMatrixProjPreimageStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlFactorFromBlocksModUniformizerStatement
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem GlobalTheory.gen_type_core : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) O, (¬ ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)) → ∃ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 ∧ ∀ g : GL (Fin r) (IsLocalRing.ResidueField O), (∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v) → ∀ L : Matrix (Fin r) (Fin r) O, L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∃ h : GL (Fin r ⊕ Fin t) O, (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j ∈ Ideal.span {ϖ}) ∧ (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}) ∧ (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * (Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O) * x) = x := by
  intro O K _ _ _ _ _ _ _ r t ϖ hϖ x hx
  obtain ⟨a, ha, hA⟩ := GlobalTheory.T.exists_residue_annihilator_of_not_standard_column_form_alt O K r t ϖ hϖ x hx
  refine ⟨a, ha, fun g hg L hL => ?_⟩
  set S : Submodule K (Fin r ⊕ Fin t → K) := Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) with hS
  let U : Submodule O (Fin r ⊕ Fin t → O) := Submodule.comap ((Algebra.linearMap O K).compLeft (Fin r ⊕ Fin t)) (S.restrictScalars O)
  have hU : ∀ u, u ∈ U ↔ (fun i => algebraMap O K (u i)) ∈ S := fun u => Iff.rfl
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_residue_first_block_factor_of_second O r t U a (fun u hu h2 => hA u ((hU u).1 hu) h2) (g : Matrix (Fin r) (Fin r) _) hg
  obtain ⟨P, hP1, hP2⟩ := GlobalTheory.T.dvr_matrix_proj_preimage_alt O K (Fin r ⊕ Fin t) S
  set bt : Matrix (Fin r) (Fin t) O := b.map (Function.surjInv IsLocalRing.residue_surjective) with hbt
  have hbt' : bt.map (IsLocalRing.residue O) = b := by
    ext i j; simp [hbt, Function.surjInv_eq]
  set q₀ : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O := Matrix.fromBlocks L bt 0 1 with hq₀

  have key : ∀ u ∈ U, ∀ i, IsLocalRing.residue O (Matrix.mulVec (1 - q₀) u i) = 0 := by
    intro u hu i
    have h1 := hb u hu
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, map_sub, sub_eq_zero]
    rw [RingHom.map_mulVec, hq₀, Matrix.fromBlocks_map]
    rw [Matrix.fromBlocks_mulVec]
    rcases i with i | i
    · have := congrFun h1 i
      simp only [Sum.elim_inl, Pi.add_apply] at this ⊢
      rw [hL, hbt']
      simpa [Function.comp_def] using this.symm
    · simp [Function.comp_def]
  have hPx : P * x = x := by
    ext i j
    have := hP2 (fun i => x i j) (Submodule.subset_span ⟨j, rfl⟩)
    exact congrFun this i
  set q := q₀ + (1 - q₀) * P with hq
  have hqx : q * x = x := by
    rw [hq, Matrix.add_mul, Matrix.mul_assoc, hPx, Matrix.sub_mul, Matrix.one_mul]; abel
  have hqq : ∀ i j, IsLocalRing.residue O (q i j) = IsLocalRing.residue O (q₀ i j) := by
    intro i j
    have hcol : (fun l => P l j) ∈ U := by
      have := hP1 (Pi.single j 1)
      rw [hU]; simpa [Matrix.mulVec_single] using this
    have := key _ hcol i
    rw [hq, Matrix.add_apply, map_add]
    have e : ((1 - q₀) * P) i j = Matrix.mulVec (1 - q₀) (fun l => P l j) i := rfl
    rw [e, this, add_zero]
  obtain ⟨h, h1, h2, h3⟩ := GlobalTheory.T.gl_factor_fromBlocks_mod_uniformizer_alt O r t ϖ hϖ g L hL bt q hqq
  exact ⟨h, h1, h2, by rw [← Matrix.mul_assoc, h3, hqx]⟩
