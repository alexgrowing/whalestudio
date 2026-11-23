import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddOfMemLdivSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEPowMulFrobMemRightDivisorSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSliceMemRightDivisorSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemLeftDivisorSetPhiModuleHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusResidueSliceMemBoundedLeftDivisorSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMemOfFrobeniusLinkedBoundedSeriesIdealsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokerFiniteLengthOfPrimitiveDivisorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelTorsionFreeOfBoundedLeftInverseStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BK.Hom.finiteLength_coker_of_generic : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → IsFiniteLength (A O K) F.coker) ∧ ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h1 : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := (map_natCast _ _).symm
  have hlK : ‖(l : K)‖ < 1 := by
    rw [h1, norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl2)
  have hl0 : (l : K) ≠ 0 := by
    rw [h1]
    exact (map_ne_zero _).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  have hone : ∃ c : ℝ, ∀ n, ‖coeff n (1 : K⟦X⟧)‖ ≤ c :=
    ⟨1, fun n => by rw [coeff_one]; split_ifs <;> simp⟩
  refine ⟨fun hyp => GlobalTheory.T.coker_finite_length_of_primitive_divisor O K l e a ι κ P Q F hyp ?_, fun hyp => GlobalTheory.T.cokernel_torsionFree_of_bounded_leftInverse O K l e a ι κ P Q F hyp ?_⟩
  · rcases isEmpty_or_nonempty κ with hκ | ⟨⟨i0⟩⟩
    · intro τ
      exact ⟨hone, 0, ⟨0, fun _ j => isEmptyElim j⟩, Subsingleton.elim _ _⟩
    · obtain ⟨M₁, h₁⟩ := GlobalTheory.T.exists_E_pow_mul_frob_mem_rightDivisorSet O K l e a ι κ P Q F
      obtain ⟨M₂, h₂⟩ := GlobalTheory.T.exists_frobeniusSlice_mem_rightDivisorSet O K l e a ι κ P Q F
      refine GlobalTheory.T.one_mem_of_frobenius_linked_boundedSeries_ideals K l e a M₁ M₂ he hl0 hlK F.rdivSet (fun τ x hx y hy => Hom.rdivSet_add F τ hx hy)
        (fun τ x hx b hb => Hom.rdivSet_mul F τ hx b hb) (fun τ x hx => hx.1) ?_ h₁ h₂
      intro τ
      obtain ⟨Y, g, hY, hg, hFY⟩ := hyp τ
      have hgA : g ∈ A O K := by
        have : (F.mat τ * Y) i0 i0 = g := by rw [hFY]; simp
        rw [← this, Matrix.mul_apply]
        exact Subalgebra.sum_mem _ fun j _ => mul_mem (F.mem τ i0 j) (hY j i0)
      exact ⟨g, ⟨⟨1, mem_A.1 hgA⟩, Y, ⟨1, fun i j => mem_A.1 (hY i j)⟩, hFY⟩, mem_A.1 hgA, hg⟩
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
    · intro τ
      exact ⟨hone, 0, ⟨0, fun i _ => isEmptyElim i⟩, Subsingleton.elim _ _⟩
    · obtain ⟨M₁, h₁⟩ := GlobalTheory.T.frob_mem_leftDivisorSet_phiModuleHom O K l e a ι κ P Q F
      obtain ⟨M₂, h₂⟩ := GlobalTheory.T.frobeniusResidueSlice_mem_boundedLeftDivisorSet O K l e a ι κ P Q F
      refine GlobalTheory.T.one_mem_of_frobenius_linked_boundedSeries_ideals K l e a M₁ M₂ he hl0 hlK F.ldivSet (fun τ x hx y hy => Hom.ldivSet_add F τ hx hy)
        (fun τ x hx b hb => Hom.ldivSet_mul F τ hx b hb) (fun τ x hx => hx.1) ?_ h₁ h₂
      intro τ
      obtain ⟨Y, g, hY, hg, hFY⟩ := hyp τ
      have hgA : g ∈ A O K := by
        have : (Y * F.mat τ) i0 i0 = g := by rw [hFY]; simp
        rw [← this, Matrix.mul_apply]
        exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY i0 j) (F.mem τ j i0)
      exact ⟨g, ⟨⟨1, mem_A.1 hgA⟩, Y, ⟨1, fun i j => mem_A.1 (hY i j)⟩, hFY⟩, mem_A.1 hgA, hg⟩
