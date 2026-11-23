import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundOfDualFamilies
import Lemmata.GeneralBFactLeftTerForm.Imports

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section RankSpanGen

variable {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

theorem span_den_gen (M : Submodule R V) (y : V) (hy : y ∈ Submodule.span K (M : Set V)) :
    ∃ s : R, s ≠ 0 ∧ s • y ∈ M := by
  first | exact Bl.general_b_fact_left_ter_form.goal1 .. | (apply Bl.general_b_fact_left_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_ter_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_ter_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_ter_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_ter_form.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M y hy | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M y | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V | exact @Bl.general_b_fact_left_ter_form.goal1 R K | exact @Bl.general_b_fact_left_ter_form.goal1 R

def toSpanG (M : Submodule R V) : M →ₗ[R] (Submodule.span K (M : Set V)) where
  toFun x := ⟨x.1, Submodule.subset_span x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance toSpanG_loc (M : Submodule R V) : IsLocalizedModule (nonZeroDivisors R) (toSpanG (K := K) M) := by
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · intro x
    have hx0 : (x : R) ≠ 0 := nonZeroDivisors.ne_zero x.2
    have hxK : algebraMap R K x ≠ 0 :=
      (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).2 hx0
    rw [Module.End.isUnit_iff]
    constructor
    · intro y z hyz
      simp only [Module.algebraMap_end_apply] at hyz
      rw [← algebraMap_smul K (x : R) y, ← algebraMap_smul K (x : R) z] at hyz
      exact smul_right_injective _ hxK hyz
    · intro y
      refine ⟨(algebraMap R K x)⁻¹ • y, ?_⟩
      simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul K (x : R), smul_smul, mul_inv_cancel₀ hxK, one_smul]
  · intro y
    obtain ⟨s, hs, hsy⟩ := span_den_gen (K := K) M y.1 y.2
    exact ⟨(⟨s • y.1, hsy⟩, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩), rfl⟩
  · intro x₁ x₂ h
    refine ⟨1, ?_⟩
    have : x₁ = x₂ := Subtype.ext (congrArg (fun z : Submodule.span K (M : Set V) => (z : V)) h)
    rw [this]

theorem finrank_eq_span_gen (M : Submodule R V) :
    Module.finrank R M = Module.finrank K (Submodule.span K (M : Set V)) := by
  unfold Module.finrank
  rw [IsLocalization.rank_eq K (nonZeroDivisors R) le_rfl]
  rw [(IsLocalizedModule.rank_eq (nonZeroDivisors R) le_rfl (toSpanG (K := K) M)).symm]

end RankSpanGen

def RestYbc : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p : ℕ) [Fact p.Prime] (ι : ℚ_[p] →+* KK O) (N r : ℕ) [NeZero r]
    (LL : ChainLetters N) (q : ℕ) (J : Fin q → ℕ) (M : Fin q → WithTop ℤ),
    ∀ y ∈ YjtZ O (r := r) LL J M,
      y ∈ Submodule.span (KK O) (map ι '' (Formalism.GM.M.YZ p (r := r) (gmL LL) J M : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])))

end Formalism.MainNotions.G.SymmetricFormBlocks

end
