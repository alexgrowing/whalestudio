import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.ExistsUniqueComplexification
import Formalism.PeriodIntegrals.IsLowUnitH

namespace CompanionTheory.D.Upq

open Matrix NormedSpace PI.UpqRep
open scoped Matrix.Norms.L2Operator Manifold

section General

variable {m : Type*} [Fintype m] [DecidableEq m] {J : Matrix m m ℂ}

theorem exp_conj_J (hJJ : J * J = 1) (X : Matrix m m ℂ) : exp (J * X * J) = J * exp X * J := by
  have hu : IsUnit J := ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩
  have hinv : J⁻¹ = J := inv_eq_left_inv hJJ
  have := Matrix.exp_conj J X hu
  rwa [hinv] at this

theorem exp_mul_exp_neg' (X : Matrix m m ℂ) : exp X * exp (-X) = 1 :=
  (expUnit ℝ (Matrix m m ℂ) X).mul_inv

theorem exp_neg_mul_exp' (X : Matrix m m ℂ) : exp (-X) * exp X = 1 :=
  (expUnit ℝ (Matrix m m ℂ) X).inv_mul

theorem isExpLieAlgebra_of_J (hJJ : J * J = 1) (G : Subgroup (Matrix m m ℂ)ˣ)
    (hG : ∀ g : (Matrix m m ℂ)ˣ, g ∈ G ↔ (g : Matrix m m ℂ)ᴴ * J * g = J) :
    IsExpLieAlgebra G (lieJ J) where
  expUnit_mem X hX := by
    have h1 : -(J * X * J) = J * (-X) * J := by rw [Matrix.mul_neg, Matrix.neg_mul]
    rw [hG, coe_expUnit, ← Matrix.exp_conjTranspose, (mem_lieJ_iff hJJ).1 hX, h1, exp_conj_J hJJ,
      mul_J_J hJJ (J * exp (-X)), Matrix.mul_assoc, exp_neg_mul_exp', Matrix.mul_one]
  exists_nhds := by
    obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 (expPartialHomeomorph ℝ (Matrix m m ℂ)).open_source
      (0 : Matrix m m ℂ) (zero_mem_expPartialHomeomorph_source ℝ (Matrix m m ℂ))
    refine ⟨Metric.ball (0 : Matrix m m ℂ) ε ∩
      (fun X : Matrix m m ℂ => Xᴴ) ⁻¹' Metric.ball (0 : Matrix m m ℂ) ε ∩
      (fun X : Matrix m m ℂ => -(J * X * J)) ⁻¹' Metric.ball (0 : Matrix m m ℂ) ε, ?_, ?_, ?_, ?_⟩
    · exact (Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage
        continuous_id.matrix_conjTranspose)).inter (Metric.isOpen_ball.preimage
        ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).neg)
    · refine ⟨⟨Metric.mem_ball_self εpos, ?_⟩, ?_⟩ <;>
        simpa using Metric.mem_ball_self (x := (0 : Matrix m m ℂ)) εpos
    · exact fun X hX => hε hX.1.1
    · intro X hX hGX
      rw [hG, coe_expUnit] at hGX
      rw [mem_lieJ_iff hJJ]
      have h1 : (exp X)ᴴ = J * exp (-X) * J := by
        calc (exp X)ᴴ = (exp X)ᴴ * J * (exp X * exp (-X)) * J := by
              rw [exp_mul_exp_neg', Matrix.mul_one, mul_J_J hJJ]
          _ = (exp X)ᴴ * J * exp X * exp (-X) * J := by simp only [Matrix.mul_assoc]
          _ = J * exp (-X) * J := by rw [hGX]
      have h2 : exp Xᴴ = exp (-(J * X * J)) := by
        rw [Matrix.exp_conjTranspose, h1, show -(J * X * J) = J * (-X) * J by
          rw [Matrix.mul_neg, Matrix.neg_mul], exp_conj_J hJJ]
      exact (expPartialHomeomorph ℝ (Matrix m m ℂ)).injOn (hε hX.1.2) (hε hX.2) h2

end General

section UJ

variable {n : ℕ} (ε : Fin n → Bool)

theorem mem_UJ_iff (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    g ∈ UJ ε ↔ (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * g = Jm ε := Iff.rfl

theorem isExpLieAlgebra_UJ : IsExpLieAlgebra (UJ ε) (lieJ (Jm ε)) :=
  isExpLieAlgebra_of_J (Jm_mul_self ε) _ (mem_UJ_iff ε)

noncomputable instance chartedSpace_UJ : ChartedSpace (lieJ (Jm ε)) (UJ ε) :=
  (isExpLieAlgebra_UJ ε).chartedSpace

instance lieGroup_UJ (k : WithTop ℕ∞) : LieGroup 𝓘(ℝ, lieJ (Jm ε)) k (UJ ε) :=
  (isExpLieAlgebra_UJ ε).lieGroup k

theorem isCompact_Kset : IsCompact (Kset ε) := by
  have hcl : IsClosed (Kset ε) := by
    refine IsClosed.inter ?_ ?_
    · have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
          {u | star u * u = 1} := by ext u; exact Matrix.mem_unitaryGroup_iff'
      rw [this]
      exact isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const
    · exact isClosed_eq (continuous_id.matrix_mul continuous_const)
        (continuous_const.matrix_mul continuous_id)
  have hB : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hB.of_isClosed_subset hcl ?_
  rintro u ⟨hu, -⟩ i - j -
  simpa using entry_norm_bound_of_unitary hu i j

theorem isCompact_KG : IsCompact (KG ε : Set (UJ ε)) := by
  have hE := (isClosedEmbeddingMatrix n ε).1
  have : (KG ε : Set (UJ ε)) = (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
      Matrix (Fin n) (Fin n) ℂ)) ⁻¹' Kset ε := rfl
  rw [this]
  exact hE.isCompact_preimage (isCompact_Kset ε)

instance compactSpace_KG : CompactSpace (KG ε) :=
  isCompact_iff_compactSpace.1 (isCompact_KG ε)

end UJ

end CompanionTheory.D.Upq
