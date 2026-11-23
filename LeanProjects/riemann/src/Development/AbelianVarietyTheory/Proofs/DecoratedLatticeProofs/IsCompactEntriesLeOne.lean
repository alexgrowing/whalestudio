import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentitiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInvertibleFamilyEvalSpanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorFiniteDimensionalStablStatement
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJInf
variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem continuous_lin_mvZ {T : Type} [TopologicalSpace T] (g : T → ι → Matrix (Fin a) (Fin a) ℂ)
    (hg : Continuous g) (h : ι → Matrix (Fin b) (Fin b) ℂ) (P : FP ι a b) :
    ∀ Λ : FP ι a b →ₗ[ℂ] ℂ, Continuous fun x => Λ (mvZ (g x) h P) := by
  induction P using MvPolynomial.induction_on with
  | C c => intro Λ; simp only [mvZ, aeval_C, algebraMap_eq]; exact continuous_const
  | add p q hp hq => intro Λ; simp only [map_add]; exact (hp Λ).add (hq Λ)
  | mul_X p v hp =>
    intro Λ
    have key : ∀ x, Λ (mvZ (g x) h (p * X v)) = ∑ i, ∑ j, (h v.1 i v.2.1 * g x v.1 v.2.2 j) *
        (Λ ∘ₗ LinearMap.mulRight ℂ (X (v.1, i, j))) (mvZ (g x) h p) := by
      intro x
      rw [map_mul]
      conv_lhs => rw [show mvZ (g x) h (X v) = ∑ i, ∑ j, C (h v.1 i v.2.1 * g x v.1 v.2.2 j) * X (v.1, i, j) by simp [mvZ, aeval_X]]
      simp only [Finset.mul_sum, map_sum, LinearMap.comp_apply, LinearMap.mulRight_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [C_mul', mul_smul_comm, map_smul, smul_eq_mul]
    simp_rw [key]
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    refine Continuous.mul (continuous_const.mul ?_) (hp _)
    exact ((continuous_apply j).comp ((continuous_apply v.2.2).comp ((continuous_apply v.1).comp hg)))

theorem continuous_evalAt_mul (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ => evalAt (fun τ => u τ * y τ) F := by
  unfold evalAt
  refine (MvPolynomial.continuous_eval F).comp (continuous_pi fun x => ?_)
  exact (((continuous_apply x.1).matrix_mul continuous_const).matrix_elem x.2.1 x.2.2)

theorem isCompact_entries_le_one :
    IsCompact {u : ι → Matrix (Fin a) (Fin a) ℂ | ∀ τ i j, ‖u τ i j‖ ≤ 1} := by
  have : {u : ι → Matrix (Fin a) (Fin a) ℂ | ∀ τ i j, ‖u τ i j‖ ≤ 1} =
      Set.univ.pi fun _ : ι => (Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a => Metric.closedBall (0:ℂ) 1 : Set (Matrix (Fin a) (Fin a) ℂ)) := by
    ext u
    constructor
    · intro hu τ _ i _ j _
      have := hu τ i j
      show dist (u τ i j) 0 ≤ 1
      simpa using this
    · intro hu τ i j
      have : dist (u τ i j) 0 ≤ 1 := hu τ trivial i trivial j trivial
      simpa using this
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem subY_eq_sum_averages : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b) (lam : ι → DomWeight a) (n : ι → ℕ) (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] (r : K → ι → Matrix (Fin a) (Fin a) ℂ), OntoUni r → ∀ y' : ι → Matrix (Fin b) (Fin b) ℂ, ∃ (m : ℕ) (y : Fin m → ι → Matrix (Fin a) (Fin a) ℂ) (P : Fin m → FP ι a b), (∀ j, IsInv (y j)) ∧ ∀ F ∈ Vn lam n, ∀ Λ : FP ι a b →ₗ[ℂ] ℂ, ∑ j, ∫ k, Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F ∂ν = Λ (subY hab y' F) := by
  intro ι _ a b hab lam n K _ _ _ _ _ ν _ r hr y'
  obtain ⟨m, y, P, hy, hT⟩ := GlobalTheory.T.exists_invertibleFamily_eval_span ι a lam n (FP ι a b) (subY hab y').toLinearMap
  refine ⟨m, y, P, hy, ?_⟩
  intro F hF Λ
  obtain ⟨h1, -, -, h4, h5, h6, -, -⟩ := GlobalTheory.T.fockSubstitution_identities ι a b hab
  have vn := (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable ι a lam n).2
  have hstar : ∀ k τ, star (r k τ) * r k τ = 1 := fun k τ => (Matrix.mem_unitaryGroup_iff').1 (hr.uni k τ)
  have hstar' : ∀ k τ, r k τ * star (r k τ) = 1 := fun k τ => (Matrix.mem_unitaryGroup_iff).1 (hr.uni k τ)
  have hinv : ∀ k τ, (r k τ)⁻¹ = star (r k τ) := fun k τ => Matrix.inv_eq_left_inv (hstar k τ)
  have hpt : ∀ k, ∑ j, Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F
      = Λ (subY hab y' F) := by
    intro k
    have hG : subY hab y' (lft (r k) F) = ∑ j, evalAt (y j) (lft (r k) F) • P j := hT _ (vn (r k) F hF)
    have e1 : mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (subY hab y' (lft (r k) F)) = subY hab y' F := by
      rw [h1, h4]
      have ha : (fun τ => r k τ * (r k τ)⁻¹) = fun _ => (1 : Matrix (Fin a) (Fin a) ℂ) := by
        funext τ; rw [hinv, hstar']
      have hb : (fun τ => (1 : Matrix (Fin b) (Fin b) ℂ) * y' τ) = y' := by funext τ; simp
      rw [ha, hb, h5]
    rw [← e1, hG, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, h6, mul_comm]
  have hst : Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ => fun τ => star (u τ) := continuous_pi fun τ => (continuous_apply τ).star
  have hcont : ∀ j, Continuous fun u : ι → Matrix (Fin a) (Fin a) ℂ =>
      Λ (mvZ (fun τ => star (u τ)) (fun _ => 1) (P j)) * evalAt (fun τ => u τ * y j τ) F := fun j => by
    have e1 := continuous_lin_mvZ (fun u : ι → Matrix (Fin a) (Fin a) ℂ => fun τ => star (u τ)) hst (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) (P j) Λ
    exact e1.mul (continuous_evalAt_mul (y j) F)
  have hint : ∀ j ∈ Finset.univ, Integrable (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) *
      evalAt (fun τ => r k τ * y j τ) F) ν := by
    intro j _
    have hfun : (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) (P j)) * evalAt (fun τ => r k τ * y j τ) F)
        = (fun u : ι → Matrix (Fin a) (Fin a) ℂ =>
          Λ (mvZ (fun τ => star (u τ)) (fun _ => 1) (P j)) * evalAt (fun τ => u τ * y j τ) F) ∘ r := by
      funext k; simp only [Function.comp_apply, hinv]
    rw [hfun]
    obtain ⟨C, hC⟩ := (isCompact_entries_le_one (ι := ι) (a := a)).exists_bound_of_continuousOn (hcont j).continuousOn
    refine Integrable.of_bound ((hcont j).comp hr.cont).aestronglyMeasurable C (Filter.Eventually.of_forall fun k => ?_)
    exact hC _ fun τ i i' => entry_norm_bound_of_unitary (hr.uni k τ) i i'
  rw [← integral_finset_sum _ hint]
  simp_rw [hpt]
  simp

end GlobalTheory.KJInf

end
