import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.NormInf

theorem entrySum_mul_le {n : Type} [Fintype n] (A B : Matrix n n ℂ) :
    ∑ i, ∑ j, ‖(A * B) i j‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ∑ i, ∑ j, ‖B i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j, ‖(A * B) i j‖ ≤ ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ k, ‖A i k‖ * ∑ j, ‖B k j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun k => ∑ j, ‖B k j‖)
          (fun k _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)

theorem norm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n)‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  refine le_trans (le_of_eq ?_) (PiLp.norm_apply_le _ i)
  congr 1
  change _ = (A *ᵥ Pi.single j 1) i
  simp

theorem sum_mul_add_le {ι : Type} [Fintype ι] (a b c d : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i) :
    ∑ i, (a i * c i + d i * b i) ≤ (∑ i, (a i + b i)) * ∑ i, (c i + d i) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : c i + d i ≤ ∑ i, (c i + d i) :=
    Finset.single_le_sum (f := fun i => c i + d i) (fun i _ => add_nonneg (hc i) (hd i)) (Finset.mem_univ i)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h (add_nonneg (ha i) (hb i)))
  nlinarith [mul_nonneg (ha i) (hd i), mul_nonneg (hb i) (hc i)]

theorem infMat_mul' {D : D7} (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (g * h) =
    HA.mat (AF D.host.F) D.sp.cm.sig V.gram g * HA.mat (AF D.host.F) D.sp.cm.sig V.gram h := rfl
  simp only [infMat, this, Units.val_mul]
  rw [Matrix.map_mul, Matrix.map_mul]

theorem infHt_le_height {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau) (g : GA D V) : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ V τ g ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height
  refine le_trans ?_ (le_mul_of_one_le_right' (one_le_finprod' fun _ => le_max_left _ _))
  exact Finset.single_le_prod' (f := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ V τ g)
    (fun _ _ => le_max_left _ _) (Finset.mem_univ τ)

end GlobalTheory.SmoothForms.NormInf

namespace GlobalTheory.SmoothForms

open NormInf in

theorem normInf_mul_le_and_le_height :
    ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
      (∀ g h : GA D V, normInf θ V (g * h) ≤ normInf θ V g * normInf θ V h) ∧
        ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := by
  intro D θ V
  refine ⟨fun g h => ?_, ⟨∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (2 : ℝ), fun g => ?_⟩⟩
  · unfold normInf
    simp only [Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin V.rank)))]
    have hn : ∀ (x : GA D V) τ, 0 ≤ ∑ i, ∑ j, ‖infMat D.sp.cm.sig V.gram (θ τ) x i j‖ := fun x τ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine le_trans ?_ (sum_mul_add_le _ _ _ _ (hn g) (hn g⁻¹) (hn h) (hn h⁻¹))
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [_root_.mul_inv_rev, infMat_mul', infMat_mul']
    exact add_le_add (entrySum_mul_le _ _) (entrySum_mul_le _ _)
  · unfold normInf
    simp only [Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h0 := infHt_le_height θ V τ g
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V τ g ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans h0
    have h2 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V τ g⁻¹ ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans h0
    have h3 := (norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g) i j).trans (NNReal.coe_le_coe.2 h1)
    have h4 := (norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹) i j).trans (NNReal.coe_le_coe.2 h2)
    linarith

end GlobalTheory.SmoothForms
