import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.HeightCoset

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

theorem opNorm_le_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  refine (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _).trans ?_
  gcongr
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x) i = ∑ j, A i j * x j := rfl
  rw [this, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  gcongr
  exact PiLp.norm_apply_le x j

variable {D : D7}

theorem infMat_mul' (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (g * h) =
    HA.mat (AF D.host.F) D.sp.cm.sig V.gram g * HA.mat (AF D.host.F) D.sp.cm.sig V.gram h := rfl
  simp only [infMat, this, Units.val_mul]
  rw [Matrix.map_mul, Matrix.map_mul]

theorem infMat_one' (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) :
    infMat D.sp.cm.sig V.gram θ (1 : GA D V) = 1 := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (1 : GA D V) = 1 := rfl
  simp only [infMat, this, Units.val_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (finHom V g).1 := rfl

theorem finHt_mul (V : HSp D) (x g : GA D V) (hg : g ∈ GinfC V) (v) : finHt V v (x * g) = finHt V v x := by
  have h0 : finHom V g = 1 := hg
  have h1 : finMat D.sp.cm.sig V.gram (x * g) = finMat D.sp.cm.sig V.gram x := by
    rw [finMat_eq, finMat_eq, map_mul, h0, mul_one]
  have h2 : finMat D.sp.cm.sig V.gram (x * g)⁻¹ = finMat D.sp.cm.sig V.gram x⁻¹ := by
    rw [finMat_eq, finMat_eq, map_inv, map_inv, map_mul, h0, mul_one]
  simp only [finHt, finNorm, h1, h2]

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem infNorm_mul_le (τ : D.what₂.Tau) (x g : GA D V) :
    infNorm θ V τ (x * g) ≤ infNorm θ V τ x * infNorm θ V τ g := by
  unfold infNorm
  rw [infMat_mul', map_mul]
  exact nnnorm_mul_le _ _

theorem infHt_mul_le (τ : D.what₂.Tau) (x g : GA D V) :
    infHt θ V τ (x * g) ≤ infHt θ V τ x * infHt θ V τ g := by
  refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)) (max_le ?_ ?_)
  · refine (infNorm_mul_le θ V τ x g).trans (mul_le_mul' ?_ ?_) <;>
      exact le_max_of_le_right (le_max_left _ _)
  · rw [_root_.mul_inv_rev, mul_comm (infHt θ V τ x)]
    refine (infNorm_mul_le θ V τ g⁻¹ x⁻¹).trans (mul_le_mul' ?_ ?_) <;>
      exact le_max_of_le_right (le_max_right _ _)

theorem infNorm_le_normInf (τ : D.what₂.Tau) (g : GA D V) :
    (infNorm θ V τ g : ℝ) ≤ normInf θ V g ∧ (infNorm θ V τ g⁻¹ : ℝ) ≤ normInf θ V g := by
  have h : ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖)
      ≤ normInf θ V g :=
    Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  constructor
  · refine (opNorm_le_sum _).trans (le_trans ?_ h)
    gcongr
    exact le_add_of_nonneg_right (norm_nonneg _)
  · refine (opNorm_le_sum _).trans (le_trans ?_ h)
    gcongr
    exact le_add_of_nonneg_left (norm_nonneg _)

theorem infHt_le_normInf (hV : 0 < V.rank) (τ : D.what₂.Tau) (g : GA D V) :
    (infHt θ V τ g : ℝ) ≤ normInf θ V g := by
  obtain ⟨h1, h2⟩ := infNorm_le_normInf θ V τ g
  haveI : Nonempty (Fin V.rank) := ⟨⟨0, hV⟩⟩
  have h3 : infNorm θ V τ 1 = 1 := by
    unfold infNorm
    rw [infMat_one', map_one]
    exact nnnorm_one
  have h4 : (1 : ℝ) ≤ infNorm θ V τ g * infNorm θ V τ g⁻¹ := by
    have := infNorm_mul_le θ V τ g g⁻¹
    rw [mul_inv_cancel, h3] at this
    exact_mod_cast this
  have h5 : 1 ≤ normInf θ V g := by
    by_contra hc
    push_neg at hc
    have a0 := (infNorm θ V τ g).coe_nonneg
    have b0 := (infNorm θ V τ g⁻¹).coe_nonneg
    nlinarith
  unfold infHt
  push_cast
  exact max_le h5 (max_le h1 h2)

theorem infHt_rank_zero (hV : V.rank = 0) (τ : D.what₂.Tau) (g : GA D V) : infHt θ V τ g = 1 := by
  haveI : IsEmpty (Fin V.rank) := by rw [hV]; infer_instance
  have h : ∀ g, infNorm θ V τ g ≤ 1 := fun g => by
    have := opNorm_le_sum (infMat D.sp.cm.sig V.gram (θ τ) g)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact_mod_cast this.trans zero_le_one
  exact max_eq_left (max_le (h g) (h g⁻¹))

theorem height_mul_le (x g : GA D V) (hg : g ∈ GinfC V) :
    height θ V (x * g) ≤ height θ V x * ∏ τ, infHt θ V τ g := by
  unfold height
  simp only [finHt_mul V x g hg]
  rw [mul_right_comm, ← Finset.prod_mul_distrib]
  gcongr with τ
  exact infHt_mul_le θ V τ x g

theorem height_le_normInf_pow (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) :
    ∃ M : ℕ, ∀ x : GA D V, ∃ C : ℝ, ∀ g ∈ GinfC V,
      (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V (x * g) : ℝ) ≤ C * normInf θ V g ^ M := by
  rcases Nat.eq_zero_or_pos V.rank with hV | hV
  · refine ⟨0, fun x => ⟨height θ V x, fun g hg => ?_⟩⟩
    have := height_mul_le θ V x g hg
    simp only [infHt_rank_zero θ V hV, Finset.prod_const_one] at this
    rw [pow_zero]
    exact_mod_cast this
  · refine ⟨Fintype.card D.what₂.Tau, fun x => ⟨height θ V x, fun g hg => ?_⟩⟩
    have : (height θ V (x * g) : ℝ) ≤ height θ V x * ∏ τ, (infHt θ V τ g : ℝ) := by
      exact_mod_cast height_mul_le θ V x g hg
    refine this.trans ?_
    gcongr
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => NNReal.coe_nonneg _) fun τ _ => infHt_le_normInf θ V hV τ g

end GlobalTheory.SmoothForms.HeightCoset

end
