import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsCuspHom
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TauNorm

theorem exists_bound {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] E) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B, ‖L B‖ ≤ c * ∑ i, ∑ j, ‖B i j‖ := by
  classical
  set c : ℝ := ∑ i, ∑ j, ‖L (Matrix.single i j (1 : ℂ))‖ with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c, hc0, fun B => ?_⟩
  have hB : L B = ∑ i, ∑ j, B i j • L (Matrix.single i j (1 : ℂ)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single B]
    simp [map_sum, ← map_smul, Matrix.smul_single]
  have hle : ∀ i j, ‖L (Matrix.single i j (1 : ℂ))‖ ≤ c := fun i j =>
    (Finset.single_le_sum (f := fun j => ‖L (Matrix.single i j (1 : ℂ))‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖L (Matrix.single i j (1 : ℂ))‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  rw [hB]
  calc ‖∑ i, ∑ j, B i j • L (Matrix.single i j (1 : ℂ))‖
      ≤ ∑ i, ∑ j, ‖B i j‖ * ‖L (Matrix.single i j (1 : ℂ))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_smul _ _).le))
    _ ≤ ∑ i, ∑ j, ‖B i j‖ * c :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hle i j) (norm_nonneg _)
    _ = c * ∑ i, ∑ j, ‖B i j‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exp_dOp_le {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B, P * B * Q ≠ 0 → Real.exp (GlobalTheory.Count.dOp (P * B * Q)) ≤ c * ∑ i, ∑ j, ‖B i j‖ := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun B => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * B * Q))
      map_add' := fun B B' => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun a B => by simp }
  obtain ⟨c, hc, h⟩ := exists_bound L
  refine ⟨c, hc, fun B hB => ?_⟩
  have hpos : 0 < ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * B * Q))‖ := by
    rw [norm_pos_iff]
    intro h0
    apply hB
    have h1 : Matrix.toEuclideanLin (P * B * Q) = 0 :=
      LinearMap.toContinuousLinearMap.injective (h0.trans (map_zero _).symm)
    exact Matrix.toEuclideanLin.injective (h1.trans (map_zero _).symm)
  unfold GlobalTheory.Count.dOp
  rw [Real.exp_log hpos]
  exact h B

theorem exp_mean_le {ι : Type} [Fintype ι] [Nonempty ι] (d : ι → ℝ) (K : ℝ) (h : ∀ v, Real.exp (d v) ≤ K) :
    Real.exp ((∑ v, d v) / Fintype.card ι) ≤ K := by
  obtain ⟨v₀, hv₀⟩ := Finite.exists_max d
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmean : (∑ v, d v) / Fintype.card ι ≤ d v₀ := by
    rw [div_le_iff₀ hcard]
    calc ∑ v, d v ≤ ∑ _v : ι, d v₀ := Finset.sum_le_sum fun v _ => hv₀ v
      _ = d v₀ * Fintype.card ι := by simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact (Real.exp_le_exp.2 hmean).trans (h v₀)

theorem card_places (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  have := I.cm.totReal
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := I.F)
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at h1 h2
  simp only [AutInst.f]
  omega

theorem inv_tau_mul_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 = 1) (K : ℝ)
    (h : ∀ v, Real.exp (GlobalTheory.Count.dOp (uMat (g.1 v))) ≤ K) :
    (GlobalTheory.Count.tau1 I (x * g))⁻¹ ≤ (GlobalTheory.Count.tau1 I x)⁻¹ * K := by
  have hK1 : g.2 ∈ I.Kset := by
    rw [hg]
    show ((1 : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
    simp only [OneMemClass.coe_one]
    exact one_mem _
  have hlog := GlobalTheory.TauLipschitz.log_trunc_le I hn x g hK1
  have hx := GlobalTheory.TauLipschitz.trunc_pos I hn x
  have hxg := GlobalTheory.TauLipschitz.trunc_pos I hn (x * g)
  have hmean : Real.exp (GlobalTheory.Dec.dSum I g.1 / I.f) ≤ K := by
    have := exp_mean_le (fun v => GlobalTheory.Count.dOp (uMat (g.1 v))) K h
    rw [card_places] at this
    simpa only [GlobalTheory.Dec.dSum] using this
  have hdiv : GlobalTheory.Count.tau1 I x / GlobalTheory.Count.tau1 I (x * g) ≤ K := by
    rw [← Real.exp_log (div_pos hx hxg), Real.log_div hx.ne' hxg.ne']
    exact (Real.exp_le_exp.2 (by linarith)).trans hmean
  rw [inv_mul_eq_div, le_div_iff₀ hx, inv_mul_eq_div]
  exact hdiv

theorem sum_le_normInf {D : D7} {V : HSp D}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (g : GA D V) (τ : D.what₂.Tau) :
    ∑ i, ∑ j, ‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g i j‖ ≤ normInf θ V g := by
  unfold Formalism.L2.Theta.normInf
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun τ => ∑ i, ∑ j, (‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
    (fun _ _ => by positivity) (Finset.mem_univ τ))
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    le_add_of_nonneg_right (norm_nonneg _)

theorem uMat_ne_zero (I : AutInst) (hn : 1 ≤ I.n) (g : I.GA) (v : InfinitePlace I.F) : uMat (g.1 v) ≠ 0 := by
  have : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  exact Units.ne_zero _

end GlobalTheory.TauNorm
