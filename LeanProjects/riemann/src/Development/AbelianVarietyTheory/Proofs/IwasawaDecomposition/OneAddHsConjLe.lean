import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeSum.GrowthAtPlace

open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace

variable {n : ℕ} {ε : Fin n → Bool} {P G : Mx n}

theorem norm_entry_le (A : Mx n) (i j : Fin n) : ‖A i j‖ ≤ 1 + hs A := by
  have h : ‖A i j‖ ^ 2 ≤ hs A :=
    (Finset.single_le_sum (f := fun b => ‖A i b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, ‖A a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))
  nlinarith [norm_nonneg (A i j)]

theorem one_add_hs_conj_le (Q y P : Mx n) : 1 + hs (Q * y * P) ≤ (1 + hs Q) * (1 + hs P) * (1 + hs y) := by
  have h1 := one_add_hs_mul_le (Q * y) P
  have h2 := mul_le_mul_of_nonneg_right (one_add_hs_mul_le Q y) (show 0 ≤ 1 + hs P by linarith [hs_nonneg P])
  nlinarith

theorem conj_mul (hP : IsUnit P) (a b : Mx n) : P⁻¹ * (a * b) * P = (P⁻¹ * a * P) * (P⁻¹ * b * P) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  calc P⁻¹ * (a * b) * P = P⁻¹ * a * (P * P⁻¹) * b * P := by
        rw [Matrix.mul_nonsing_inv _ hd]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem conj_exp (hP : IsUnit P) (X : Mx n) (t : ℝ) :
    P⁻¹ * NormedSpace.exp (t • X) * P = NormedSpace.exp (t • (P⁻¹ * X * P)) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  rw [Matrix.mul_assoc, exp_mul_eq hP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

theorem conj_lie (hP : IsUnit P) (h : Pᴴ * Jm ε * P = G) {X : Mx n} (hX : X ∈ lieSet ε) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * Xᴴ * (P * P⁻¹)ᴴ * Jm ε * P + Pᴴ * Jm ε * (P * P⁻¹) * X * P := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * (Xᴴ * Jm ε + Jm ε * X) * P := by
        rw [Matrix.mul_nonsing_inv _ hd]
        simp only [conjTranspose_one, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [h1, Matrix.mul_zero, Matrix.zero_mul]

theorem normInf_atTau_le {D : D7} {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {ε : Fin V.rank → Bool} {P : Mx V.rank} (hP : IsUnit P) (h : Pᴴ * Jm ε * P = gramAt D V τ) :
    ∃ c : ℝ, ∀ y ∈ UJset ε, normInf θ V (atTau θ V τ (P⁻¹ * y * P)) ≤ c * (1 + hs y) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  set K : ℝ := (1 + hs P⁻¹) * (1 + hs P) + (1 + hs (1 : Mx V.rank)) with hK
  refine ⟨∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (K + K), fun y hy => ?_⟩
  have hs1 := hs_nonneg (1 : Mx V.rank)
  have hsy := hs_nonneg y
  have hPP : 0 ≤ (1 + hs P⁻¹) * (1 + hs P) := mul_nonneg (by linarith [hs_nonneg P⁻¹]) (by linarith [hs_nonneg P])
  have b1 : ∀ z : Mx V.rank, hs z = hs y → 1 + hs (P⁻¹ * z * P) ≤ K * (1 + hs y) := fun z hz => by
    have := one_add_hs_conj_le P⁻¹ z P
    rw [hz] at this
    nlinarith
  have b2 : 1 + hs (1 : Mx V.rank) ≤ K * (1 + hs y) := by nlinarith
  have sp := atTau_spec hθ V τ (conj_inv_mem hP h hy)
  unfold normInf
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun τ' _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have e := infMat_mul_inv θ V τ' (atTau θ V τ (P⁻¹ * y * P))
  rw [add_mul]
  refine add_le_add ((norm_entry_le _ i j).trans ?_) ((norm_entry_le _ i j).trans ?_)
  · by_cases c : τ' = τ
    · subst c
      rw [sp.2.1]
      exact b1 y rfl
    · rw [sp.2.2 τ' c]
      exact b2
  · by_cases c : τ' = τ
    · subst c
      rw [sp.2.1] at e
      have e2 : (P⁻¹ * y⁻¹ * P) * (P⁻¹ * y * P) = 1 := by
        rw [← conj_mul hP, inv_mul_UJ hy, Matrix.mul_one, Matrix.nonsing_inv_mul _ hd]
      rw [← left_inv_eq_right_inv e2 e]
      exact b1 _ (hs_inv hy)
    · rw [sp.2.2 τ' c, Matrix.one_mul] at e
      rw [e]
      exact b2

theorem umg_atTau : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ (ε : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ → ∀ x : GA D V, GlobalTheory.TypeSum.UMG ε (fun y => φ (x * atTau θ V τ (P⁻¹ * y * P))) := by
  intro D θ hθ V τ φ hφ ε P hP h x
  obtain ⟨N, hN⟩ := hφ.growth
  obtain ⟨c, hc⟩ := normInf_atTau_le hθ V τ hP h
  have hl : ∀ l : List (Mx V.rank), (∀ Y ∈ l, Y ∈ lieSet ε) →
      ∀ p ∈ l.map fun X => (τ, P⁻¹ * X * P), p.2 ∈ lieAt V p.1 := fun l hl p hp => by
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hp
    exact conj_lie hP h (hl Y hY)
  refine ⟨N, fun l y => ((l.map fun X => (τ, P⁻¹ * X * P)).foldr (fun p f => Rder θ V p.1 p.2 f) φ)
    (x * atTau θ V τ (P⁻¹ * y * P)), fun _ _ => rfl, fun l hl' X hX g hg => ?_, fun l hl' => ?_⟩
  · have hs := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Mx V.rank => Rder θ V p.1 p.2) _
      fun p hp => linOnSm_Rder (hl l hl' p hp)).mem φ hφ.smooth
    have hd := (differentiable_oneP hs (τ := τ) (conj_lie hP h hX) (x * atTau θ V τ (P⁻¹ * g * P)) 0).hasDerivAt
    refine HasDerivAt.congr_of_eventuallyEq hd (Filter.Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP h hg) (conj_inv_mem hP h (exp_mem_UJ hX t)), conj_exp hP,
      ← mul_assoc]
    rfl
  · obtain ⟨C, hC⟩ := hN _ (hl l hl') x
    refine ⟨|C| * c ^ N, fun g hg => (hC _ (atTau_mem V τ _)).trans ?_⟩
    have h0 := normInf_nonneg (θ := θ) (atTau θ V τ (P⁻¹ * g * P))
    rw [mul_assoc |C|, ← mul_pow]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ h0 (hc g hg) N) (pow_nonneg h0 _) (abs_nonneg _)

end GlobalTheory.TypeSum.GrowthAtPlace

end
