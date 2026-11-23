import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryIntegralConjInvariantStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCoordFunMulEqSumStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasDerivAtMatrixExpEntryRealStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ToMKExpKEqMatrixExpRealStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivConjInvariantAverageEqStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.KFourierCoefficientRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSumCompactUnitaryFourierValueOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier
open MeasureTheory Matrix Formalism.REAL GlobalTheory.TypeSum

variable {n : ℕ}

theorem rder_mem (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d) (l : List (Mx n))
    (hl : ∀ X ∈ l, inK ε X) : rder ε l φ ∈ polyV ε d := by
  induction l with
  | nil => exact hφ
  | cons X l ih =>
    have h := (GlobalTheory.T.contDiff_matrixRightInvariantDerivative ε d _ (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) X (hl X List.mem_cons_self)).1
    exact h

theorem hs_mul_toMK (ε : Fin n → Bool) (y : Mx n) (k : KG ε) : hs (y * toMK k) = hs y :=
  ((hermitian_small_ball n ε).2 y _ k.2).1

theorem toMK_expK_mul (ε : Fin n → Bool) (X : Mx n) (hK : inK ε X) (t : ℝ) (x : KG ε) :
    toMK (expK ε X t * x) = NormedSpace.exp (t • X) * toMK x := by
  rw [toMK_mul, toMK_expK hK, Complex.coe_smul]

theorem summable_listSum {ι : Type} (U : List ι) (b : ι → ℕ → ℝ) (hb : ∀ u ∈ U, Summable (b u)) :
    Summable fun i => (U.map fun u => b u i).sum := by
  induction U with
  | nil => simpa using (summable_zero : Summable fun _ : ℕ => (0 : ℝ))
  | cons u U ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hb u List.mem_cons_self).add (ih fun v hv => hb v (List.mem_cons_of_mem _ hv))

theorem exists_rightKFourier : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ e : ℕ → (Formalism.REAL.KG ε → ℂ), (∀ i, Continuous (e i)) ∧
    (∀ i, KFinFun ε (e i)) ∧ ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → UMG ε f →
    ∃ (N : ℕ) (Φ : ℕ → List (Mx n) → Mx n → ℂ) (B : ℕ → ℕ → ℝ),
      (∀ i, ∀ y ∈ UJset ε, Φ i [] y = ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
      (∀ i (l : List (Mx n)), (∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ X : Mx n, X ∈ lieSet ε → Xᴴ = -X →
        ∀ y ∈ UJset ε, HasDerivAt (fun t : ℝ => Φ i l (y * NormedSpace.exp (t • X))) (Φ i (X :: l) y) 0) ∧
      (∀ i k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
        ∀ y ∈ UJset ε, ‖Φ i w y‖ ≤ B i k * (1 + hs y) ^ N) ∧
      (∀ k, Summable fun i => B i k) ∧
      ∀ y ∈ UJset ε, HasSum (fun i => ∫ k, e i k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (f y) := by
  intro n ε
  have hker : ∀ i, IsKer ε i (kerE ε i) := fun i => isKer_kerE (GlobalTheory.T.exists_compactUnitary_fourierKernel ε i)
  refine ⟨kerE ε, fun i => continuous_of_mem (hker i).1, fun i => kFinFun_of_mem (hker i).1, ?_⟩
  intro f hf hU
  obtain ⟨N, F, hF0, hFd, hFg⟩ := hU
  have hcF : ContinuousOn (F []) (UJset ε) := hf.congr fun g hg => hF0 g hg
  have hdec : ∀ u : List (Mx n), ∃ b : ℕ → ℝ, Summable b ∧ ((∀ X ∈ u, inK ε X) → ∀ i, ∀ y ∈ UJset ε,
      ‖∫ k, kerE ε i k * F u (y * toMK k) ∂(muK ε)‖ ≤ b i * (1 + hs y) ^ N) := by
    intro u
    by_cases hu : ∀ X ∈ u, inK ε X
    · obtain ⟨b, hb, hb'⟩ := GlobalTheory.T.kFourier_coefficient_rapid_decay ε N F hFd hFg hcF (kerE ε) hker u hu
      exact ⟨b, hb, fun _ => hb'⟩
    · exact ⟨0, summable_zero, fun h => absurd h hu⟩
  choose b hbs hbb using hdec
  choose U C hC0 hUK hC using GlobalTheory.T.rightDeriv_norm_le_finite_words_bound ε
  have hQ : ∀ i, ∀ y ∈ UJset ε, avgK ε (kerE ε i) f y ∈ polyV ε i := fun i y hy =>
    GlobalTheory.T.compactUnitaryAverage_mem_polyV ε i _ (hker i).1 f hf y hy
  have hbound : ∀ i m (w : List (Mx n)), w.length ≤ m → (∀ X ∈ w, X ∈ GlobalTheory.SmoothGlob.lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖rder ε w (avgK ε (kerE ε i) f y) 1‖ ≤ C m * ((U m).map fun u => b u i).sum * (1 + hs y) ^ N := by
    intro i m w hw hwX y hy
    have hwK : ∀ X ∈ w, inK ε X ∧ hs X ≤ 1 := fun X hX =>
      ⟨inK_of_skew (hwX X hX).1 (hwX X hX).2.1, (hwX X hX).2.2⟩
    have h1 := hC m i _ (hQ i y hy) w hw hwK
    have h2 : ((U m).map fun u => ‖rder ε u (avgK ε (kerE ε i) f y) 1‖).sum ≤
        ((U m).map fun u => b u i * (1 + hs y) ^ N).sum := by
      refine List.sum_le_sum fun u hu => ?_
      rw [GlobalTheory.T.compactUnitaryRightDeriv_conjInvariantAverage_eq ε N F hFd hFg f hf hF0 _ (continuous_of_mem (hker i).1) (GlobalTheory.T.compactUnitary_fourierKernel_conj_invariant ε i _ (hker i)) u (hUK m u hu) y hy]
      exact hbb u (hUK m u hu) i y hy
    rw [List.sum_map_mul_right] at h2
    calc _ ≤ _ := h1
      _ ≤ C m * (((U m).map fun u => b u i).sum * (1 + hs y) ^ N) := mul_le_mul_of_nonneg_left h2 (hC0 m)
      _ = _ := by ring
  refine ⟨N, fun i l y => rder ε l (avgK ε (kerE ε i) f y) 1,
    fun i m => C m * ((U m).map fun u => b u i).sum, ?_, ?_, hbound, ?_, ?_⟩
  · intro i y hy
    simp [avgK, toMK_one]
  · intro i l hl X hX hXs y hy
    have hK := inK_of_skew hX hXs
    have hlK : ∀ Y ∈ l, inK ε Y := fun Y hY => inK_of_skew (hl Y hY).1 (hl Y hY).2
    have hR := rder_mem ε i _ (hQ i y hy) l hlK
    have e1 : (fun t : ℝ => rder ε l (avgK ε (kerE ε i) f (y * NormedSpace.exp (t • X))) 1) =
        fun t : ℝ => rder ε l (avgK ε (kerE ε i) f y) (1 * expK ε X t) := by
      funext t
      rw [one_mul, ← mul_one (expK ε X t), ← rder_left ε l _ (expK ε X t) 1]
      congr 1
      funext x
      simp only [avgK]
      rw [toMK_expK_mul ε X hK t x]
      simp only [Matrix.mul_assoc]
    show HasDerivAt (fun t : ℝ => rder ε l (avgK ε (kerE ε i) f (y * NormedSpace.exp (t • X))) 1)
      (rder ε [X] (rder ε l (avgK ε (kerE ε i) f y)) 1) 0
    rw [e1]
    exact (GlobalTheory.T.contDiff_matrixRightInvariantDerivative ε i _ hR X hK).2 1
  · intro m
    exact (summable_listSum (U m) b fun u _ => hbs u).mul_left (C m)
  · intro y hy
    have key := GlobalTheory.T.hasSum_compactUnitaryFourier_value_one ε (kerE ε) hker (fun k => f (y * toMK k)) ?_ (fun i => C 0 * ((U 0).map fun u => b u i).sum * (1 + hs y) ^ N)
      (((summable_listSum (U 0) b fun u _ => hbs u).mul_left (C 0)).mul_right _) ?_
    · simpa [toMK_one] using key
    · exact hf.comp_continuous ((continuous_const.mul (continuous_toMK ε))) fun k => mul_mem_UJ hy (K_le_UJ k.2)
    · intro i k'
      have hyk : y * toMK k' ∈ UJset ε := mul_mem_UJ hy (K_le_UJ k'.2)
      have := hbound i 0 [] le_rfl (by simp) _ hyk
      rw [hs_mul_toMK] at this
      simpa [avgK, toMK_one, toMK_mul, Matrix.mul_assoc] using this

end GlobalTheory.KFourier

end
