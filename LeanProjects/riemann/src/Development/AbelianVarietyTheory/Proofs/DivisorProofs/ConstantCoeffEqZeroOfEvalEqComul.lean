import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory

theorem constantCoeff_eq_zero_of_eval_eq_comul : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : O)}) O] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, constantCoeff (μ i) = 0 := by
  intro p O A _ _ _ _ d x E₂ μ hx hE hμ i
  let φ : A ⊗[O] A →ₐ[O] O := Algebra.TensorProduct.lift (Bialgebra.counitAlgHom O A)
    (Bialgebra.counitAlgHom O A) (fun _ _ => Commute.all _ _)
  have hφ : ∀ a b : A, φ (a ⊗ₜ[O] b) = Coalgebra.counit (R := O) a * Coalgebra.counit (R := O) b := by
    intro a b
    simp [φ, Algebra.TensorProduct.lift_tmul, Bialgebra.counitAlgHom_apply]

  have hφc : ∀ a : A, φ (Coalgebra.comul (R := O) a) = Coalgebra.counit (R := O) a := by
    intro a
    have hL : (φ.toLinearMap : A ⊗[O] A →ₗ[O] O) =
        (LinearMap.mul' O O) ∘ₗ (LinearMap.lTensor O (Coalgebra.counit (R := O) (A := A))) ∘ₗ
          (LinearMap.rTensor A (Coalgebra.counit (R := O) (A := A))) := by
      apply TensorProduct.ext'
      intro a b
      simp [hφ]
    have := LinearMap.congr_fun hL (Coalgebra.comul (R := O) a)
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul,
      LinearMap.lTensor_tmul, LinearMap.mul'_apply, one_mul] at this
    exact this
  let c : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] O :=
    { (constantCoeff : MvPowerSeries (Fin d ⊕ Fin d) O →+* O) with
      commutes' := fun r => by
        first
        | exact constantCoeff_C r
        | (rw [MvPowerSeries.algebraMap_apply]; simp)
        | (show constantCoeff (C r) = r; simp)
        | simp [MvPowerSeries.algebraMap_apply'] }
  have hc : ∀ f, c f = constantCoeff f := fun _ => rfl
  have hnil : ∀ j : Fin d ⊕ Fin d, ∃ N : ℕ, (p : O) ∣ (fun _ => (0 : O)) j ^ N :=
    fun _ => ⟨1, by simp⟩
  obtain ⟨⟨E, _, huniq⟩, _⟩ := GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O O (Fin d ⊕ Fin d) (fun _ => (0 : O)) hnil
  have h1 : IsEval p (fun _ => (0 : O)) (φ.comp E₂) := by
    refine ⟨?_, ?_⟩
    · intro j
      rw [AlgHom.comp_apply, hE.1 j]
      cases j with
      | inl k => simp [hφ, hx]
      | inr k => simp [hφ, hx]
    · intro m
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      obtain ⟨a, ha⟩ := hN f hf
      refine ⟨φ a, ?_⟩
      rw [AlgHom.comp_apply, ha, map_mul, map_pow, map_natCast]
  have h2 : IsEval p (fun _ => (0 : O)) c := by
    refine ⟨fun j => by simp [hc], fun m => ⟨1, fun f hf => ?_⟩⟩
    have : constantCoeff f = 0 := by
      have := hf 0 (by simp)
      simpa [coeff_zero_eq_constantCoeff_apply] using this
    rw [hc, this]; exact dvd_zero _
  have e1 := huniq _ h1
  have e2 := huniq _ h2
  have := congrArg (fun F : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] O => F (μ i)) (e1.trans e2.symm)
  simp only [AlgHom.comp_apply, hμ, hφc, hx, hc] at this
  exact this.symm

end GlobalTheory
