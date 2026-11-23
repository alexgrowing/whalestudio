import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearInPolynomialDatum
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.ThK.ThetaLinSum

theorem I_finset_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (ι : Type) [Fintype ι] (z : ι → ℂ) (Ψ : ι → (Fin a × Fin (a + a') → AF F) → ℂ), (∀ i, Ψ i ∈ GlobalTheory.ThK.PolData B G.M) →
      ∀ h, G.M.I om (∑ i, z i • Ψ i) h = ∑ i, z i * G.M.I om (Ψ i) h := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hKP hT ι _ z Ψ hΨ h
  have lin := GlobalTheory.ThK.ThetaLin.I_lin F E σ B a a' G X om om' hKP hT
  have h0 : G.M.I om 0 h = 0 := by
    have e := congrFun (lin 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1) h
    simp only [one_smul, add_zero, Pi.add_apply] at e
    linear_combination -e
  classical
  have key : ∀ s : Finset ι, (∑ i ∈ s, z i • Ψ i) ∈ GlobalTheory.ThK.PolData B G.M ∧
      G.M.I om (∑ i ∈ s, z i • Ψ i) h = ∑ i ∈ s, z i * G.M.I om (Ψ i) h := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨by simpa using Submodule.zero_mem _, by simpa using h0⟩
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      refine ⟨Submodule.add_mem _ (Submodule.smul_mem _ _ (hΨ j)) ih.1, ?_⟩
      have e := congrFun (lin (Ψ j) (hΨ j) _ ih.1 (z j)) h
      rw [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ih.2]
  exact (key Finset.univ).2

end GlobalTheory.ThK.ThetaLinSum
