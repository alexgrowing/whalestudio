import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.HeisTransport

theorem actsD_heisLine_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ →
      ActsD (evI F) (M.heisLine B.ψ (mat g * u * (mat h).transpose)) (T f) (T f₁) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hB hX hW hM hWeil g hg h hh T hT hTi u hu f f₁ hf
  have hS := IsUWeilPair.isUSplitting hWeil
  set ψ := B.ψ with hψ
  set p : UA σ X.J × UA σ W.J := (g, h) with hp

  have hrest : ∀ (φ : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Af F) →
      Rest (evI F) (⇑φ) (fun x => g' (fun i => (x i).2)) := by
    intro φ g' hg'
    refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨φ, g', hg', rfl⟩⟩
    change g' (fun i => (x i + z i).2) = g' (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
  have hpure : ∀ (φ : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Af F) →
      om p (pureA F φ g') = pureA F (T φ) g' := fun φ g' hg' => hT φ _ (hrest φ g' hg')

  have h0 : ∀ v : Matrix (Fin n) (Fin d) (AE F E), ∀ t : ℝ, M.heisLine ψ v t 0 = 0 := by
    intro v t
    funext x
    simp [Model.heisLine, Darboux.rho, schr]

  obtain ⟨D, hD⟩ := GlobalTheory.HeisDer.derEx F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J) M.co hB.std
  have hSDD := (hD u hu f).1
  have hL := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₁ (D u f)
  have hAD : ActsD (evI F) (M.heisLine ψ u) f (D u f) := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (D u f) f₁).1 _ (h0 u) hSDD
  have hf₁ : f₁ = D u f := hL.2.2.1 _ hf hAD
  rw [← hf₁] at hSDD

  have himpl : ∀ t : ℝ, ∀ Φ ∈ schA F (Fin n × Fin d),
      M.heisLine ψ (mat g * u * (mat h).transpose) t (om p Φ) = om p (M.heisLine ψ u t Φ) := by
    intro t Φ hΦ
    have e := hS.impl p (realAd F t • u) Φ hΦ
    simp only [Model.heisLine]
    rw [e]
    congr 2
    simp only [actAB, hp, mat, Matrix.mul_smul, Matrix.smul_mul]

  have hSD : GlobalTheory.RealLift.SD (M.heisLine ψ (mat g * u * (mat h).transpose)) (T f) (T f₁) := by
    intro g' hg' l hl
    have hΦ : pureA F (⇑f) g' ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g', hg', rfl⟩
    have e : (fun t => l (M.heisLine ψ (mat g * u * (mat h).transpose) t (pureA F (⇑(T f)) g'))) =
        fun t => (l ∘ₗ om p) (M.heisLine ψ u t (pureA F (⇑f) g')) := by
      funext t
      rw [← hpure f g' hg', himpl t _ hΦ]
      rfl
    rw [e, ← hpure f₁ g' hg']
    exact hSDD g' hg' (l ∘ₗ om p) (hS.adm p l hl)
  exact (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (T f) (T f₁) (T f₁)).1 _ (h0 _) hSD

end GlobalTheory.HeisTransport
