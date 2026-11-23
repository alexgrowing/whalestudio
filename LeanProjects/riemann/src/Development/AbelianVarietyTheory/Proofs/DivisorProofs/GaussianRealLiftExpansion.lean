import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzLogDerivativeGaussianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairExistsArchimedeanTranslatesStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.VacGauss

def trL {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ where
  toFun x := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * b i)
  map_add' x y := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add]
  map_smul' c x := by simp [smul_mul_assoc, ← Finset.smul_sum]

open scoped Classical in

theorem fock_vacuum_gaussian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.ActsLaws →
    ∀ f₀ : SInf F (Fin n × Fin d), f₀ ≠ 0 → M.IsGauss B.ψ B.emb f₀ →
    ∃ (Q : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℂ)
      (z : ℂ), (∀ x, x ≠ 0 → 0 < (Q x x).re) ∧ ∀ x, f₀ x = z * Complex.exp (-(Q x x)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP hDer hLaws f₀ hf₀ ⟨ε, hε⟩
  obtain ⟨D, hD⟩ := hDer F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ (incM F X.J) (incM F W.J) M.co hP.base.std
  have hz0 : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ), M.heisLine B.ψ u t 0 = 0 := by
    intro u t; funext x; simp [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  have act : ∀ u, At (evI F) u → ActsD (evI F) (M.heisLine B.ψ u) f₀ (D u f₀) := fun u hu =>
    (hLaws F (Fin n × Fin d) f₀ (D u f₀) (D u f₀)).1 _ (hz0 u) (hD u hu f₀).1
  choose u u' hu hu' hrel ha ha' using GlobalTheory.T.pair_exists_archimedean_translates F E σ B n d X W M χX χW om r s r' s' hP ε
  have key : ∀ α x, fderiv ℝ (⇑f₀) x α = ((2 * Real.pi * Complex.I) *
      (trL (fun i => evI F ((M.co.e (u' α)).2 i)) x : ℂ) +
      2 * Real.pi * (trL (fun i => evI F ((M.co.e (u α)).2 i)) x : ℂ)) * f₀ x := by
    intro α x
    have h := hε (u α) (u' α) (hu α) (hu' α) (hrel α) _ _ (act _ (hu α)) (act _ (hu' α))
    have h2 := congrArg (fun g : SInf F (Fin n × Fin d) => g x) h
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
    rw [(hD _ (hu α) f₀).2 x, (hD _ (hu' α) f₀).2 x] at h2
    have e1 : (fun i => evI F ((M.co.e (u α)).1 i)) = 0 := funext (ha α)
    have e2 : (fun i => evI F ((M.co.e (u' α)).1 i)) = α := funext (ha' α)
    rw [e1, e2, map_zero] at h2
    show _ = ((2 * Real.pi * Complex.I) *
      ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((M.co.e (u' α)).2 i)) : ℝ) : ℂ) +
      2 * Real.pi * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((M.co.e (u α)).2 i)) : ℝ) : ℂ)) * f₀ x
    linear_combination h2 - (2 * Real.pi * (((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (∑ i, x i * evI F ((M.co.e (u α)).2 i)) : ℝ) : ℂ)) * f₀ x) * Complex.I_sq
  exact GlobalTheory.T.schwartz_log_derivative_gaussian f₀ hf₀ (fun α => (2 * Real.pi * Complex.I) • Complex.ofRealCLM.toLinearMap.comp
      (trL (fun i => evI F ((M.co.e (u' α)).2 i))) +
    ((2 * Real.pi : ℝ) : ℂ) • Complex.ofRealCLM.toLinearMap.comp (trL (fun i => evI F ((M.co.e (u α)).2 i))))
    (fun x α => by
      rw [key α x]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        Complex.ofRealCLM_apply, smul_eq_mul]
      push_cast; ring)

end GlobalTheory.VacGauss
