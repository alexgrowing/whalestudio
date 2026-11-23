import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumFockEquations
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveComplexStructureDarbouxPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFockFormOfComplexStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzCexpNegFormStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section
namespace GlobalTheory.GaussVacPair
open GlobalTheory.GaussFockJ GlobalTheory.ThK.EvAt0.PolD

theorem actsD_unique {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ f₂ : SInf F κ}
    (h1 : ActsD (evI F) T f f₁) (h2 : ActsD (evI F) T f f₂) : f₁ = f₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) κ
  ext y
  have hr := hR f
  let x : κ → AF F := fun i => liftA (y i)
  have hx : At (evI F) x := fun c hc => funext fun i => smul_liftA hc (y i)
  have e := (h1 R hr x).unique (h2 R hr x)
  have hRx : R x = R 0 := by
    have := hr.1 0 x hx
    rwa [zero_add] at this
  have hl : (fun i => evI F (x i)) = y := funext fun i => evI_liftA (y i)
  simp only [tens, hl, hRx] at e
  exact mul_right_cancel₀ hR0 e

theorem exists_gauss_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∃ g : SInf F (Fin n × Fin d), M.IsGauss B.ψ B.emb g ∧
      ∃ (Q : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ) (c : ℝ),
        0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ ∀ x, g x = Complex.exp (-(Q x x)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨J₀, hJJ, hJω, hJpos, hJrel⟩ := GlobalTheory.T.exists_positive_complex_structure_darboux_pair F E σ B n d X W M χX χW om r s r' s' hP
  have hsym : ∀ x y : (Fin n × Fin d → mixedEmbedding.mixedSpace F), GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x y = GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) y x := by
    intro x y
    simp only [GlobalTheory.GaussLine.pairInf_apply, mul_comm]
  obtain ⟨Q, c, hc, hQc, hQs, hQJ⟩ := GlobalTheory.T.exists_siegel_fock_form_of_complex_structure (Fin n × Fin d → mixedEmbedding.mixedSpace F) (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) J₀ hsym hJJ hJω hJpos
  obtain ⟨g, hg, hgd⟩ := GlobalTheory.T.exists_schwartz_eq_cexp_neg_form (Fin n × Fin d → mixedEmbedding.mixedSpace F) Q c hc hQc
  refine ⟨g, ⟨fun _ => 1, ?_⟩, Q, c, hc, hQc, hg⟩
  intro u u' hu hu' hrel f f' hf hf'
  have hrel' : ∀ w, u'.map (piInf (B.emb w)) = Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ) := by
    intro w
    rw [hrel w]
    simp
  have key : ∀ v : Matrix (Fin n) (Fin d) (AE F E), At (evI F) v → ∀ h : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ v) g h → ∀ x, h x = GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (Psi M v) g x := by
    intro v hv h hh x
    have h0 := actsD_Phi hψ M (Psi M v) g
    rw [Phi_Psi M hv] at h0
    rw [actsD_unique hh h0, dHeis_eq_dOp]
  have hJ : Psi M u' = J₀ (Psi M u) := hJrel u u' hu hu' hrel'
  have hd : ∀ (w : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) x, GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) w g x =
      -2 * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x w.2 : ℂ)) * g x := by
    intro w x
    rw [GlobalTheory.GaussLine.dHeis, hgd x w.1, hQs w.1 x]
    ring
  ext x
  rw [SchwartzMap.smul_apply, key u' hu' f' hf' x, key u hu f hf x, hJ, hd, hd, hQJ, smul_eq_mul]
  ring

end GlobalTheory.GaussVacPair
