import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalPartStabilizerStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.LemF.ConePass

theorem linear_iterated_integral {α β Y : Type} [MeasurableSpace α] [MeasurableSpace β] (μK : Measure α) (μ : Measure β)
    {N : ℕ} (f : Fin N → Y → ℂ) (c : Fin N → α → β → ℂ) (h1 : ∀ i k, Integrable (c i k) μ)
    (h2 : ∀ i, Integrable (fun k => ∫ t, c i k t ∂μ) μK) (g : α → β → Y → ℂ)
    (hg : ∀ k t y, g k t y = ∑ i, c i k t * f i y) (l : (Y → ℂ) →ₗ[ℂ] ℂ) :
    l (fun y => ∫ k, ∫ t, g k t y ∂μ ∂μK) = ∫ k, ∫ t, l (g k t) ∂μ ∂μK := by
  have key : ∀ s : Fin N → ℂ, ∫ k, ∫ t, ∑ i, c i k t * s i ∂μ ∂μK = ∑ i, (∫ k, ∫ t, c i k t ∂μ ∂μK) * s i := fun s => by
    have e : ∀ k, ∫ t, ∑ i, c i k t * s i ∂μ = ∑ i, (∫ t, c i k t ∂μ) * s i := fun k => by
      rw [integral_finsetSum _ fun i _ => (h1 i k).mul_const (s i)]
      exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
    simp only [e]
    rw [integral_finsetSum _ fun i _ => (h2 i).mul_const (s i)]
    exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
  have e1 : (fun y => ∫ k, ∫ t, g k t y ∂μ ∂μK) = ∑ i, (∫ k, ∫ t, c i k t ∂μ ∂μK) • f i := by
    funext y
    simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact key fun i => f i y
  have e2 : ∀ k t, l (g k t) = ∑ i, c i k t * l (f i) := fun k t => by
    have : g k t = ∑ i, c i k t • f i := by
      funext y
      simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [this, map_sum]
    simp only [map_smul, smul_eq_mul]
  simp only [e2]
  rw [e1, key, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem linear_coneFin_eq : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ l : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        l (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ) =
          ∫ k, coneLin B G.M' om' v (ev' v) μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l φ k.1 ∂μK := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he ei' ev' hl K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ l φ hφ
  obtain ⟨N, f, c, -, h1, h2, h3⟩ := GlobalTheory.T.config_b_local_part_stabilizer hP F E σ B a b G G₁ H H' hC e' he ei' ev' hl K hK X om om' om₁ om₁'
    hT hT₁ v μK μ hμK hμ ((a - (b + 2)) / 2 + 1) (Nat.le_add_left 1 _) φ hφ
  refine (linear_iterated_integral μK μ f c h1 h2
    (fun k t => coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k.1 t.1) h3 l).trans ?_
  refine congrArg (integral μK) (funext fun k => congrArg (integral μ) (funext fun t => ?_))
  have e : coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k.1 t.1 =
      ((X.ν t.1 : ℂ) * ((absE F E t.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) •
        ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' t.1))) (locOp v (om' (k.1, 1)) φ)) := by
    funext y
    simp only [coneFinInt, Pi.smul_apply, smul_eq_mul]
    ring
  beta_reduce
  rw [e, map_smul, smul_eq_mul]
  ring

end GlobalTheory.ThK.LemF.ConePass
