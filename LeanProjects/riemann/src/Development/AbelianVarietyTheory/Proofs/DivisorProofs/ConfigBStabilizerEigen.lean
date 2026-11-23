import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerLocalEvalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerGlobalEvalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerThetaEvalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerPeriodEvalStatement

noncomputable section

open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped Classical

namespace GlobalTheory.ConeSoB

theorem cone_pure_euler : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (μK : Measure K) (μ : Measure (AE F E)ˣ), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
    IntOK B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (pure f φ) ∧
    ∃ (c : ℂ) (f₁ : SInf F (Fin b × Fin (a + b))) (ψ : ∀ v : Pl F, (Fin b × Fin (a + b) → Fv F v) → ℂ)
      (μK₁ : Measure (KAt K (evFin F B.v₁))) (μ₁ : Measure (idelesAt E (evFin F B.v₁))),
      IsNormK K (evFin F B.v₁) μK₁ ∧ IsNormE E B.v₁ μ₁ ∧ (∀ v, ψ v ∈ SB _) ∧ (∀ᶠ v in cofinite, ψ v = G₁.M'.vac v) ∧
      ψ B.v₁ = coneFin B G.M' om' B.v₁ (ev B.v₁) K μK₁ μ₁ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (φ B.v₁) ∧
      cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (pure f φ) = c • pure f₁ ψ := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hloc μK μ hμK hμ f φ hφ hvac
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) := by
    obtain ⟨K', -, -, hK', hc, -, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B (b + 2) G.V' G.q ((b + 2) - G.q) hT.base hT.geo.hV'
    have e : K = K' := Subgroup.ext fun g => (hK g).trans (hK' g).symm
    rw [e]; exact hc
  obtain ⟨μKi, hμKi, -⟩ := existsUnique_isNormK hKc (evI F)
  obtain ⟨μi, hμi⟩ := exists_haar_idelesAt E (evI F)
  let μKv : ∀ v : Pl F, Measure (KAt K (evFin F v)) := fun v => (existsUnique_isNormK hKc (evFin F v)).choose
  let μv : ∀ v : Pl F, Measure (idelesAt E (evFin F v)) := fun v => (existsUnique_isNormE E v).choose
  have hμKv : ∀ v, IsNormK K (evFin F v) (μKv v) := fun v => (existsUnique_isNormK hKc (evFin F v)).choose_spec.1
  have hμv : ∀ v, IsNormE E v (μv v) := fun v => (existsUnique_isNormE E v).choose_spec.1
  have hfin : Set.Finite {v | ¬ φ v = G.M'.vac v} := Filter.eventually_cofinite.1 hvac
  let S : Finset (Pl F) := X.T ∪ {B.v₁} ∪ hfin.toFinset
  have hS : ∀ v ∉ S, φ v = G.M'.vac v := fun v hv => by
    by_contra h
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
  have hT0 : X.T ⊆ S := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hv₁ : B.v₁ ∈ S := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_schwartz_eq_coneInfFun_shiftB hP B G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hloc μKi μi hμKi hμi f
  obtain ⟨c, hc⟩ := GlobalTheory.T.config_B_stabilizer_period_eval hP B G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hloc μK μ hμK hμ
    μKi μi hμKi hμi μKv μv hμKv hμv f φ S hφ hS hT0 hv₁
  refine ⟨GlobalTheory.T.config_B_stabilizer_local_eval hP B G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hloc μK μ hμK hμ f φ hφ hvac,
    c, g, fun v => if v ∈ S then coneFin B G.M' om' v (ev v) K (μKv v) (μv v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (φ v)
      else G₁.M'.vac v, μKv B.v₁, μv B.v₁, hμKv B.v₁, hμv B.v₁, fun v => ?_, ?_, by simp only [if_pos hv₁], ?_⟩
  · by_cases hv : v ∈ S
    · simp only [if_pos hv]
      exact GlobalTheory.T.config_B_stabilizer_theta_eval hP B G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hloc v _ _ (hμKv v) (hμv v) _ (hφ v)
    · simp only [if_neg hv]
      exact (hT₁.geo.hM'.vac v).1
  · refine (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    exact hv (if_neg h)
  · funext y
    rw [hc y]
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hg]

end GlobalTheory.ConeSoB
