import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalPartStabilizerStatement

open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeSoB

theorem iterated_integral_mem {α β Y : Type} [MeasurableSpace α] [MeasurableSpace β] (μK : Measure α) (μ : Measure β)
    (S : Submodule ℂ (Y → ℂ)) {N : ℕ} (f : Fin N → Y → ℂ) (c : Fin N → α → β → ℂ) (hf : ∀ i, f i ∈ S)
    (hc1 : ∀ i k, Integrable (c i k) μ) (hc2 : ∀ i, Integrable (fun k => ∫ l, c i k l ∂μ) μK)
    (g : α → β → Y → ℂ) (hsum : ∀ k l y, g k l y = ∑ i, c i k l * f i y) :
    (fun y => ∫ k, ∫ l, g k l y ∂μ ∂μK) ∈ S := by
  have e : (fun y => ∫ k, ∫ l, g k l y ∂μ ∂μK) = ∑ i, (∫ k, ∫ l, c i k l ∂μ ∂μK) • f i := by
    funext y
    have h1 : ∀ k, ∫ l, g k l y ∂μ = ∑ i, (∫ l, c i k l ∂μ) * f i y := fun k => by
      simp_rw [hsum]
      rw [integral_finsetSum _ fun j _ => (hc1 j k).mul_const _]
      exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [h1]
    rw [integral_finsetSum _ fun j _ => (hc2 j).mul_const _]
    exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hf i)

theorem coneFin_mem_SB_of_norm : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (v : Pl F) (μKv : Measure (KAt K (evFin F v))) (μv : Measure (idelesAt E (evFin F v))),
    IsNormK K (evFin F v) μKv → IsNormE E v μv → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
    coneFin B G.M' om' v (ev v) K μKv μv (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ ∈ SB (Fin b × Fin (a + b) → Fv F v) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' he' K hK X om om' om₁ om₁' T T₁ ei ev hei hev hpure v μK μ hμK hμ φ hφ
  obtain ⟨N, f, c, hf, hc1, hc2, hsum⟩ := GlobalTheory.T.config_b_local_part_stabilizer hP F E σ B a b G G₁ H H' cfg e' he' ei ev ⟨hei, hev, hpure⟩ K hK
    X om om' om₁ om₁' T T₁ v μK μ hμK.1 hμ.1 _ (Nat.le_add_left 1 _) φ hφ
  exact iterated_integral_mem μK μ _ f c hf hc1 hc2 _ hsum

end GlobalTheory.ConeSoB

end
