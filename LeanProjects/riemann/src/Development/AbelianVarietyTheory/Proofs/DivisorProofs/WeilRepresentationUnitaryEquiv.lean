import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RealConjFac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem inv_mem_UAt {n : ℕ} {X : Spc F E n} {g : UA σ X.J} (hg : g ∈ UAt σ X (evI F)) :
    g⁻¹ ∈ UAt σ X (evI F) := by
  intro u hu
  have h1 : u • (mat g - 1) = 0 := hg u hu
  have hm : mat g⁻¹ * mat g = 1 := by simp [mat]
  have : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
    rw [Matrix.mul_sub, hm, Matrix.mul_one, neg_sub]
  rw [this, smul_neg, ← Matrix.mul_smul, h1, Matrix.mul_zero, neg_zero]

theorem acts_comp {κ : Type} [Fintype κ] {A B : Module.End ℂ ((κ → AF F) → ℂ)}
    (hA : ∀ Φ ∈ schA F κ, A Φ ∈ schA F κ) {f f₁ f₂ : SInf F κ}
    (h₁ : Acts (evI F) A (⇑f) (⇑f₁)) (h₂ : Acts (evI F) B (⇑f₁) (⇑f₂)) :
    Acts (evI F) (B * A) (⇑f) (⇑f₂) := by
  intro r hr
  have e₁ := h₁ r hr
  have hr₁ : Rest (evI F) (⇑f₁) r := ⟨hr.1, by rw [← e₁]; exact hA _ hr.2⟩
  rw [Module.End.mul_apply, e₁]
  exact h₂ r hr₁

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∃ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) ∧
      ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hB _ _ _ hw g hg h hh
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  have hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om x Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun x Φ hΦ => hW.pres x Φ hΦ
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hB.std hw (g, h) hg hh
  obtain ⟨T₂, hT₂⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hB.std hw (g⁻¹, h⁻¹) (inv_mem_UAt hg) (inv_mem_UAt hh)
  have hid : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (1 : Module.End ℂ _) (⇑f) (⇑f) := fun f r _ => rfl
  have e21 : ∀ f, T₂ (T₁ f) = f := by
    intro f
    have hc := acts_comp (hpres _) (hT₁ f) (hT₂ (T₁ f))
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (T₂ (T₁ f)) f).2.2.2.1 _ hc (hid f))
  have e12 : ∀ f, T₁ (T₂ f) = f := by
    intro f
    have hc := acts_comp (hpres _) (hT₂ f) (hT₁ (T₂ f))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (T₁ (T₂ f)) f).2.2.2.1 _ hc (hid f))
  refine ⟨LinearEquiv.ofLinear T₁ T₂ (LinearMap.ext e12) (LinearMap.ext e21), fun f => hT₁ f, fun f => ?_⟩
  exact hT₂ f

end GlobalTheory.RealConjFac
