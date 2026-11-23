import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mem_of_duplication_eq :
    ∀ (V : ValuationSubring ℂ) (W : WeierstrassCurve ℂ) (x y δ : ℂ), IntV V W →
      W.toAffine.Equation x y → 2 * y + W.a₁ * x + W.a₃ ∈ V → δ ∈ V →
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ = (2 * y + W.a₁ * x + W.a₃) ^ 2 * (x + δ) →
      x ∈ V ∧ y ∈ V := by
  intro V W x y δ hW hE hl hδ h
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  have hr : ∀ z : ℂ, z ∈ V → z ∈ (algebraMap V ℂ).range := fun z hz => ⟨⟨z, hz⟩, rfl⟩
  have hr' : ∀ z : ℂ, z ∈ (algebraMap V ℂ).range → z ∈ V := by
    rintro z ⟨w, rfl⟩; exact w.2
  have hb₄ : W.b₄ ∈ V := by
    rw [WeierstrassCurve.b₄]
    exact add_mem (mul_mem (ofNat_mem V 2) h₄) (mul_mem h₁ h₃)
  have hb₆ : W.b₆ ∈ V := by
    rw [WeierstrassCurve.b₆]
    exact add_mem (pow_mem h₃ 2) (mul_mem (ofNat_mem V 4) h₆)
  have hb₈ : W.b₈ ∈ V := by
    rw [WeierstrassCurve.b₈]
    refine sub_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
    · exact mul_mem (pow_mem h₁ 2) h₆
    · exact mul_mem (mul_mem (ofNat_mem V 4) h₂) h₆
    · exact mul_mem (mul_mem h₁ h₃) h₄
    · exact mul_mem h₂ (pow_mem h₃ 2)
    · exact pow_mem h₄ 2
  set l := 2 * y + W.a₁ * x + W.a₃ with hl_def
  have hx : x ∈ V := by
    refine hr' x (GlobalTheory.mem_range_of_quartic (A := V) (c₀ := -(W.b₈ + l ^ 2 * δ))
      (c₁ := -(2 * W.b₆ + l ^ 2)) (c₂ := -W.b₄) (c₃ := 0) (hr _ ?_) (hr _ ?_) (hr _ ?_) (hr _ ?_) ?_)
    · exact neg_mem (add_mem hb₈ (mul_mem (pow_mem hl 2) hδ))
    · exact neg_mem (add_mem (mul_mem (ofNat_mem V 2) hb₆) (pow_mem hl 2))
    · exact neg_mem hb₄
    · exact zero_mem V
    · linear_combination h
  refine ⟨hx, ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff] at hE
  refine hr' y (GlobalTheory.mem_range_of_quartic (A := V) (c₀ := 0) (c₁ := 0)
    (c₂ := -(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) (c₃ := W.a₁ * x + W.a₃)
    (hr _ (zero_mem V)) (hr _ (zero_mem V)) (hr _ ?_) (hr _ ?_) ?_)
  · exact neg_mem (add_mem (add_mem (add_mem (pow_mem hx 3)
      (mul_mem h₂ (pow_mem hx 2))) (mul_mem h₄ hx)) h₆)
  · exact add_mem (mul_mem h₁ hx) h₃
  · linear_combination y ^ 2 * hE

end GlobalTheory.CMModel
