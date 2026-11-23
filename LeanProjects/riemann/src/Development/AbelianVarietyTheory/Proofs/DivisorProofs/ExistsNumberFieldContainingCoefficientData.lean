import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder IntermediateField

namespace GlobalTheory.ColNorms.ExField

theorem exists_field_holdsData : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (cD : D.what₂.Tau → ℂ) (K : Type) [Field K] [NumberField K] (σ₀ : K →+* ℂ) (R : Ranks), StandardLatticesGL3.Crv D cc dl → IsDgen D cD → (∀ i < R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ TaylorLogMetric.CoefIn D (B.thZero (R.N i) (R.N (i + 1))) M) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ThetaFieldData B cD σ₀ R M := by
  intro D cc dl B cD K _ _ σ₀ R hC hD hM
  obtain ⟨M₁, hM₁, hE, hc⟩ := hD
  obtain ⟨⟨-, h2, h3⟩, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D
    (GlobalTheory.InducedType.induced_type D).1).2 cc dl hC
  choose Mi hMi hcoef using fun i : Fin R.m => hM i.1 i.2
  let M₀ : IntermediateField ℚ ℂ := σ₀.toRatAlgHom.fieldRange
  haveI f0 : FiniteDimensional ℚ M₀ :=
    (AlgEquiv.ofInjectiveField σ₀.toRatAlgHom).toLinearEquiv.finiteDimensional
  let M₂ : IntermediateField ℚ ℂ := ℚ⟮TaylorLogMetric.g2 (TaylorLogMetric.tor0 D cc dl).abelian₂⟯
  let M₃ : IntermediateField ℚ ℂ := ℚ⟮TaylorLogMetric.g3 (TaylorLogMetric.tor0 D cc dl).abelian₂⟯
  haveI f2 : FiniteDimensional ℚ M₂ :=
    IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.mp h2).isIntegral
  haveI f3 : FiniteDimensional ℚ M₃ :=
    IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.mp h3).isIntegral
  haveI f1 : FiniteDimensional ℚ M₁ := inferInstance
  haveI f4 : FiniteDimensional ℚ (⨆ i, Mi i : IntermediateField ℚ ℂ) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  let M : IntermediateField ℚ ℂ := (M₀ ⊔ M₁) ⊔ (M₂ ⊔ M₃) ⊔ ⨆ i, Mi i
  have l0 : M₀ ≤ M := le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  have l1 : M₁ ≤ M := le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have l2 : M₂ ≤ M := le_sup_of_le_left (le_sup_of_le_right le_sup_left)
  have l3 : M₃ ≤ M := le_sup_of_le_left (le_sup_of_le_right le_sup_right)
  have l4 : ∀ i, Mi i ≤ M := fun i => le_sup_of_le_right (le_iSup Mi i)
  refine ⟨M, inferInstance, fun k => l0 ⟨k, rfl⟩, ⟨fun τ x => l1 (hE τ x),
    l2 (IntermediateField.mem_adjoin_simple_self _ _), l3 (IntermediateField.mem_adjoin_simple_self _ _)⟩,
    fun τ => ?_, fun i hi α => l4 ⟨i, hi⟩ (hcoef ⟨i, hi⟩ α)⟩
  obtain ⟨s, hs, -⟩ := hc τ
  exact hs ▸ l1 s.2

end GlobalTheory.ColNorms.ExField
