import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HolomorphicDiscreteSeriesDecomposition

theorem dRepC_eq_sum : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E → ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (v : D), GlobalTheory.SmVec.dRepC (Jm ε) σ Z v = ((∑ a, ∑ b, Z a b • E a b v : D) : H) := by
  intro n ε H _ _ σ D E hK Z v
  have hG : IsUnit (Jm ε) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)
  obtain ⟨h1, h2⟩ := GlobalTheory.SmVec.parts_mem hG (Formalism.REAL.Jm_conjTranspose ε) Z
  have key : ∀ X, inG ε X → Formalism.L2.Theta.dRep σ X (v : H) = ∑ a, ∑ b, X a b • (E a b v : H) := fun X hX => by
    have := hK.real X hX v
    simp only [Complex.coe_smul] at this
    exact this.deriv
  unfold GlobalTheory.SmVec.dRepC
  rw [key _ h1, key _ h2]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul, ← add_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  field_simp
  ring

end GlobalTheory.HolomorphicDiscreteSeriesDecomposition
