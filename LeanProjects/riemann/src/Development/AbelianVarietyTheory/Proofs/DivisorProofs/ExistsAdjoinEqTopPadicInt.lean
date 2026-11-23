import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Formalism.LocalToGlobal.ProjectiveLattices.AvMono
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.MonoGen

theorem exists_adjoin_eq_top_padicInt : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ],
    ∃ α : Λ, Algebra.adjoin ℤ_[p] {α} = ⊤ := by
  intro p _ Λ _ _ _ _ _ _
  have hinj : Function.Injective (algebraMap ℤ_[p] Λ) := FaithfulSMul.algebraMap_injective _ _
  haveI : Algebra.IsIntegral ℤ_[p] Λ := Algebra.IsIntegral.of_finite ℤ_[p] Λ
  haveI : IsLocalHom (algebraMap ℤ_[p] Λ) :=
    RingHom.IsIntegral.isLocalHom (Algebra.IsIntegral.isIntegral (R := ℤ_[p]) (A := Λ)) hinj
  haveI : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
  exact Formalism.L2.Pj.AvAlg.exists_adjoin_eq_top hinj

end GlobalTheory.MonoGen
