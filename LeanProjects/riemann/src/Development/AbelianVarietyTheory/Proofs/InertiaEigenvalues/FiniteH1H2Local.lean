import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteOfPerfectPairingZmodStatement
open Formalism.GaloisCohomology ReciprocityTheory.Gal

namespace GlobalTheory

theorem finite_H1_H2_of_localTateDuality : LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ContAction rho → Finite (H1 rho) ∧ Finite (H2 rho) := by
  intro hT l _ K hK r M _ _ _ _ _ rho hr hrho
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hC, -, h11, h11f, h20⟩ := hT l K hK r M rho hr hrho
  obtain ⟨e⟩ := hC
  haveI hCfin : Finite (H2 ((charRep (cycK l K r)).comp (MonoidHom.id (GK l K)))) :=
    Finite.of_equiv _ e.toEquiv.symm
  have hAB := GlobalTheory.T.finite_of_bijective_pairing_zmod (l ^ r) _ _ _ _ ⟨e⟩ h11 h11f
  refine ⟨hAB.2, ?_⟩
  haveI : Finite (TDual (ZMod (l ^ r)) M) :=
    Finite.of_injective (fun φ : TDual (ZMod (l ^ r)) M => (φ : M → ZMod (l ^ r)))
      DFunLike.coe_injective
  haveI : Finite (H0 ((twDual (cycK l K r) rho).comp (MonoidHom.id (GK l K)))) :=
    Subtype.finite
  haveI : Finite (H0 ((twDual (cycK l K r) rho).comp (MonoidHom.id (GK l K))) →ₗ[ZMod (l ^ r)]
      H2 ((charRep (cycK l K r)).comp (MonoidHom.id (GK l K)))) :=
    Finite.of_injective (fun f => (f : _ → _)) DFunLike.coe_injective
  exact Finite.of_injective _ h20.1

end GlobalTheory
