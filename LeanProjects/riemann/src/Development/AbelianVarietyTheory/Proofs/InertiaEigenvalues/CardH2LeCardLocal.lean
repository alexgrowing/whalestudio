import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1H2Local
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDualZmodLeCard
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

theorem card_H2_le_of_local_duality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K) M), 0 < r → ContAction rho → Finite (H2 rho) ∧ Nat.card (H2 rho) ≤ Nat.card M := by
  intro hT l _ K hK r M _ _ _ _ _ rho hr hrho
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hfin := (GlobalTheory.finite_H1_H2_of_localTateDuality hT l K hK r M rho hr hrho).2
  obtain ⟨⟨e⟩, -, -, -, h20⟩ := hT l K hK r M rho hr hrho
  refine ⟨hfin, ?_⟩
  haveI : Finite (TDual (ZMod (l ^ r)) M) :=
    Finite.of_injective (fun φ : TDual (ZMod (l ^ r)) M => (φ : M → ZMod (l ^ r)))
      DFunLike.coe_injective
  haveI : Finite (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
    Subtype.finite
  haveI : Finite (H2 ((charRep (Formalism.GaloisCohomology.cycK l K r)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
    Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K))) →ₗ[ZMod (l ^ r)]
      H2 ((charRep (Formalism.GaloisCohomology.cycK l K r)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
    Finite.of_injective (fun f => (f : _ → _)) DFunLike.coe_injective
  calc Nat.card (H2 rho)
      ≤ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K))) →ₗ[ZMod (l ^ r)]
          H2 ((charRep (Formalism.GaloisCohomology.cycK l K r)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
        Nat.card_le_card_of_injective _ h20.1
    _ = Nat.card (Module.Dual (ZMod (l ^ r))
          (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K))))) :=
        Nat.card_congr (LinearEquiv.congrRight e).toEquiv
    _ ≤ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
        GlobalTheory.card_dual_zmod_le_card (l ^ r) _
    _ ≤ Nat.card (TDual (ZMod (l ^ r)) M) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ ≤ Nat.card M := GlobalTheory.card_dual_zmod_le_card (l ^ r) M

end GlobalTheory
