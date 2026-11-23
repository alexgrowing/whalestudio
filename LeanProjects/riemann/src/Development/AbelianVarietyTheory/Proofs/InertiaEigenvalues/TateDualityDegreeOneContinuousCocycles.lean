import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalTatePairingBilinearStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupOneCocyclesAnticommUpToCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleMemCoboundariesOfTateOrthogonalStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem tateDuality_degreeOne_cocycles : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ β : ↥(continuousCocycles A.ρ) →ₗ[LL] ↥(continuousCocycles A'.ρ) →ₗ[LL] LL, (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL A'.ρ m a.1 b.1)) ∧ (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 A.ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 A'.ρ := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' m hm
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_rational_tatePairing_bilinear hT l P K LL O hO A A' m hm
  have hflip : IsDual1 (P.PD K) A'.ρ A.ρ m.flip :=
    ⟨fun g x y => hm.1 g y x, hm.2.2.1, hm.2.1, hm.2.2.2.symm⟩
  have hanti := GlobalTheory.T.cup_one_cocycles_anticomm_up_to_coboundary l P K LL O hO A A' m hm
  refine ⟨β, hβ, fun a => ⟨fun h => ?_, fun ha b => ?_⟩, fun b => ⟨fun h => ?_, fun hb a => ?_⟩⟩
  · refine GlobalTheory.T.cocycle_mem_coboundaries_of_tate_orthogonal hT l P K LL O hO A' A m.flip hflip a.1 a.2 (fun b hb => ?_)
    exact ((hanti a.1 a.2 b hb).1).1 ((hβ a ⟨b, hb⟩).1 (h ⟨b, hb⟩))
  · exact (hβ a b).2 ((hanti a.1 a.2 b.1 b.2).2 (Or.inl ha))
  · exact GlobalTheory.T.cocycle_mem_coboundaries_of_tate_orthogonal hT l P K LL O hO A A' m hm b.1 b.2
      (fun a ha => (hβ ⟨a, ha⟩ b).1 (h ⟨a, ha⟩))
  · exact (hβ a b).2 ((hanti a.1 a.2 b.1 b.2).2 (Or.inr hb))

end GlobalTheory
