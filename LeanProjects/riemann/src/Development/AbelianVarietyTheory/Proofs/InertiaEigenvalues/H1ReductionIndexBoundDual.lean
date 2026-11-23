import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualPairingCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicIntegralLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1ReductionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerReductionH1EqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeLevelPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedFiniteCohomologyQuotientsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetPrimePowTorsionQuotientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowInvSmulLiftMemDivisibleCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfDoubleAnnihilatorPairingStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BoundedIndex

set_option maxHeartbeats 1000000 in

theorem h1_reduction_index_bounded : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ Nat.card (QuotientCohomology LA _ hI) ∧ Nat.card (QuotientCohomology LA _ hI) ≤ C * Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' LA LA' m hm
  obtain ⟨L1, hL1⟩ := GlobalTheory.T.exists_cyclotomic_integral_lattice l P K LL O hO
  obtain ⟨C0, k0, hF⟩ := GlobalTheory.T.bounded_finite_cohomology_quotients hT l P K LL O hO A' LA'
  obtain ⟨Es, hEs⟩ := GlobalTheory.T.exists_finset_primePow_torsion_quotient l LL O hO k0
  have hEs1 : 1 ≤ Es.card := Finset.card_pos.2 ⟨0, hEs 0 (smul_zero _)⟩
  refine ⟨Es.card ^ C0, pow_pos hEs1 _, fun r hI => ?_⟩
  have hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) :=
    GlobalTheory.TateOrth.stable_span_smul_top LA' _
  haveI hX := GlobalTheory.T.finite_H1_reduction hT l K LL O hO A LA r hI
  haveI hY := GlobalTheory.T.finite_H1_reduction hT l K LL O hO A' LA' r hI'
  haveI : Module.Finite O (QuotientCohomology LA' _ hI') := Module.Finite.of_finite
  obtain ⟨f, hker, hf⟩ := GlobalTheory.T.ker_reduction_H1_eq l P K LL O hO A LA r hI
  obtain ⟨β, hβ1, hβ2⟩ := GlobalTheory.T.tate_pairing_lattice_level_primePow hT l P K LL O hO L1 hL1 A A' LA LA' m hm r hI hI'
  obtain ⟨F, hFc, hFm⟩ := hF r hI'
  have hcardS : Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) =
      Nat.card (LinearMap.range f) := by
    have key : ∀ N : Submodule O (LatticeCohomology LA), LinearMap.ker f = N → Nat.card (LatticeCohomology LA ⧸ N) = Nat.card (LinearMap.range f) := by
      rintro N rfl
      exact Nat.card_congr f.quotKerEquivRange.toEquiv
    exact key _ hker
  rw [hcardS]
  refine ⟨Nat.card_le_card_of_injective _ Subtype.val_injective, ?_⟩
  have hdd : ∀ c, (∀ y, (∀ s ∈ LinearMap.range f, β y s = 0) → β y c = 0) → c ∈ LinearMap.range f :=
    GlobalTheory.mem_of_forall_annihilator_annihilator l LL O hO _ _ β (LinearMap.range f)
      (fun c hc => by rw [hβ1 c hc]; exact Submodule.zero_mem _)
  have hA : ∀ y, (∀ s ∈ LinearMap.range f, β y s = 0) → y ∈ F ∧ ((l : ℕ) : O) ^ k0 • y = 0 := by
    intro y hy
    obtain ⟨c', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    apply hFm c'
    refine GlobalTheory.TateOrth.mem_BD_of_orthogonal hT l P K LL O hO L1 hL1 A A' LA LA' m hm _
      (GlobalTheory.T.primePow_inv_smul_lift_mem_divisible_cocycles l K LL O hO A' LA' r hI' c') fun d hd => ?_
    obtain ⟨h, hfd⟩ := hf ⟨d, hd⟩
    have h0 : β (Submodule.Quotient.mk c') (f (Submodule.Quotient.mk ⟨d, hd⟩)) = 0 := hy _ ⟨_, rfl⟩
    exact hβ2 ⟨d, hd⟩ h c' ((congrArg (β (Submodule.Quotient.mk c')) hfd).symm.trans h0)
  calc Nat.card (QuotientCohomology LA _ hI) ≤ Es.card ^ F.card * Nat.card (LinearMap.range f) :=
        GlobalTheory.T.card_le_of_double_annihilator_pairing O _ _ _ β (LinearMap.range f) F Es _ hdd hA hEs
    _ ≤ Es.card ^ C0 * Nat.card (LinearMap.range f) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hEs1 hFc)

end GlobalTheory.BoundedIndex
