import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstAdmissibilityAtOfPartsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Adm8AtOfUnramifiedHeckeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobDualOfAttachedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkFrobOfAttachedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeOfAttachedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsGoodOfAttachedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PureOfAttachedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfAttachedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualCharpolyOfSplitFrobeniusDenseStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateNegativeJumpCountOfGoodHodgeJumpsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvAtTypePrimesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAboveLOfNoHodgeJumpStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvTateDualStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAuxiliaryPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoHodgeJumpOfGoodJumpMultisetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvAwayOfPureStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeOfConjDualCharpolyStatement

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem noInv_all_places (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i)
    (hT : ∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) (h2 : ValuationStabilityAtRing D.ntw i s)
    (hA : TripleAtt D.naut bkP i s) (hJ : NoJump bkP i s) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  by_cases hl : v ∈ placesOver D.host.E (D.ntw.l i)
  · exact ⟨GlobalTheory.T.noDecompositionInvariants_aboveL_of_noHodgeJump D bkP i s hJ v hl, GlobalTheory.T.noInv_tateDual_of_hodge_of_noJump D bkP i s hT (GlobalTheory.T.hodge_of_attached D bkP i s hA) hJ v hl⟩
  by_cases hS : v ∈ Spl (X := D.ntw) i
  · rcases hS.1 with hg | hp
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hg
      exact GlobalTheory.T.noInv_at_type_primes D i s h2 k (fun e => hl (e ▸ hk)) v hk
    · exact GlobalTheory.T.noDecompositionInvariants_auxiliaryPrime D i s (GlobalTheory.T.unramified_of_attached D bkP i s hA) v (Finset.mem_coe.1 hp)
  · obtain ⟨ι, hι⟩ := GlobalTheory.T.pure_of_attached D bkP i s hA
    exact GlobalTheory.T.noInv_away_of_pure D i s ι hι v hl hS

theorem galois_hypotheses_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D), GlobalTheory.TypeLeaf.FrobDense D → (∀ i, D.ntw.NonzeroIndexPlace i → (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI))) → BlochKatoReduction.adm2 D → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, TripleAtt D.naut bkP i s) → BlochKatoReduction.adm1 bkP ∧ BlochKatoReduction.adm8 D ∧ ∀ i, D.ntw.NonzeroIndexPlace i → True ∧ ∀ s : D.ntw.Sig i, SelfDual i s ∧ NoJump bkP i s := by
  intro D bkP hF hT h2 hA
  have hJ : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, NoJump bkP i s := fun i hi s => by
    obtain ⟨ι, J, h, h'⟩ := GlobalTheory.T.jumps_good_of_attached D bkP i s (hA i hi s)
    exact GlobalTheory.T.noHodgeJump_of_goodJumpMultiset D bkP i s ι J (GlobalTheory.T.hodge_of_attached D bkP i s (hA i hi s)) h h'
  refine ⟨fun i hi s => ?_, fun i hi s => ?_, fun i hi => ⟨trivial, fun s => ⟨?_, hJ i hi s⟩⟩⟩
  · obtain ⟨ι, J, h, h'⟩ := GlobalTheory.T.jumps_good_of_attached D bkP i s (hA i hi s)
    exact GlobalTheory.T.isotypicValuationAtRing_of_unrRho_hodgeL_noInv_negCount D bkP i s (GlobalTheory.T.unramified_of_attached D bkP i s (hA i hi s)) (GlobalTheory.T.hodge_of_attached D bkP i s (hA i hi s))
      (noInv_all_places D bkP i s (hT i hi) (h2 i hi s) (hA i hi s) (hJ i hi s))
      (GlobalTheory.T.conjugateNegativeJumpCount_of_goodHodgeJumps D bkP i s ι J (GlobalTheory.T.hodge_of_attached D bkP i s (hA i hi s)) h h')
  · exact GlobalTheory.T.characterTwistExists_of_unrRho_of_hkFrob D i s (GlobalTheory.T.unramified_of_attached D bkP i s (hA i hi s)) (GlobalTheory.T.hkFrob_of_attached D bkP i s (hA i hi s))
  · exact GlobalTheory.T.selfDual_lattice_of_conjDualCharpoly D i s (h2 i hi s) (GlobalTheory.T.conjDualCharpoly_of_splitFrobenius_dense D hF i s (GlobalTheory.T.frobDual_of_attached D bkP i s (hA i hi s)))

end GlobalTheory.TripleGal
