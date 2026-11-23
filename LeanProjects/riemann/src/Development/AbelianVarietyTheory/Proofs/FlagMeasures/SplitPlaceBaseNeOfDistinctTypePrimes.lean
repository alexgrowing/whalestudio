import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAddEquivOfCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WBEqPrimeComap
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommTensCastRSymmMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.SplitPlaceDistinct

theorem not_mem_both {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (h1 : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) (h2 : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have e : ((a : 𝓞 E)) * ((p : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((q : ℕ) : 𝓞 E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
  rw [← e]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h1) (w.asIdeal.mul_mem_left _ h2)

theorem splitPlace_v_ne : ∀ (D : D7) (s s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (kv kv' : Σ k : Fin 2, D.nd.PlG k),
    s.w = D.naut.plGw kv.1 kv.2 → s'.w = D.naut.plGw kv'.1 kv'.2 → kv ≠ kv' → s.v ≠ s'.v := by
  intro D s s' kv kv' hs hs' hne hv
  obtain ⟨k, v⟩ := kv
  obtain ⟨k', v'⟩ := kv'
  have hgk : ∀ a b : Fin 2, a ≠ b → D.host.g a ≠ D.host.g b := by
    intro a b hab
    have h01 := D.host.g_ne
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact h01
    · exact h01.symm
    · exact absurd rfl hab
  have hover := D.naut.plGw_over
  rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s s'.w
      (s'.w_under.trans (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hv.symm)) with e | e
  · rw [hs, hs'] at e
    by_cases hk : k = k'
    · subst hk
      exact hne (congrArg (Sigma.mk k) (D.naut.plGw_inj k e))
    · exact not_mem_both (D.host.g_prime k) (D.host.g_prime k') (hgk k k' hk) _ (hover k v)
        (e ▸ hover k' v')
  · rw [hs, hs'] at e
    by_cases hk : k = k'
    · subst hk
      exact D.naut.plGw_nconj k v' v e
    · have hm : ((D.host.g k' : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal :=
        (e _ _ (by simp)).1 (hover k' v')
      exact not_mem_both (D.host.g_prime k) (D.host.g_prime k') (hgk k k' hk) _ (hover k v) hm

end GlobalTheory.SplitPlaceDistinct
