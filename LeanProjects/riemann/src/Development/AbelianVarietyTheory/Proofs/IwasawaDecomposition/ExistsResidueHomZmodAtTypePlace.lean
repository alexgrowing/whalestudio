import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import ReciprocityTheory.ResidueCardinality.ArtinOntoB
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TypePlaceResidue

theorem residueHom_zmod : ∀ (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = NX.pG D kv →
    Nonempty (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)) := by
  intro D kv s hs
  have hp := D.host.g_prime kv.1
  haveI : Fact (D.host.g kv.1).Prime := ⟨hp⟩
  have hN := GlobalTheory.TameLabels.normV_eq_of_split hp (D.nd.g_split kv.1) (D.naut.plGw_over kv.1 kv.2)
  have hc : Nat.card (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))) =
      D.host.g kv.1 := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue, ← s.card_quot, hs]
    rw [← hN]
    rfl
  haveI : Finite (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact hp.ne_zero)
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)))
  have hcF : Fintype.card (IsLocalRing.ResidueField (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))) =
      D.host.g kv.1 := by rw [Fintype.card_eq_nat_card]; exact hc
  haveI := charP_of_card_eq_prime hcF
  exact ⟨(ZMod.ringEquiv _ hcF).symm.toRingHom.comp (IsLocalRing.residue _)⟩

end GlobalTheory.TypePlaceResidue
