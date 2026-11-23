import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.IdemLat

theorem finPart_idem_mem {D : D7} {P : Pl D.host.E} {e : Formalism.L2.Theta.AE D}
    (h : ∀ x : 𝓞 D.host.E, x ≠ 0 →
      (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)) :
    finPart D e ∈ intAE D := by
  have h1 : (1 : 𝓞 D.host.E) ∉ P.asIdeal := fun h1 =>
    P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have := not_not.1 fun hn => h1 ((h 1 one_ne_zero).2 hn)
  simpa using this

theorem finPart_placeIdem_mem {D : D7} {P : Pl D.host.E} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) : finPart D f ∈ intAE D := by
  rcases h with ⟨⟨_, h⟩, rfl⟩ | ⟨rfl, _, h⟩
  · have he := finPart_idem_mem h
    rw [RingHom.map_add]
    exact add_mem he (GlobalTheory.IdemSupport.finPart_cA_mem he)
  · exact finPart_idem_mem h

theorem lamHat_idem : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f →
    ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V := by
  intro D V P e f h y hy
  exact (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2 _ (finPart_placeIdem_mem h) y hy

end GlobalTheory.IdemLat
