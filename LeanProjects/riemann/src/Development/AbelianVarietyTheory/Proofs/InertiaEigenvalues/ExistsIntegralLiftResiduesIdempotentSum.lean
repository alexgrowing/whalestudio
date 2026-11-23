import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.IdemResLift

set_option maxHeartbeats 800000 in

theorem exists_int_lift : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → ∀ Y : ∀ PP : Pl D.host.E, kP PP, ∃ N : EAf D, ∃ hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (∑ PP ∈ Q, es PP) * N = N ∧ ∀ PP ∈ Q, resS D.host.F PP ⟨N, hN⟩ = Y PP := by
  intro D Q es hI hc Y
  have h1 : ∀ i ∈ Q, es i * es i = es i := fun i hi => (hI i hi).1.1
  have hx := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es Q h1 hc
  have horth : ∀ i ∈ Q, ∀ j ∈ Q, j ≠ i → es i * es j = 0 := fun i hi j hj hji =>
    GlobalTheory.PlaceDatum.idemAt_mul (hI i hi) (hI j hj) (hx i hi j hj) (hx j hj i hi) hji
  have hfix : ∀ j ∈ Q, (∑ i ∈ Q, es i) * es j = es j := by
    intro j hj
    rw [Finset.sum_mul, Finset.sum_eq_single j (fun i hi hij => by rw [mul_comm]; exact horth j hj i hi hij)
      (fun h => absurd hj h), h1 j hj]
  choose a ha using fun P : Pl D.host.E => Ideal.Quotient.mk_surjective (Y P)
  have hint : ∀ P ∈ Q, toEAf D (es P) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun P hP =>
    (GlobalTheory.IdemRes.resS_idem_eq_one D (es P) P (hI P hP)).1
  have hmem : ∀ P ∈ Q, toEAf D (es P) * ((oToS D.host.F D.host.E (a P) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D)
      ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun P hP => Subring.mul_mem _ (hint P hP) (Subtype.property _)
  let T : ∀ P, P ∈ Q → Formalism.L2.Herm.intAf D.host.F D.host.E := fun P hP =>
    ⟨toEAf D (es P), hint P hP⟩ * oToS D.host.F D.host.E (a P)
  refine ⟨∑ P ∈ Q, toEAf D (es P) * ((oToS D.host.F D.host.E (a P) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D),
    Subring.sum_mem _ hmem, ?_, ?_⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [← mul_assoc, ← RingHom.map_mul (toEAf D), hfix P hP]
  · intro P hP
    have hN : (⟨_, Subring.sum_mem _ hmem⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ x ∈ Q.attach, T x.1 x.2 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      exact (Finset.sum_attach Q (fun P => toEAf D (es P) *
        ((oToS D.host.F D.host.E (a P) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D))).symm
    rw [hN, map_sum, Finset.sum_eq_single ⟨P, hP⟩]
    · obtain ⟨h, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (es P) P (hI P hP)
      show resS D.host.F P (⟨toEAf D (es P), hint P hP⟩ * oToS D.host.F D.host.E (a P)) = Y P
      rw [map_mul, resS_oToS, ha, h1, one_mul]
    · rintro ⟨P', hP'⟩ - hne
      have hne' : P' ≠ P := fun h => hne (Subtype.ext h)
      show resS D.host.F P (⟨toEAf D (es P'), hint P' hP'⟩ * oToS D.host.F D.host.E (a P')) = 0
      rw [map_mul, GlobalTheory.TameProd.resS_idem_eq_zero (hI P' hP') hne', zero_mul]
    · intro h; exact absurd (Finset.mem_attach Q _) h

end GlobalTheory.IdemResLift
