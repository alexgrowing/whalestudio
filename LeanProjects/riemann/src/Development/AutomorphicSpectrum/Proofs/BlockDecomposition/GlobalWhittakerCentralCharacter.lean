import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusAverageIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetFinAtMemIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionCentralCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWhittakerCentralCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCentralScalarsTrivialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedStandardValuesAtIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicRealPartPropertiesStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

namespace GlobalTheory.CompanionTheory.CenTheta

theorem WM_central : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (z : Jd) (g : G2), WM n t M (dg2 z z * g) = uW n t M z * WM n t M g := by
  intro K _ _ h2 c n t M hM z g
  classical
  obtain ⟨hok, S0, hS0⟩ := hM
  obtain ⟨hc1, hc2, hc3, hc4⟩ := GlobalTheory.T.adelic_realPart_properties
  obtain ⟨S1, hS1⟩ := GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g
  obtain ⟨S2, hS2⟩ := hc4 z
  have hreal : WcR (chC n (Complex.I * t)) (PhiInf n) (GL2Classical.realPart (dg2 z z * g)) =
      omR n t (RationalIdeles.realPart z) *
        WcR (chC n (Complex.I * t)) (PhiInf n) (GL2Classical.realPart g) := by
    rw [hc2, hc3]
    exact GlobalTheory.T.real_weil_action_central_character n t _ _ 1
  have hloc : ∀ v, (M v).W (finAt v (dg2 z z * g)) =
      omW (M v) (Ad3.R.lc v z) * (M v).W (finAt v g) := by
    intro v
    rw [GroundTheory.Automorphic.Reduction.finAt_mul, hc1]
    exact GlobalTheory.T.local_whittaker_central_character K h2 c v (M v) (hok v) _ _
  have hs1 : (Function.mulSupport fun v => omW (M v) (Ad3.R.lc v z)).Finite := by
    refine (S0 ∪ S2).finite_toSet.subset fun v hv => ?_
    by_contra hn
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hn
    exact hv (GlobalTheory.T.unramified_central_scalars_trivial K h2 c v (M v) (hS0 v hn.1).1 (hok v) _ (hS2 v hn.2)).1
  have hs2 : (Function.mulSupport fun v => (M v).W (finAt v g)).Finite := by
    refine (S0 ∪ S1).finite_toSet.subset fun v hv => ?_
    by_contra hn
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hn
    exact hv (GlobalTheory.T.unramified_standard_values_at_integral K h2 c v (M v) (hS0 v hn.1).1 (hok v) (hS0 v hn.1).2 _ (hS1 v hn.2)).1
  unfold WM pw2 uW
  rw [hreal, finprod_congr hloc, finprod_mul_distrib hs1 hs2]
  ring

end GlobalTheory.CompanionTheory.CenTheta
