import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusAverageIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetFinAtMemIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionCentralCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalThetaCentralCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecialDatumCentralCharacterAtZeroStatement
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

noncomputable section

namespace GlobalTheory.CompanionTheory.CenTheta

theorem thT_zero_central : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (z : Jd) (g : G2), thT n t M (dg2 z z * g) 0 = u0 n t M z * thT n t M g 0 := by
  intro K _ _ h2 c n t M hM z g
  obtain ⟨hok, S0, hS0⟩ := hM
  obtain ⟨hfin, hreal, hrealdg, hcomp⟩ := GlobalTheory.T.adelic_realPart_properties
  obtain ⟨S1, hS1⟩ := GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g
  obtain ⟨S2, hS2⟩ := hcomp z
  classical
  have hloc : ∀ v : Pl, (M v).val (finAt v (dg2 z z * g)) 0 =
      om0 (M v) (Ad3.R.lc v z) * (M v).val (finAt v g) 0 := by
    intro v
    have hmul : finAt v (dg2 z z * g) = dg2 (Ad3.R.lc v z) (Ad3.R.lc v z) * finAt v g := by
      rw [GroundTheory.Automorphic.Reduction.finAt_mul, hfin]
    rw [hmul]
    by_cases hs : (M v).IsSp
    · exact GlobalTheory.T.special_datum_central_character_at_zero K c v (M v) (hok v) hs _ _
    · have h := GlobalTheory.T.local_theta_central_character K h2 c v (M v) (hok v) hs (Ad3.R.lc v z) (finAt v g) 0
      rw [h]
      congr 1
      cases hm : M v with
      | sp w₁ w₂ Φ => rw [hm] at hs; exact absurd trivial hs
      | ns w σ η Φ => rfl
  have hoff : ∀ v ∉ S0 ∪ S1 ∪ S2, om0 (M v) (Ad3.R.lc v z) = 1 ∧ (M v).val (finAt v g) 0 = 1 := by
    intro v hv
    simp only [Finset.mem_union, not_or] at hv
    obtain ⟨⟨h0, h1⟩, h2'⟩ := hv
    obtain ⟨hU, hs⟩ := hS0 v h0
    exact ⟨(GlobalTheory.T.unramified_central_scalars_trivial K h2 c v (M v) hU (hok v) _ (hS2 v h2')).2,
      (GlobalTheory.T.unramified_standard_values_at_integral K h2 c v (M v) hU (hok v) hs _ (hS1 v h1)).2⟩
  have hA : (Function.mulSupport fun v => om0 (M v) (Ad3.R.lc v z)).Finite :=
    (S0 ∪ S1 ∪ S2).finite_toSet.subset fun v hv => by
      by_contra hn
      exact hv (hoff v (by simpa using hn)).1
  have hB : (Function.mulSupport fun v => (M v).val (finAt v g) 0).Finite :=
    (S0 ∪ S1 ∪ S2).finite_toSet.subset fun v hv => by
      by_contra hn
      exact hv (hoff v (by simpa using hn)).2
  simp only [thT, u0]
  rw [hreal, hrealdg, GlobalTheory.T.real_weil_action_central_character n t, finprod_congr hloc, finprod_mul_distrib hA hB]
  ring

end GlobalTheory.CompanionTheory.CenTheta
