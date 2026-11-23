import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusAverageIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetFinAtMemIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormRealCentralCharacterEqOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLocalCentralScalarsEqOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCentralScalarsTrivialStatement
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

theorem norm_uW_eq_one : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (z : Jd), ‖uW n t M z‖ = 1 := by
  classical
  intro K _ _ h2 c n t M hM z
  obtain ⟨hok, S0, hS0⟩ := hM
  obtain ⟨S, hS⟩ := GlobalTheory.T.adelic_realPart_properties.2.2.2 z
  have hsupp : (Function.mulSupport fun v : Pl => omW (M v) (Ad3.R.lc v z)) ⊆
      ((S0 ∪ S : Finset Pl) : Set Pl) := by
    intro v hv
    by_contra hn
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hn
    exact hv (GlobalTheory.T.unramified_central_scalars_trivial K h2 c v (M v) (hS0 v hn.1).1 (hok v) _ (hS v hn.2)).1
  unfold uW
  rw [norm_mul, GlobalTheory.T.norm_real_central_character_eq_one, one_mul, finprod_eq_prod_of_mulSupport_subset _ hsupp, norm_prod]
  exact Finset.prod_eq_one fun v _ => (GlobalTheory.T.norm_local_central_scalars_eq_one K h2 c v (M v) (hok v) _).1

end GlobalTheory.CompanionTheory.CenTheta
