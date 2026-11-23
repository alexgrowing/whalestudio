import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatAtIsCO
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylUnipotentIwasawaHeightStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeImageLowerBlocksStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarImageGLScalingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarGLImageScalingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaximalCompactUnitaryArchimedeanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanHeightDeterminantFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsValueAdelicProductFormulaStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.HeightNu
open IsDedekindDomain NumberField

set_option maxHeartbeats 2000000 in

theorem heightNu : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (H : G D n → ℝ≥0), IsHeight H → ∀ (nb : hermA D n → G D n), IsNMap nb → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (a : GL (Fin n) (AE D)) (lamG : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), (∀ v, (lamG v).IsAddHaarMeasure) → ∀ b : hermA D n, PositivityTheory.SiegelWeilFormula.Gen.nuA θ (gAt θ a) lamG (latAt a.1) (latAt (adj (a⁻¹).1)) b.1 = ((H (w * nb (pull a b)) : ℝ≥0) : ℝ)⁻¹ := by
  intro D n θ hθ H hH nb hnb w hw a lamG hlam b
  obtain ⟨d, k, k₁, k₂, k₃, k₄, hk, hmk, h3, h4, hH'⟩ := GlobalTheory.T.weyl_unipotent_iwasawa_height D n H hH nb hnb w hw (pull a b)
  have hU := fun τ => GlobalTheory.T.maximal_compact_unitary_archimedean D n θ hθ k hk τ
  rw [hmk] at hU
  have hfin : ∀ v, PositivityTheory.SiegelWeilFormula.Gen.nu2 (lamG v) (latAt a.1 v) (latAt (adj (a⁻¹).1) v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1) =
      (absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d)) : ℝ) := fun v =>
    GlobalTheory.T.local_haar_GL_image_scaling D n a d b k₃ k₄ v (lamG v) (hlam v) (GlobalTheory.T.haar_image_GL_scaling D n v (lamG v) (hlam v)) (GlobalTheory.CompanionTheory.MM.latAt_isCO D n a v)
      h3 h4 (GlobalTheory.T.lattice_image_lower_blocks D n k k₁ k₂ k₃ k₄ hk hmk v)
  have hinf : PositivityTheory.SiegelWeilFormula.Gen.nuInf θ (gAt θ a) (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1) =
      ((∏ τ, ‖θ τ (infPart D (Matrix.GeneralLinearGroup.det d).1)‖₊ ^ 2 : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [NNReal.coe_pow, coe_nnnorm]
    exact GlobalTheory.T.archimedean_height_determinant_formula D n θ hθ a d b k₁ k₂ k₃ k₄ τ (hU τ) h3 h4
  have hfp : ((∏ᶠ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d)) : ℝ≥0) : ℝ) =
      ∏ᶠ v, ((absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d)) : ℝ≥0) : ℝ) :=
    MonoidHom.map_finprod NNReal.toRealHom.toMonoidHom (finite_mulSupport_absEv _)
  have e : ((H (w * nb (pull a b)) : ℝ≥0) : ℝ)⁻¹ = ((absA D (Matrix.GeneralLinearGroup.det d) : ℝ≥0) : ℝ) := by
    rw [← NNReal.coe_inv, hH']
  rw [e, GlobalTheory.T.absValue_adelic_product_formula D θ hθ, NNReal.coe_mul, hfp, ← hinf]
  exact congrArg _ (finprod_congr hfin)

end GlobalTheory.CompanionTheory.HeightNu
