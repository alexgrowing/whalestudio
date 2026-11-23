import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaUnipotentInvariance
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta.ZeroTerm

theorem theta_zero_term_unipotent_invariant_adelic : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ)
    (M : ∀ v : Pl, LM c v), AdmM M → ∀ (x : 𝔸[ℚ]) (g : G2), thT n t M (uni2 x * g) 0 = thT n t M g 0 := by
  intro K _ _ h2 c n t M hM x g
  have hfin : ∀ v, (M v).val (finAt v (uni2 x * g)) (0 : K) = (M v).val (finAt v g) (0 : K) := by
    intro v
    rw [GroundTheory.Automorphic.Reduction.finAt_mul, GlobalTheory.CompanionTheory.GlobalWhittakerPsi.finiteComponent_unipotent,
      GlobalTheory.CompanionTheory.ThetaUnipotent.local_theta_value_unipotent h2 (M v) (hM.1 v)]
    simp
  have hinf : piRc (chC n (Complex.I * t)) (GL2Classical.realPart (uni2 x * g)) (PhiInf n) (embC K 0) =
      piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K 0) := by
    rw [GlobalTheory.CompanionTheory.GL2Factorization.PT.realPart_mul, GlobalTheory.CompanionTheory.GlobalWhittakerPsi.realPart_unipotent_adele,
      GlobalTheory.CompanionTheory.ThetaUnipotent.real_weil_action_unipotent]
    simp [embC, GlobalTheory.CompanionTheory.GlobalWhittakerPsi.eC]
  simp only [thT]
  rw [hinf, finprod_congr hfin]

end GlobalTheory.CompanionTheory.FexTheta.ZeroTerm
