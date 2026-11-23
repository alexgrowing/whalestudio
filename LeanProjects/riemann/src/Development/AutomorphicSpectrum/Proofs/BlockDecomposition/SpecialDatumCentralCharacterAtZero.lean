import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentralCharacterHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AddCharConductorInv
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

theorem degreeOneEmbedding_zero {K : Type} [Field K] [NumberField K] (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] : dg1 v w (0 : K) = 0 := by
  have hinj : Function.Injective (algebraMap (Qv v) (Kv K w)) := (algebraMap (Qv v) (Kv K w)).injective
  have h := Function.leftInverse_invFun hinj (0 : Qv v)
  simpa [dg1] using h

theorem val_zero_central_sp : ∀ (K : Type) [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl)
    (m : LM c v), m.ok → m.IsSp → ∀ (a : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)),
      m.val (dg2 a a * g) 0 = om0 m a * m.val g 0 := by
  intro K _ _ c v m hok hsp a g
  have hχ := GlobalTheory.CompanionTheory.SphStd.isStd_psiF_inv v
  cases m with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    have hΦ : Φ ∈ GL2LocalData.SBE (Qv v × Qv v) := ⟨hok.2.1, hok.2.2⟩
    simp only [LM.val, om0, degreeOneEmbedding_zero]
    rw [GlobalTheory.CompanionTheory.SplitPi.piS_mul hχ.1 hχ.2.1 _ hΦ, GlobalTheory.CompanionTheory.SplitCentre.piS_scalar]
    simp
  | ns w σ η Φ => exact hsp.elim

end GlobalTheory.CompanionTheory.CenTheta
