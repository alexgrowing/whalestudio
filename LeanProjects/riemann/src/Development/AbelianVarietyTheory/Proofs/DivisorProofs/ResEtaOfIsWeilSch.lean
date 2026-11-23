import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AnisoClauseOfFirstTerm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentSiegelCols
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EisensteinSeriesContinuationModuli
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodMajorantLevelConjUnitaryAdelicMaximalCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanPairingEisensteinSimplePole
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightTranslateCommutesCenterAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeAlongLieAlgebraPreservesSmoothSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionSmoothCommuting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanPairingLieDerivativeAntisymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionSmoothBounded
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GelfandTransposeEqOfInvariantWords
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaCenterActionLeft
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionTransportChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerModelSmoothInGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralTranslateSmul
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelSobolevBoundWeilCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSobolevBoundThetaPointwise
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LscSeminormThetaFunctionsLevelLeSobolev
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsThetaIntegralLeSobolevSeminorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriedCentreAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerModelCenterEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaCentreLinear
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHermIsUnitGeneric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeyl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMovedNotProportional
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsSchwartz
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

open scoped Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.FirstTermIsoCst
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory GlobalTheory.RegSch
open Filter Topology

namespace GlobalTheory.RegSch.JointCont

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model in

theorem levi_weyl_rel {R : Type} [CommRing R] {n : ℕ} {b c : Matrix (Fin n) (Fin n) R} (h1 : b * c = 1) (h2 : c * b = 1) :
    blk4 b 0 0 c * blk4 0 1 (-1) 0 = blk4 1 b 0 1 * blk4 0 1 (-1) 0 * blk4 1 c 0 1 *
      (blk4 0 1 (-1) 0 * blk4 0 1 (-1) 0 * blk4 0 1 (-1) 0) * blk4 1 b 0 1 := by
  simp [submatrix_fromBlocks_mul, h1, h2]

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model in

theorem resEta_of_isWeilSch {D : D7} {n : ℕ} (hn : 0 < n) {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {θ : InfFam D} (hθ : IsInfFam θ) {χ : (AE D)ˣ →* Circle}
    {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω) : ResEta D χ V.rank := by
  obtain ⟨χ₀, h1, h2, -⟩ := GlobalTheory.PlaceCompare.Spherical.exists_unram_char D V.rank
  obtain ⟨ψ₀, h₀, lam, hlam, hψeq⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hsh : ψ = shift ψ₀ lam := by
    ext x
    rw [hψeq]
    rfl
  obtain ⟨ω₀, hω₀⟩ := Inhab.weil_exists D n V ψ₀ h₀ lam hlam χ₀ h1 h2 θ hθ μ 𝓕 hμ
  rw [← hsh] at hω₀
  suffices h : ∀ t, χ (idF D t) = χ₀ (idF D t) from ⟨h2.1, fun η hη a => (h a).trans (h2.2 η hη a)⟩
  intro t
  let i₀ : Fin n := ⟨0, hn⟩
  let dg : (AF D.host.F)ˣ → Mx D n n := fun u => Matrix.diagonal (Function.update 1 i₀ (idF D u : AE D))
  have hmul : ∀ u u', dg u * dg u' = dg (u * u') := fun u u' => by
    simp only [dg, Matrix.diagonal_mul_diagonal, map_mul, Units.val_mul]
    congr 1
    funext i
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  have hone : dg 1 = 1 := by simp [dg]
  have hadj : ∀ u, adj (dg u) = dg u := fun u => by
    ext i j
    simp only [adj, dg, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = i₀
      · subst hi
        simp only [if_true, Function.update_self]
        exact GlobalTheory.HermTransversal.cA_algebraMap _
      · simp [Function.update_of_ne hi]
    · simp [hij, Ne.symm hij]
  have e1 : dg t * dg t⁻¹ = 1 := by rw [hmul, mul_inv_cancel, hone]
  have e2 : dg t⁻¹ * dg t = 1 := by rw [hmul, inv_mul_cancel, hone]
  let a : GL (Fin n) (AE D) := ⟨dg t, dg t⁻¹, e1, e2⟩
  have hdet : Matrix.GeneralLinearGroup.det a = idF D t := by
    ext
    simp [a, dg, Finset.prod_update_of_mem]
  obtain ⟨g, hg⟩ := exists_levi (D := D) (n := n) a
  obtain ⟨u, hu⟩ := (exists_unip (dg t)).2 (hadj t)
  obtain ⟨u', hu'⟩ := (exists_unip (dg t⁻¹)).2 (hadj t⁻¹)
  obtain ⟨w, hw⟩ := exists_weyl (D := D) (n := n)
  have hinj : ∀ x y : StdUnn.G D n, mat x = mat y → x = y := fun x y h => Subtype.ext (Units.ext h)
  have hrel : g * w = u * w * u' * (w * w * w) * u := by
    refine hinj _ _ ?_
    have e4 : (adj (a⁻¹).1 : Mx D n n) = dg t⁻¹ := hadj t⁻¹
    rw [e4] at hg
    change mat g * mat w = mat u * mat w * mat u' * (mat w * mat w * mat w) * mat u
    rw [hg, hw, hu, hu']
    exact levi_weyl_rel e1 e2
  let S := ω.toHomUnits.eqLocus ω₀.toHomUnits
  have hU : ∀ (x : StdUnn.G D n) (b : Mx D n n), mat x = blk4 1 b 0 1 → x ∈ S := fun x b hx =>
    Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun y => (hω.unip x b hx Φ y).trans (hω₀.unip x b hx Φ y).symm))
  have hW : w ∈ S :=
    Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun y => (hω.weyl w hw Φ y).trans (hω₀.weyl w hw Φ y).symm))
  have hgS : g ∈ S := by
    rw [← S.mul_mem_cancel_right hW, hrel]
    exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (hU _ _ hu) hW) (hU _ _ hu')) (S.mul_mem (S.mul_mem hW hW) hW)) (hU _ _ hu)
  have hge : ω g = ω₀ g := congrArg Units.val hgS
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.Published.ThetaConvModel.exists_schwartz θ V.rank n
  have k1 := hω.levi g a hg Φ 0
  rw [hge, hω₀.levi g a hg Φ 0, hdet] at k1
  have z1 : ((0 : Mx D V.rank n) ⬝ a.1 : Mx D V.rank n) = 0 := Matrix.zero_mul _
  rw [z1] at k1
  have hp : npow (absA D (idF D t)) ((V.rank : ℂ) / 2) ≠ 0 := by
    have : absA D (idF D t) ≠ 0 := ((Group.isUnit _).map (absA D)).ne_zero
    rw [npow, Complex.cpow_def_of_ne_zero (by exact_mod_cast this)]
    exact Complex.exp_ne_zero _
  exact Circle.ext (mul_right_cancel₀ hp (mul_right_cancel₀ hΦ k1)).symm

end GlobalTheory.RegSch.JointCont

end
