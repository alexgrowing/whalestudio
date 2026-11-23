import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilAdditiveCharacterHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitAdditiveCharacterHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedThetaSpherical
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialGaloisPlaceDegreeTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetFinAtMemIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SummableUnitBounds.SBoundOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizationPureIntegrand
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.GlobalWhittakerPsi

abbrev eC (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

theorem unipotent_mul_val_real (x : ℝ) (g : GL (Fin 2) ℝ) :
    (uni2 x * g).val = !![g.val 0 0 + x * g.val 1 0, g.val 0 1 + x * g.val 1 1; g.val 1 0, g.val 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem local_whittaker_unipotent_character {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    {c : HeckeCharacter K} {v : Pl} (M : LM c v) (hok : M.ok) (x : Qv v) (g : GL (Fin 2) (Qv v)) :
    M.W (uni2 x * g) = (((GP.psiF v)⁻¹ x : Circle) : ℂ) * M.W g := by
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
    have : (((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) : Qv v → Circle) = fun x => (GP.psiF v x)⁻¹ := by
      funext x; exact AddChar.inv_apply' _ _
    rw [this]
    exact hstd.1.inv
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.mpr hstd.2.1
  cases M with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    exact GlobalTheory.CompanionTheory.WeilSplit.SplitAdditiveCharacter.sPsi (Qv v) _ hχc hχ1 _ _ Φ x g
  | @ns w i σ η Φ =>
    haveI := i
    obtain ⟨-, hσ, hη, -⟩ := hok
    exact GlobalTheory.CompanionTheory.WeilPsi.wPsi (Qv v) _ hχc hχ1 (Kv K w)
      (GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl K h2 v w i σ hσ)
      (continuous_adicCompletionMap v w) σ hσ η hη _ Φ x g

theorem LM_W_sph {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    {c : HeckeCharacter K} {v : Pl} (M : LM c v) (hok : M.ok) (hU : Unr c v) (hs : M.std) :
    SphN M.W := by
  refine GlobalTheory.CompanionTheory.StdSph.stdTh_sphN K h2 c v hU _ ?_
  cases M with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    obtain rfl : Φ = _ := hs
    exact Or.inl ⟨w₁, w₂, i₁, i₂, hok.1, rfl⟩
  | @ns w i σ η Φ =>
    obtain rfl : Φ = _ := hs
    exact Or.inr ⟨w, i, hok.1, σ, η, hok.2.1, hok.2.2.1, rfl⟩

theorem finiteComponent_unipotent (v : Pl) (x : 𝔸[ℚ]) : finAt v (uni2 x) = uni2 (x.2 v) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, GroundTheory.Automorphic.Reduction.finAt_apply] <;> rfl

theorem realPart_unipotent_adele (x : 𝔸[ℚ]) :
    GL2Classical.realPart (uni2 x) = uni2 (GP.eR (x.1 GP.wR)) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change RationalIdeles.realEquiv ((uni2 x : GL (Fin 2) 𝔸[ℚ]) i j).1 = _
  fin_cases i <;> fin_cases j <;> simp [uni2]
  all_goals first | exact (GlobalTheory.CompanionTheory.GL2Factorization.PT.eR_eq _).symm | exact Prod.fst_one | rfl

end GlobalTheory.CompanionTheory.GlobalWhittakerPsi
