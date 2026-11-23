import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm
import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

noncomputable section
namespace GlobalTheory.KeyEq

theorem normalAt_scale :
    ∀ (P : Out.PolAV (Sp ℂ)) (hg rig hr th hth v hv th' hth' v' hv') (a : ℂ) (N : Matrix (Fin P.g) (Fin P.g) ℂ), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (N i) v (v' i)) → a ≠ 0 ∧ N.det ≠ 0 ∧ ∀ (τ M : Matrix (Fin P.g) (Fin P.g) ℂ) (α β : Fin P.g → ℂ) (c : ℂ), NormalAt ⟨P, hg, rig, hr, th, hth, v, hv⟩ τ M α β c → NormalAt ⟨P, hg, rig, hr, th', hth', v', hv'⟩ τ (N * M) α β (a * c) := by
  intro P hg rig hr th hth v hv th' hth' v' hv' a N ha hN
  haveI := P.isAb.comm
  obtain ⟨-, -, -, -, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v hv.1
  refine ⟨?_, ((bas N v' hv hN).1 hv').ne_zero, ?_⟩
  · rintro rfl
    obtain ⟨y, -, hy⟩ := hth' (IsLocalRing.closedPoint ℂ)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  · rintro τ M α β c ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩
    refine ⟨u, h₁, h₂, h₃, h₄, ?_, ?_⟩
    · intro i z hz
      have e := h₅ i z hz
      refine ((congrArg (valAt' _ _) (ha i)).trans (valAt'_mul _ _ _ _)).trans ?_
      rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
      refine (congrArg (a * ·) e).trans ?_
      beta_reduce
      simp only [_root_.mul_assoc]
    · intro i
      have h1 := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 h₆ (hN i)
      have e : ∑ j, N i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
          (2 * Real.pi * Complex.I : ℂ)⁻¹ • (N * M) i := by
        simp only [smul_comm (N i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
        rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum]
        rfl
      rwa [e] at h1

end GlobalTheory.KeyEq
end
