import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieImagePoly

theorem exists_isLieImage_aeval (A : Over (Sp ℂ)) [GrpObj A] (Lb : LB A.left) (g : ℕ) (u : HolUnif A Lb g)
    (α : A ⟶ A) [IsMonHom α] (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (hD : ∀ z, u.ex (D z) = u.ex z ≫ α)
    (h : HdR A) (v : epsR ℂ ⟶ A) (w : Fin g → ℂ) (c : ℂ) (hv : IsLieImage h v) (hw : u.IsDiff w v)
    (hc : D w = c • w) (Q : Polynomial ℂ) :
    ∃ v', IsLieImage (Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α) Q h) v' ∧ u.IsDiff (Q.eval c • w) v' := by
  induction Q using Polynomial.induction_on with
  | C a =>
    refine ⟨GlobalTheory.GrpTangent.epsScale a ≫ v, ?_, ?_⟩
    · rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
      exact hv.smul a
    · rw [Polynomial.eval_C]
      exact GlobalTheory.PeriodLattice.isDiff_epsScale u hw a
  | add p q hp hq =>
    obtain ⟨v₁, h₁, d₁⟩ := hp
    obtain ⟨v₂, h₂, d₂⟩ := hq
    refine ⟨v₁ * v₂, ?_, ?_⟩
    · rw [map_add, LinearMap.add_apply]
      exact h₁.add h₂
    · rw [Polynomial.eval_add, add_smul]
      exact GlobalTheory.UnifDifferential.isDiff_mul u ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 h₁.1)
        ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 h₂.1) d₁ d₂
  | monomial n a ih =>
    obtain ⟨v₁, h₁, d₁⟩ := ih
    refine ⟨v₁ ≫ α, ?_, ?_⟩
    · have e : Polynomial.C a * Polynomial.X ^ (n + 1) = Polynomial.X * (Polynomial.C a * Polynomial.X ^ n) := by ring
      rw [e, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
      exact h₁.push α
    · have e : Polynomial.eval c (Polynomial.C a * Polynomial.X ^ (n + 1)) =
          c * Polynomial.eval c (Polynomial.C a * Polynomial.X ^ n) := by simp [pow_succ]; ring
      have k := GlobalTheory.UnifLieBasis.isDiff_comp u α D hD h₁.1 d₁
      rwa [map_smul, hc, smul_smul, mul_comm, ← e] at k

end GlobalTheory.LieImagePoly
