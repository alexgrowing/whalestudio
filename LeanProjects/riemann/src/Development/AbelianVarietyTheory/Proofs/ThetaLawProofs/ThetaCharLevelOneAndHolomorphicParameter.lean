import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLevelIffAut
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsLevBasisReal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta
open ReciprocityTheory.PTheta Matrix

private theorem levelTheta_one_zero {g : ℕ} (a b : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ)
    (z : Fin g → ℂ) : GlobalTheory.levelTheta a b 1 τ 0 z = theta a b z τ := by
  unfold GlobalTheory.levelTheta
  have e1 : ((fun i => ((0 : Fin g → ℤ) i : ℝ) / ((1 : ℕ) : ℝ)) + a) = a := by
    funext i; simp
  rw [e1]
  simp

theorem differentiableOn_thetaChar_comp {g : ℕ} {a b : Fin g → ℂ} (h : charHalf g a b)
    {w : (Fin g → Fin g → ℂ) → Fin g → ℂ} (hw : Differentiable ℂ w) :
    DifferentiableOn ℂ (fun p => thetaChar (per p) a b (w p)) (Key.phDom g) := by
  obtain ⟨ha, hb⟩ := h
  have hF := GlobalTheory.KeyKa.LevelBasis.holFam_levelTheta (fun i => (a i).re) (fun i => (b i).re) Nat.one_pos 0
  unfold GlobalTheory.KeyKa.HolFam at hF
  simp only [levelTheta_one_zero] at hF
  have hm : Differentiable ℂ (fun p : Fin g → Fin g → ℂ => (p, w p)) := by fun_prop
  refine (hF.comp hm.differentiableOn (fun p hp => ⟨hp, Set.mem_univ _⟩)).congr (fun p _ => ?_)
  rw [GlobalTheory.TorusAlg.thetaChar_eq_theta _ ha hb]
  rfl

theorem differentiable_per_apply {g : ℕ} (i j : Fin g) :
    Differentiable ℂ (fun p : Fin g → Fin g → ℂ => per p i j) := by
  simp only [GlobalTheory.KeyKa.per, ReciprocityTheory.ChartRestriction.G.Key.phSym, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul]
  fun_prop

theorem differentiable_lat {g : ℕ} (k n : Fin g → ℤ) :
    Differentiable ℂ (fun p : Fin g → Fin g → ℂ => lat (per p) k n) := by
  rw [differentiable_pi]
  intro i
  have hp := differentiable_per_apply (g := g)
  simp only [lat, Pi.add_apply, Matrix.mulVec, dotProduct]
  fun_prop

theorem differentiable_tors {g : ℕ} (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (r : Fin 4) :
    Differentiable ℂ (fun p : Fin g → Fin g → ℂ => tors (per p) al m k n r) := by
  have hl : ∀ c, Differentiable ℂ (fun p : Fin g → Fin g → ℂ => lat (per p) (k c) (n c)) :=
    fun c => differentiable_lat (k c) (n c)
  unfold tors
  exact (Differentiable.fun_sum fun c _ => (hl c).const_smul (al r c)).const_smul ((m : ℂ)⁻¹)

theorem level_one_and_holomorphic : ∀ (g : ℕ) (a b : Fin g → ℂ), charHalf g a b → (∀ p ∈ Key.phDom g, IsLevel (per p) a b 1 (thetaChar (per p) a b)) ∧ (∀ (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ), DifferentiableOn ℂ (fun p => simTheta (per p) a b al m k n y) (Key.phDom g)) ∧ ∀ (k n : Fin g → ℤ) (z : Fin g → ℂ), Differentiable ℂ (fun p : Fin g → Fin g → ℂ => aut (per p) a b k n z) := by
  intro g a b h
  refine ⟨fun p hp => ?_, fun al m k n y => ?_, fun k n z => ?_⟩
  · have hτ : per p ∈ SiegelH (Fin g) := hp
    obtain ⟨ha, hb⟩ := h
    have e := GlobalTheory.KeyKa.LevelBasis.isLevel_iff (per p) (fun i => (a i).re) (fun i => (b i).re) 1
      (thetaChar (per p) a b)
    rw [GlobalTheory.TorusAlg.ofRealVec_re ha, GlobalTheory.TorusAlg.ofRealVec_re hb] at e
    rw [e, (GlobalTheory.TorusAlg.thetaChar_level hτ.1 hτ.2 ha hb).2.1]
    exact Submodule.mem_span_singleton_self _
  · unfold simTheta
    have hθ : ∀ r, DifferentiableOn ℂ
        (fun p => thetaChar (per p) a b (∑ c, al r c • y c + tors (per p) al m k n r)) (Key.phDom g) :=
      fun r => differentiableOn_thetaChar_comp h
        ((differentiable_const _).add (differentiable_tors al m k n r))
    have hprod : DifferentiableOn ℂ
        (∏ r, fun p => thetaChar (per p) a b (∑ c, al r c • y c + tors (per p) al m k n r))
        (Key.phDom g) :=
      Finset.prod_induction _ (fun F => DifferentiableOn ℂ F (Key.phDom g))
        (fun _ _ h1 h2 => h1.mul h2) (differentiableOn_const 1) (fun r _ => hθ r)
    rw [Finset.prod_fn] at hprod
    exact hprod.mul (differentiableOn_const _)
  · have hp := differentiable_per_apply (g := g)
    simp only [aut, Matrix.mulVec, dotProduct]
    fun_prop

end GlobalTheory.SimilTheta
end
