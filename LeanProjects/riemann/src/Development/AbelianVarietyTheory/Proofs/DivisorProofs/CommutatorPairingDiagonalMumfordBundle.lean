import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagWeil

theorem diag_psum (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (I : Finset (Fin 2)) :
    lift (𝟙 A) (𝟙 A) ≫ psum A (x2 A) I = psum A ![𝟙 A, 𝟙 A] I := by
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl <;>
    simp [psum, padd, pzero, x2, List.finRange_succ]

theorem lbIso_lam_diag (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB) :
    LBIso ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) (cubeLB A ![𝟙 A, 𝟙 A] M) := by
  refine GlobalTheory.PrimNorm.lbIso_nested hM _ _ _ _ _ _ ?_
  simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [← Over.comp_left, diag_psum]

end GlobalTheory.DiagWeil

open GlobalTheory.TorusRM.DiagFrame in

theorem GlobalTheory.DiagWeil.weilIs_diag_lam : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (N : LB A.left), N.IsLB → LBIso N (cubeLB A ![𝟙 A, 𝟙 A] M) → Out.RelAmple A N → ∀ (k : ℕ) (a b : Fin g → ℂ) (c : ℂˣ), 0 < k → a ∈ u.Λ → b ∈ u.Λ → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((2 * (hermForm Hm a b).im : ℝ)) : ℂ) / k) → Out.WeilIs A N k (u.ex ((k : ℂ)⁻¹ • a)) (u.ex ((k : ℂ)⁻¹ • b)) (unitOn c) := by
  intro A _ _ g hA _ M u Hm χ hM hF N hN hNc hamp k a b c hk ha hb hc
  have : IsProper A.hom := hA.proper
  have hL : ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB (LB.isLB_linComb hM _ _) _
  have hcube : (cubeLB A ![𝟙 A, 𝟙 A] M).IsLB := LB.isLB_linComb hM _ _
  have hLN : LBIso ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) N :=
    LBIso.trans hL hcube hN (GlobalTheory.DiagWeil.lbIso_lam_diag A hM) hNc.symm
  have hampL : Out.RelAmple A ((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left) :=
    GlobalTheory.AmpleApprox.relAmple_of_lbIso_self hN hL hLN hamp
  have hF' := isFactorAH_diagUnif u hF
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ hL hampL g (diagUnif u) _ _ hF'.1 hF'.2.1 hF'.2.2
  have hAH := GlobalTheory.TorusRM.isAH_of_isFactorAH hF' hpos
  have hc' : (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (((a ⬝ᵥ ((2 : ℂ) • Hm).mulVec (star b)).im : ℝ) : ℂ) / k) := by
    rw [hc]
    congr 4
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_im]
    simp [hermForm]
  have hw := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm A hA _ hL g (diagUnif u) _ _ hAH k a b c hk ha hb hc'
  rw [diagUnif_ex] at hw
  exact GlobalTheory.PELFamily.weilIs_of_lbIso GlobalTheory.globalFns_holds hA hN hL
    (LBIso.trans hN hL (pull_isLB hL _) hLN.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hL)) hw
