import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPrBPtMP
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

theorem differentiableOn_eval₂_ratio (N : ℕ) (c : Fin (N + 1))
    (p : MvPolynomial {j : Fin (N + 1) // j ≠ c} ℤ) :
    DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ =>
      MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun j : {j // j ≠ c} => w j.1 / w c) p)
      {w | w c ≠ 0} := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    exact differentiableOn_const _
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at hp ⊢
    have hj : DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ => w j.1) {w | w c ≠ 0} :=
      (differentiable_apply j.1).differentiableOn
    have hc : DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ => w c) {w | w c ≠ 0} :=
      (differentiable_apply c).differentiableOn
    have hinv : DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ => (w c)⁻¹) {w | w c ≠ 0} :=
      fun w hw => (hc w hw).inv hw
    simp only [div_eq_mul_inv]
    exact hp.mul (hj.mul hinv)

theorem differentiableOn_ev_ptP (N : ℕ) (c : Fin (N + 1)) (a : Γ(PSpace ℤ N, chart ℤ N c)) :
    DifferentiableOn ℂ (fun w => CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) a (ptP N c w))
      {w | w c ≠ 0} := by
  have h : (fun w => CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) a (ptP N c w)) =
      fun w : Fin (N + 1) → ℂ => MvPolynomial.eval₂Hom (Int.castRingHom ℂ)
        (fun j : {j // j ≠ c} => w j.1 / w c) ((chartAlgEquiv ℤ N c).symm a) := by
    funext w
    exact CxPts.ev_ofHom _ _ _ a
  rw [h]
  exact differentiableOn_eval₂_ratio N c _

end GlobalTheory.CompanionTheory.MPSmooth
