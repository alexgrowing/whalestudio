import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt

theorem exists_tens_sec_finite_subset_nonzeroLocus : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsAmb q → ∀ (M : HermLB q) (S : Set Y), S.Finite →
      ∃ (A : HermLB q) (s : (M.tens A).B.Sec) (u : A.B.Sec), S ⊆ nonzeroLocus s ∧ S ⊆ nonzeroLocus u := by
  intro k _ Y q hq M S hS
  have := hq.isNoetherian
  obtain ⟨N, j, hj, e⟩ := hq.isProjOver
  let A₀ : HermLB q := (ProjSpace.hermitianTwistingSheaf k N).pull j e
  have hA : IsAmpleLB A₀.B := (isAmple_projective_O_one k N).pull_of_isClosedImmersion j
  obtain ⟨n, h₁, h₂⟩ := (tendsto_natCast_atTop_atTop.eventually
    ((hA.eventually_exists_finite_subset_nonzeroLocus M.isLB hS).and
      (hA.eventually_exists_finite_subset_nonzeroLocus (LB.isLB_triv Y) hS))).exists
  obtain ⟨s, hs⟩ := h₁ (CechPic.tens M.B (lbPow A₀.B n)) (isLB_tens M.isLB (isLB_lbPow A₀.isLB n)) (by
    rw [cls_tens M.isLB (isLB_lbPow A₀.isLB n), cls_lbPow A₀.isLB, natCast_zsmul])
  obtain ⟨u, hu⟩ := h₂ (lbPow A₀.B n) (isLB_lbPow A₀.isLB n) (by
    rw [cls_lbPow A₀.isLB, cls_triv, zero_add, natCast_zsmul])
  exact ⟨A₀.pow n, s, u, hs, hu⟩

end GlobalTheory.MixHt
