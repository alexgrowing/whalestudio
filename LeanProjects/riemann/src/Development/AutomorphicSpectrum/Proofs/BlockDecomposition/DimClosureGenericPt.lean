import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvProdBlockUnit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianLineBundleSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdNormPull
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImageZMCoordIdealOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldMapPtCoordSndM

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.CompanionTheory.MPDict
open GlobalTheory.ArithmeticHeightTower ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem charZero_genericPt {n' m : ℕ} {n : Fin (m + 1) → ℕ} {Y : Scheme.{0}} [IsIntegral Y]
    {j : Y ⟶ MP ℤ (m + 1) (consN n' n)} {e : ℕ} (hvar : GlobalTheory.IsArithVar (j ≫ qpStr n' m n) e) :
    CharZero ((MP ℤ (m + 1) (consN n' n)).residueField (j (genericPoint Y))) := by
  haveI h0 : CharZero Γ(Y, ⊤) := hvar.charZero
  have hinj : Function.Injective ((Y.residue (genericPoint Y)).hom.comp
      (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom) :=
    (Y.residue (genericPoint Y)).hom.injective.comp (germ_injective_of_isIntegral Y _ _)
  haveI h1 : CharZero (Y.residueField (genericPoint Y)) := charZero_of_injective_ringHom hinj
  exact (RingHom.charZero_iff (j.residueFieldMap (genericPoint Y)).hom.injective).2 h1

theorem charZero_image (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n))
    [hx : CharZero ((MP ℤ (m + 1) (consN n' n)).residueField x)] :
    CharZero ((MP ℤ m n).residueField (qpSnd n' m n x)) := by
  let F : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n
  exact (RingHom.charZero_iff (F.residueFieldMap x).hom.injective).2 hx

theorem dim_closure_genericPt {n' m : ℕ} {n : Fin (m + 1) → ℕ} {Y : Scheme.{0}} [IsIntegral Y]
    {j : Y ⟶ MP ℤ (m + 1) (consN n' n)} [IsClosedImmersion j] {e : ℕ}
    (hvar : GlobalTheory.IsArithVar (j ≫ qpStr n' m n) e) :
    topologicalKrullDim (closure ({j (genericPoint Y)} : Set (MP ℤ (m + 1) (consN n' n)))) = ((e + 1 : ℕ) : _) := by
  have hrange : Set.range j = closure {j (genericPoint Y)} := by
    have h₁ := (genericPoint_spec Y).image j.continuous
    rw [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  exact (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).trans hvar.dim_eq

end GlobalTheory.CompanionTheory.MPDict
