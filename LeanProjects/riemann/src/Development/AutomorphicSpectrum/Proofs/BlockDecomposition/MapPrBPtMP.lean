import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

def chartHom (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) : Γ(PSpace ℤ N, chart ℤ N c) →+* ℂ :=
  (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun j : {j // j ≠ c} => w j.1 / w c)).comp
    (chartAlgEquiv ℤ N c).symm.toRingEquiv.toRingHom

def ptP (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) : CxPts (PSpace.str ℤ N) σ₀ :=
  CxPts.ofHom (isAffineOpen_chart ℤ N c) (chartHom N c w)
    (fun a => RingHom.congr_fun (RingHom.ext_int ((chartHom N c w).comp (DVR.FlatBC.algX _ _)) σ₀) a)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def multiprojectivePoint (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) : CxPts (mpStr ℤ m n) σ₀ :=
  ⟨GroundTheory.Arith.SchemeCoh.ProjSpace.lift m n (spMap σ₀)
      (fun k => (ptP (n k) (c k) (fun i => z ⟨k, i⟩)).1) (fun k => (ptP (n k) (c k) (fun i => z ⟨k, i⟩)).2),
    GroundTheory.Arith.SchemeCoh.ProjSpace.lift_mpStr _ _ _ _ _⟩

theorem map_prB_ptMP (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) (k : Fin (m + 1)) :
    (GlobalTheory.Points.PtsOver.map (prB n k) (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) _ (multiprojectivePoint c z)) =
      ptP (n k) (c k) (fun i => z ⟨k, i⟩) :=
  Subtype.ext (GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ _ _ _ _ k)

end GlobalTheory.CompanionTheory.MPSmooth
