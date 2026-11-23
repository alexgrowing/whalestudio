import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPrBPtMP
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectivePointChartRatioStatement
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem mem_blockChart_iff (y : CxPts (mpStr ℤ m n) σ₀) (k : Fin (m + 1)) (i : Bk n k) :
    y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔
      GlobalTheory.Points.PtsOver.map (prB n k) (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) _ y ∈
        ptsIn (PSpace.str ℤ (n k)) σ₀ (chart ℤ (n k) i) :=
  Iff.rfl

theorem ev_pullRatio (y : CxPts (mpStr ℤ m n) σ₀) (k : Fin (m + 1)) (i j : Bk n k) :
    CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y =
      CxPts.ev (PSpace.str ℤ (n k)) σ₀ (chart ℤ (n k) i) (ratio ℤ (n k) i j)
        (GlobalTheory.Points.PtsOver.map (prB n k) (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) _ y) := by
  have e : pullRatio (prB n k) (blockChart n k i) i le_rfl j = (prB n k).app (chart ℤ (n k) i) (ratio ℤ (n k) i j) := by
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  rw [e]
  exact CxPts.ev_app (p := PSpace.str ℤ (n k)) (q := mpStr ℤ m n) (prB n k)
    (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) (chart ℤ (n k) i) (ratio ℤ (n k) i j) y

theorem isUnder_ptMP (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ)
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) :
    IsUnder (GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z) z ∧ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := by
  have H : IsUnder (multiprojectivePoint c z) z := fun k i => by
    obtain ⟨h₁, h₂⟩ := GlobalTheory.T.projective_point_chart_ratio (n k) (c k) (fun i => z ⟨k, i⟩) (hz k)
    have e := map_prB_ptMP c z k
    refine ⟨?_, fun j hy => ?_⟩
    · rw [mem_blockChart_iff, e]
      exact h₁ i
    · rw [ev_pullRatio, e]
      exact h₂ i j (by rw [← e]; exact (mem_blockChart_iff _ k i).1 hy)
  refine ⟨H, CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => ?_)⟩
  exact CxPts.mem_ptsIn.1 ((H k (c k)).1.2 (hz k))

end GlobalTheory.CompanionTheory.MPSmooth
