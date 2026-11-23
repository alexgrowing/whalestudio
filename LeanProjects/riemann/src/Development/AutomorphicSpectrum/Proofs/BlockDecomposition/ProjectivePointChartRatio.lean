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

theorem ptP_mem_chart (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) :
    ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N c) :=
  CxPts.ofHom_mem _ _ _

theorem ev_ptP (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (a : Γ(PSpace ℤ N, chart ℤ N c)) :
    CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) a (ptP N c w) = chartHom N c w a :=
  CxPts.ev_ofHom _ _ _ a

theorem ev_ptP_ratio (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0)
    (i : Fin (N + 1)) :
    CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) (ratio ℤ N c i) (ptP N c w) = w i / w c := by
  rw [ev_ptP]
  by_cases h : i = c
  · subst h
    rw [ratio, ratioOn_self, map_one, div_self hc]
  · have e : (chartAlgEquiv ℤ N c).symm (ratio ℤ N c i) = X ⟨i, h⟩ := by
      rw [← chartAlgEquiv_X ℤ N c ⟨i, h⟩]
      exact AlgEquiv.symm_apply_apply _ _
    simp [chartHom, e]

theorem ptP_mem_chart_iff (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0)
    (i : Fin (N + 1)) :
    ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) ↔ w i ≠ 0 := by
  have e := CxPts.mem_ptsIn_basicOpen (ptP_mem_chart N c w) (ratio ℤ N c i)
  rw [ratio, basicOpen_ratioOn, CxPts.mem_ptsIn_inf] at e
  rw [← ratio, ev_ptP_ratio N c w hc i] at e
  constructor
  · intro h
    have := e.1 ⟨ptP_mem_chart N c w, h⟩
    exact fun h0 => this (by rw [h0, zero_div])
  · intro h
    exact (e.2 (div_ne_zero h hc)).2

theorem ptP_chart (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0) :
    (∀ i, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) ↔ w i ≠ 0) ∧
    ∀ i j, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) →
      CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N i) (ratio ℤ N i j) (GlobalTheory.CompanionTheory.MPSmooth.ptP N c w) =
        w j / w i := by
  refine ⟨ptP_mem_chart_iff N c w hc, fun i j hi => ?_⟩
  have hwi : w i ≠ 0 := (ptP_mem_chart_iff N c w hc i).1 hi
  have hW : ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i) :=
    CxPts.mem_ptsIn_inf.2 ⟨ptP_mem_chart N c w, hi⟩
  have h₁ : ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left i *
      ratioOn (chart ℤ N c ⊓ chart ℤ N i) i inf_le_right j =
      ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left j :=
    ratioOn_mul_ratioOn
  have h₂ := congrArg (fun f => CxPts.ev (PSpace.str ℤ N) σ₀ _ f (ptP N c w)) h₁
  simp only [CxPts.ev_mul] at h₂
  have ea : ∀ k, CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i)
      (ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left k) (ptP N c w) = w k / w c := fun k =>
    (CxPts.ev_res inf_le_left hW (ratio ℤ N c k)).trans (ev_ptP_ratio N c w hc k)
  have eb : CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i)
      (ratioOn (chart ℤ N c ⊓ chart ℤ N i) i inf_le_right j) (ptP N c w) =
      CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N i) (ratio ℤ N i j) (ptP N c w) :=
    CxPts.ev_res inf_le_right hW (ratio ℤ N i j)
  rw [ea, ea, eb] at h₂
  field_simp at h₂ ⊢
  exact h₂

end GlobalTheory.CompanionTheory.MPSmooth
