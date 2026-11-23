import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPrBPtMP
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePointOfNonvanishingCoordsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectiveChartHolomorphicCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicSectionSmoothCompositionStatement
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.MPSmooth

theorem smooth_of_isHermRep : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)),
    IsHermRep M A → Geo.IsSmoothHerm A := by
  rintro m n M A ⟨u, -, -, hA⟩ z₀ hz₀
  choose c hc using hz₀
  refine ContDiffAt.contDiffWithinAt ?_
  let T : Set ((Σ k, Bk n k) → ℂ) := {z | ∀ k, z ⟨k, c k⟩ ≠ 0}
  have hT : IsOpen T := by
    have : T = ⋂ k, {z : (Σ k, Bk n k) → ℂ | z ⟨k, c k⟩ ≠ 0} := by ext; simp [T]
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
  have hz : z₀ ∈ T := hc
  let s := multiprojectivePoint (m := m) (n := n) c
  obtain ⟨haff, hgen⟩ := GlobalTheory.T.multiprojective_chart_holomorphic_coordinates m n c
  have hmem : ∀ z ∈ T, s z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := fun z h => (GlobalTheory.T.multiprojective_point_of_nonvanishing_coords m n c z h).2
  obtain ⟨hcont, hholo⟩ := holo_of_affine haff hT hmem hgen
  obtain ⟨i, hi⟩ := exists_mem_ptsIn M.isLB.cover (s z₀)
  have hV : s z₀ ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) := mem_ptsIn_inf.2 ⟨hi, hmem z₀ hz⟩

  let F : CxPts (mpStr ℤ m n) σ₀ → ℝ := fun y =>
    ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
      Real.exp ((M.φ σ₀).φ i y / 2)
  have hF : CInfAt F (s z₀) := by
    have h1 : CInfAt (fun y => ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)
        (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖) (s z₀) := by
      refine ⟨M.B.U i ⊓ mchart c, Unit, inferInstance, fun _ => (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)),
        fun v => ‖v ()‖, {v | v () ≠ 0}, hV, isOpen_ne_fun (continuous_apply _) continuous_const,
        ev_ne_zero hV (u i c).isUnit, ?_, Filter.EventuallyEq.rfl⟩
      intro v hv
      exact ((contDiffAt_norm ℝ hv).comp v ((contDiff_apply ℝ ℂ ()).contDiffAt)).contDiffWithinAt
    have h2 := (M.cInf σ₀) i (s z₀) hi
    exact h1.comp₂ h2 (G := fun x => x.1 * Real.exp (x.2 / 2))
      (contDiff_fst.mul (Real.contDiff_exp.comp (contDiff_snd.div_const 2)))
  have hFs := GlobalTheory.T.holomorphic_section_smooth_composition hT hcont hholo hz hF
  have hP : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) z₀ := by
    refine contDiffAt_prod fun k _ => ?_
    have hn : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ‖z ⟨k, c k⟩‖) z₀ :=
      (contDiffAt_norm ℝ (hc k)).comp z₀ ((contDiff_apply ℝ ℂ (⟨k, c k⟩ : Σ k, Bk n k)).contDiffAt)
    have hx : ‖z₀ ⟨k, c k⟩‖ ≠ 0 := norm_ne_zero_iff.2 (hc k)
    cases h : A.a k with
    | ofNat j =>
      simp only [Int.ofNat_eq_natCast, zpow_natCast]
      exact hn.pow j
    | negSucc j =>
      simp only [zpow_negSucc]
      exact (hn.pow (j + 1)).inv (pow_ne_zero _ hx)
  refine (hP.mul hFs).congr_of_eventuallyEq ?_
  have hnb : ∀ᶠ z in nhds z₀, z ∈ T ∧ s z ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) :=
    Filter.Eventually.and (hT.mem_nhds hz) ((hcont.continuousAt (hT.mem_nhds hz)).preimage_mem_nhds ((isOpen_ptsIn _).mem_nhds hV))
  filter_upwards [hnb] with z hz'
  rw [hA i c (s z) z (GlobalTheory.T.multiprojective_point_of_nonvanishing_coords m n c z hz'.1).1 hz'.2]
  simp only [F, Function.comp_apply]
  ring

end GlobalTheory.CompanionTheory.MPSmooth
