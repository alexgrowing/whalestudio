import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTwistedBundleExistsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem exists_block_ne_zero_of_isUnder {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (h : IsUnder y z) (k : Fin (m + 1)) :
    ∃ i, z ⟨k, i⟩ ≠ 0 :=
  ⟨ptChart _ k, (h k _).1.1 (CxPts.mem_ptsIn.2 (mem_ptChart _ k))⟩

theorem combLine_unit_a (A : HermLine (Bk n)) : (combLine (fun _ : Unit => A) 1).a = A.a := by
  simp [combLine]

theorem combLine_unit_h (A : HermLine (Bk n)) {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (combLine (fun _ : Unit => A) 1).h z = A.h z := by
  simp [combLine, if_pos hz]

theorem combLine_unit_h_off (A : HermLine (Bk n)) {z : (Σ k, Bk n k) → ℂ} (hz : ¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (combLine (fun _ : Unit => A) 1).h z = 0 :=
  if_neg hz

theorem isHermRep_combLine_unit {M : HermLB (mpStr ℤ m n)} {A : HermLine (Bk n)} (hA : IsHermRep M A) :
    IsHermRep M (combLine (fun _ : Unit => A) 1) := by
  obtain ⟨u, h₁, h₂, h₃⟩ := hA
  refine ⟨u, h₁, fun i c c' => ?_, fun i c y z hu hy => ?_⟩
  · rw [combLine_unit_a]
    exact h₂ i c c'
  · rw [combLine_unit_h A (exists_block_ne_zero_of_isUnder hu), combLine_unit_a]
    exact h₃ i c y z hu hy

theorem existsRead : ExistsRead := by
  rintro m n M ⟨c, t, e⟩
  obtain ⟨A, hA, -⟩ := GlobalTheory.T.hermRep_twisted_bundle_exists m n M c t e
  have hs : IsSmoothHerm A := GlobalTheory.CompanionTheory.MPDict.SmoothRep.isSmoothHerm_of_isHermRep m n M A hA
  exact ⟨combLine (fun _ : Unit => A) 1, isSmoothHerm_combLine (fun _ => hs) 1, isHermRep_combLine_unit hA,
    fun z hz => combLine_unit_h_off A hz⟩

end GlobalTheory.CompanionTheory.MixZ
