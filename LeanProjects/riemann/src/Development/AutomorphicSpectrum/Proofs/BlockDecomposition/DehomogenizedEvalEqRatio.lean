import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ

theorem ev_dehomog_of_isUnder : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    ∀ (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), IsUnder w z → w ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) →
    ev (mpStr ℤ m n) σ₀ (mchart c) (dehomog c f) w =
      eval z (map (Int.castRingHom ℂ) f) / ∏ k, z ⟨k, c k⟩ ^ a k := by
  intro m n c f a hf w z H hw
  have hmem : ∀ k, w ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) := fun k =>
    GlobalTheory.CxPts.ptsIn_mono (mchart_le c k) hw
  have hX : ∀ q, GlobalTheory.CxPts.evHom hw (dehomog c (X q)) = z q / z ⟨q.1, c q.1⟩ := by
    rintro ⟨k, i⟩
    rw [← GlobalTheory.CxPts.ev_eq hw]
    simp only [dehomog, coe_eval₂Hom, eval₂_X]
    rw [GlobalTheory.CxPts.ev_res _ hw]
    exact (H k (c k)).2 i (hmem k)
  have hφ : (GlobalTheory.CxPts.evHom hw).comp (dehomog c) =
      eval₂Hom (Int.castRingHom ℂ) (fun q => z q / z ⟨q.1, c q.1⟩) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
    · simp
    · simpa using hX q
  have hv : GlobalTheory.CxPts.evHom hw (dehomog c f) =
      eval₂ (Int.castRingHom ℂ) (fun q => z q / z ⟨q.1, c q.1⟩) f := by
    simpa using congrArg (fun φ => φ f) hφ
  rw [GlobalTheory.CxPts.ev_eq hw, hv, MvPolynomial.eval_map, eval₂_eq', eval₂_eq', Finset.sum_div]
  refine Finset.sum_congr rfl fun e he => ?_
  have hden : ∏ q : Σ k, Bk n k, z ⟨q.1, c q.1⟩ ^ e q = ∏ k, z ⟨k, c k⟩ ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun i : Bk n k => e ⟨k, i⟩) (z ⟨k, c k⟩)).trans (by rw [hf e he k])
  simp only [div_pow, Finset.prod_div_distrib, hden]
  rw [mul_div_assoc]

end GlobalTheory.CompanionTheory.MixZ
