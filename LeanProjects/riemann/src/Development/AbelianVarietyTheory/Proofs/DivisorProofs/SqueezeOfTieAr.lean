import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolHomog
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionUpperDenseSmallStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

theorem squeeze_of_tieAr : GlobalTheory.Published.VolNef → GlobalTheory.Published.VolGe → GlobalTheory.Published.ArCalc →
    ∀ (D : D7) (Y : ShimX D.what₂.Tau) (A : SlopeTestRemainingChoices Y), TieAr A → Squeeze A := by
  intro h1 h2 h3 D Y A hT L hs hn c e
  obtain ⟨m, H, hsp, hnf, n, ν, r, hn0, hν, hSI, hg, hx₁, -, hr, hd⟩ := hT.exists_rel hs hn c
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hpos : 0 < ν * (n : ℝ) ^ (dimY Y + 1) := by positivity
  have key : ((dimY Y : ℝ) + 1) * (n * e) * gdeg H (dimY Y) =
      ν * (n : ℝ) ^ (dimY Y + 1) * (((dimY Y : ℝ) + 1) * e * Y.geoC L c) := by
    rw [hg]; ring
  refine ⟨fun hy => ?_, fun ⟨Z, hZ, hy⟩ => ?_⟩
  · have := GlobalTheory.T.self_intersection_lower_height h1 h3 m.k m.X m.p (dimY Y) m.av H _ (n * e) hsp hnf hSI
      (fun x hx => have ⟨y, h⟩ := hx₁ x hx
        ⟨_, (hr x y h).2.2, mul_le_mul_of_nonneg_left (hy _ (hr x y h).2.1) hn'.le⟩)
    rw [key] at this
    exact le_of_mul_le_mul_left this hpos
  · have := GlobalTheory.T.self_intersection_upper_dense_small h2 h3 m.k m.X m.p (dimY Y) m.av H _ (n * e) hsp hnf hSI
      (Dense.mono (fun x hx => by
        obtain ⟨y, hyZ, h⟩ := hx
        exact ⟨(hr x y h).1, _, (hr x y h).2.2, mul_le_mul_of_nonneg_left (hy _ hyZ) hn'.le⟩) (hd Z hZ))
    rw [key] at this
    exact le_of_mul_le_mul_left this hpos

end GlobalTheory.Mean4O
