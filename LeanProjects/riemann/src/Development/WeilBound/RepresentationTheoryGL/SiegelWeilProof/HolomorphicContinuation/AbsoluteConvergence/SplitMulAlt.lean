import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HzBound

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.FarK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.Far

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem split_mul (x₀ : G) (y k : GR n) : x₀ * ι y * ι k = x₀ * ι (y * k) := by
  rw [mul_assoc, ← map_mul]

theorem cont_hz (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I)
    (z : ℂ) (b : GR n) (x : G) : Continuous fun k : KR n => hz Ht sec s₀ z 1 (x * ι ((k : GR n) * b)) := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  have hfun : (fun k : KR n => hz Ht sec s₀ z 1 (x₀ * ι y * ι ((k : GR n) * b))) =
      fun k : KR n => ((r * hLoc (y * (k : GR n) * b) : ℝ) : ℂ) ^ (z - s₀) * (S * F0 p q e (y * (k : GR n) * b)) := by
    funext k
    unfold hz
    rw [split_mul, ← mul_assoc y (k : GR n) b, (h _).1, (h _).2 1, hL.vac]
  rw [hfun]
  have hc : Continuous fun k : KR n => y * (k : GR n) * b :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  refine Continuous.mul ?_ (continuous_const.mul ((continuous_weight_factor hD p q e).comp hc))
  refine Continuous.cpow ?_ continuous_const (fun k => ?_)
  · exact Complex.continuous_ofReal.comp (continuous_const.mul ((continuous_hLoc hD).comp hc))
  · exact Complex.ofReal_mem_slitPlane.mpr (mul_pos hr (hLoc_pos hD _))

theorem pointId [MeasurableSpace (KR n)] (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) {ν : Measure (KR n)} {κ : KR n → ℂ} {N : ℕ}
    {yy : Fin N → GR n} {QQ : Fin N → PX m n} {M : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hMid : ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
        F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y')
    (z : ℂ) (i : Fin N) (x : G) :
    ∫ k, κ k * hz Ht sec s₀ z 1 (x * ι ((k : GR n) * yy i)) ∂ν = ∑ j, M (z - s₀) i j * hz Ht sec s₀ z (QQ j) x := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  have hfun : (fun k : KR n => κ k * hz Ht sec s₀ z 1 (x₀ * ι y * ι ((k : GR n) * yy i))) =
      fun k : KR n => ((r : ℂ) ^ (z - s₀) * S) *
        (κ k * ((hLoc (y * (k : GR n) * yy i) : ℂ) ^ (z - s₀) * F0 p q e (y * (k : GR n) * yy i))) := by
    funext k
    unfold hz
    rw [split_mul, ← mul_assoc y (k : GR n) (yy i), (h _).1, (h _).2 1, hL.vac, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_pos hD _).le]
    ring
  rw [hfun, integral_const_mul, hMid (z - s₀) i y, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold hz
  rw [(h y).1, (h y).2 (QQ j), Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_pos hD _).le]
  ring

end PositivityTheory.Rg.Sw.AbsSt.FarK
