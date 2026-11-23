import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.LocalFrames

theorem span_eq_of_saturated : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E) (S : Finset (Fin g)), IsCptGen ξ → Submodule.span Ω (Set.range b) = ⊤ → L p = Submodule.span (regAt ξ p) (Set.range b) → (L.inter V') p = Submodule.span (regAt ξ p) (b '' S) → V' = Submodule.span Ω (b '' S) := by
  intro X Ω _ ξ E _ _ L V' p g b S h hspan hL hI
  haveI hfr : IsFractionRing (regAt ξ p) Ω := (RegAtRing.regAt_ring X Ω ξ h p).1
  have sm : ∀ (c : regAt ξ p) {m : E}, m ∈ L p → (c : Ω) • m ∈ L p := fun c _ hm => (L p).smul_mem c hm
  have key : ∀ x : E, ∃ d : regAt ξ p, (d : Ω) ≠ 0 ∧ (d : Ω) • x ∈ L p := by
    intro x
    have hx : x ∈ Submodule.span Ω (Set.range b) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      refine ⟨1, by simp, ?_⟩
      rw [hL]
      simpa using Submodule.subset_span hy
    | zero => exact ⟨1, by simp, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨d, hd, hdy⟩ := hy
      obtain ⟨e, he, hez⟩ := hz
      refine ⟨d * e, by rw [Subring.coe_mul]; exact mul_ne_zero hd he, ?_⟩
      have : ((d * e : regAt ξ p) : Ω) • (y + z) = (e : Ω) • ((d : Ω) • y) + (d : Ω) • ((e : Ω) • z) := by
        simp only [Subring.coe_mul, smul_add, smul_smul, mul_comm]
      rw [this]
      exact (L p).add_mem (sm e hdy) (sm d hez)
    | smul a y _ hy =>
      obtain ⟨d, hd, hdy⟩ := hy
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := regAt ξ p) a
      have hv0 : (v : Ω) ≠ 0 := by
        have := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := Ω) hv
        simpa using this
      refine ⟨v * d, by rw [Subring.coe_mul]; exact mul_ne_zero hv0 hd, ?_⟩
      have : ((v * d : regAt ξ p) : Ω) • ((algebraMap (regAt ξ p) Ω u / algebraMap (regAt ξ p) Ω v) • y) =
          (u : Ω) • ((d : Ω) • y) := by
        have hu : algebraMap (regAt ξ p) Ω u = (u : Ω) := rfl
        have hv' : algebraMap (regAt ξ p) Ω v = (v : Ω) := rfl
        rw [hu, hv', smul_smul, smul_smul, Subring.coe_mul]
        congr 1
        field_simp
      rw [this]
      exact sm u hdy
  apply le_antisymm
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := key x
    have h1 : (d : Ω) • x ∈ (L.inter V') p := ⟨hdx, V'.smul_mem _ hx⟩
    rw [hI] at h1
    have h2 : (d : Ω) • x ∈ Submodule.span Ω (b '' S) :=
      Submodule.span_subset_span (regAt ξ p) Ω (b '' S) h1
    exact (Submodule.smul_mem_iff _ hd).1 h2
  · rw [Submodule.span_le]
    intro y hy
    have h1 : y ∈ (L.inter V') p := by
      rw [hI]
      exact Submodule.subset_span hy
    exact h1.2

end GlobalTheory.CompanionTheory.Ar.LocalFrames
