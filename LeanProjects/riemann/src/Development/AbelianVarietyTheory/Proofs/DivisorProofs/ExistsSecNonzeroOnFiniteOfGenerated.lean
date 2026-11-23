import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionVanishes
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open GlobalTheory.ZeroDimSystem in

theorem exists_sec_nonzero_on_finite_of_generated :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X), L.IsLB → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∀ S : Set X, S.Finite → ∃ s : L.Sec, ∀ x ∈ S, x ∈ nonzeroLocus s := by
  intro k _ _ X _ p L _ n u hu S hS
  classical
  letI : Algebra k Γ(X, ⊤) := (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have hne : ∀ x ∈ hS.toFinset, vanishAt (k := k) u x ≠ ⊤ := fun x _ h => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hu.ge (Set.mem_univ x))
    exact single_notMem_vanishAt (k := k) u hi (h.symm ▸ Submodule.mem_top)
  have h := Subspace.biUnion_ne_univ_of_top_notMem (k := k) (E := Fin n → k)
    (s := hS.toFinset.image (vanishAt (k := k) u)) (by
      rw [Finset.mem_image]
      rintro ⟨x, hx, h⟩
      exact hne x hx h)
  obtain ⟨c, hc⟩ := (Set.ne_univ_iff_exists_notMem _).1 h
  refine ⟨comb u c, fun x hx => ?_⟩
  by_contra hxc
  exact hc (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hS.mem_toFinset.2 hx)))
    ((mem_vanishAt u x c).2 hxc))

end GlobalTheory
