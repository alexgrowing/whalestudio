import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixPull

theorem hess_pull {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (π : Y ⟶ X) (hπ : π ≫ p = q) (A : MLine p σ) (c : AlgChart p σ D) (c' : AlgChart q σ D)
    (H : ∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w))
    (z : CxPts q σ) (hz : z ∈ c'.e.source) :
    c'.hess (A.pull π hπ).φ (pick (A.pull π hπ).φ.isLB z) z = c.hess A.φ (pick A.φ.isLB (ptMap π hπ σ z)) (ptMap π hπ σ z) := by
  have hz' := (H z hz).1
  have hj := mem_of_mem_linComb (m := fun _ => PtsOver.map π hπ _ z) (fun _ => rfl)
    (mem_pick (A.φ.pull π hπ).isLB z) PUnit.unit
  rw [c.hess_eq A.cInf hz' hj (mem_pick _ _)]
  show c'.hess (A.φ.pull π hπ) _ z = _
  unfold AlgChart.hess
  rw [← (H z hz).2]
  refine ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_
  filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hz)] with v hv
  have hw := c'.e.map_target hv
  obtain ⟨h₁, h₂⟩ := H _ hw
  rw [c'.e.right_inv hv] at h₂
  have e₁ : c.e.symm v = PtsOver.map π hπ (spMap σ) (c'.e.symm v) := by
    exact (congrArg c.e.symm h₂).trans (c.e.left_inv h₁)
  rw [e₁]
  exact congrArg _ (A.φ.pull_φ π hπ _ _)

theorem dens_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (π : Y ⟶ X) (hπ : π ≫ p = q) (L : Fin D → MLine p σ) (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w)) → ∀ w ∈ c'.e.source, dens (fun i => (L i).pull π hπ) c' w = dens L c (ptMap π hπ σ w) := by
  intro k _ X Y p q σ D π hπ L c c' H w hw
  have e : ∀ τ : Equiv.Perm (Fin D), (Matrix.of fun j l =>
      c'.hess ((fun i => (L i).pull π hπ) (τ l)).φ (pick ((fun i => (L i).pull π hπ) (τ l)).φ.isLB w) w j l) =
      Matrix.of fun j l => c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB (ptMap π hπ σ w)) (ptMap π hπ σ w) j l := by
    intro τ
    ext j l
    simp only [Matrix.of_apply]
    rw [hess_pull π hπ (L (τ l)) c c' H w hw]
  simp only [dens, e]

end GlobalTheory.MixPull
