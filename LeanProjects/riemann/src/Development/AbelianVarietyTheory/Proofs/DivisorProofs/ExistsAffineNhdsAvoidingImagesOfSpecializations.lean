import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.BadOpen

theorem exists_affine_nhds_avoid : ∀ (X Y : Scheme.{0}) [IsIntegral X] (s : Y ⟶ X) [IsProper s] (T : Set Y) (σ : Y) (y : X) (N : CartierDiv X), T.Finite → (∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → ¬ s w ⤳ y) → ∃ (U : X.Opens) (e : X.functionFieldˣ), IsAffineOpen U ∧ y ∈ U ∧ (∀ x ∈ U, N.IsEqn x e) ∧ ∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → s w ∉ U := by
  intro X Y _ s _ T σ y N hT hbad
  obtain ⟨g, hg⟩ := N.exists_isEqn y
  obtain ⟨U₁, hyU₁, hU₁⟩ := hg.exists_nhds
  set C : Set X := ⋃ v ∈ T, s.base '' (closure {v} ∩ closure {σ}) with hC
  have hCc : IsClosed C := by
    refine hT.isClosed_biUnion fun v _ => ?_
    exact s.isClosedMap _ (isClosed_closure.inter isClosed_closure)
  have hyC : y ∉ C := by
    simp only [hC, Set.mem_iUnion, Set.mem_image, not_exists, not_and]
    intro v hv w hw hwy
    exact hbad v hv w (specializes_iff_mem_closure.2 hw.1) (specializes_iff_mem_closure.2 hw.2)
      (hwy ▸ specializes_rfl)
  let V : X.Opens := U₁ ⊓ ⟨Cᶜ, hCc.isOpen_compl⟩
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset (U := V) (x := y) ⟨hyU₁, hyC⟩
  refine ⟨W, g, hW, hyW, fun x hx => hU₁ x (hWV hx).1, fun v hv w hvw hσw hw => ?_⟩
  have := (hWV hw).2
  apply this
  simp only [hC, Set.mem_iUnion, Set.mem_image]
  exact ⟨v, hv, w, ⟨specializes_iff_mem_closure.1 hvw, specializes_iff_mem_closure.1 hσw⟩, rfl⟩

end GlobalTheory.BadOpen
