import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finite_affine_chart_cover : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), QuasiCompact G.hom → ∀ (L : LB G.left), L.IsLB → ∃ (n : ℕ) (j : Fin n → L.ι) (W : Fin n → G.left.Opens) (U : Fin n → M.S.Opens), (⨆ b, W b = ⊤) ∧ (∀ b, W b ≤ L.U (j b)) ∧ (∀ b, W b ≤ G.hom ⁻¹ᵁ U b) ∧ (∀ b, IsAffineOpen (W b)) ∧ (∀ b, IsAffineOpen (U b)) := by
  intro R _ _ M G hG L hL
  haveI := M.proper
  haveI : CompactSpace M.S := QuasiCompact.compactSpace_of_compactSpace M.π
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hx : ∀ x : G.left, ∃ (j : L.ι) (W : G.left.Opens) (U : M.S.Opens),
      x ∈ W ∧ W ≤ L.U j ∧ W ≤ G.hom ⁻¹ᵁ U ∧ IsAffineOpen W ∧ IsAffineOpen U := by
    intro x
    have hxt : x ∈ (⊤ : G.left.Opens) := trivial
    rw [← hL.cover] at hxt
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxt
    obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 M.S.isBasis_affineOpens)
      (show G.hom x ∈ (⊤ : M.S.Opens) from trivial)
    obtain ⟨W, hW, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 G.left.isBasis_affineOpens)
      (show x ∈ L.U j ⊓ G.hom ⁻¹ᵁ U from ⟨hj, hxU⟩)
    exact ⟨j, W, U, hxW, hWle.trans inf_le_left, hWle.trans inf_le_right, hW, hU⟩
  choose j W U hxW hWj hWU hWa hUa using hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set G.left)) (fun x => (W x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  let e := t.equivFin
  refine ⟨t.card, fun b => j (e.symm b), fun b => W (e.symm b), fun b => U (e.symm b), ?_,
    fun b => hWj _, fun b => hWU _, fun b => hWa _, fun b => hUa _⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨e ⟨y, hy⟩, by simpa using hxy⟩

end GlobalTheory.Mum
