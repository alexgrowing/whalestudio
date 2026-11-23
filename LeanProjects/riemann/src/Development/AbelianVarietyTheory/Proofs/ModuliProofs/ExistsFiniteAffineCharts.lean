import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.FinAffineCharts

variable {X : Scheme.{0}}

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)ˣ) :
    res h₂ (res h₁ s) = res (h₂.trans h₁) s := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
    (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem cocycle_on {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have := congrArg (res (le_inf h₁ (h₂.trans inf_le_right) : W ≤ L.U i ⊓ L.U j ⊓ L.U k))
    (hL.cocycle i j k)
  rwa [map_mul, res_res, res_res, res_res] at this

noncomputable def refineLB (L : LB X) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) : LB X :=
  ⟨κ, W, fun a b => res (inf_le_inf (h a) (h b)) (L.g (c a) (c b))⟩

theorem refineLB_isLB {L : LB X} (hL : L.IsLB) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) (hc : ⨆ a, W a = ⊤) : (refineLB L W c h).IsLB where
  cover := hc
  g_self a := by
    have := congrArg (res (h a)) (hL.g_self (c a))
    rw [res_res, map_one] at this
    exact (res_res _ _ _).trans this
  cocycle a b d :=
    (congrArg₂ (· * ·) (res_res _ _ _) (res_res _ _ _)).trans
      ((cocycle_on hL _ _ _ _ _ _).trans (res_res _ _ _).symm)

theorem iso_refineLB {L : LB X} (hL : L.IsLB) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) : LBIso L (refineLB L W c h) := by
  refine ⟨⟨fun p => res (inf_le_inf_right _ (h p.1) : W p.1 ⊓ L.U p.2 ≤ L.U (c p.1) ⊓ L.U p.2)
    (L.g (c p.1) p.2)⟩, ?_⟩
  have key : ∀ (a b : κ) (i j : L.ι),
      res (inf_le_left : W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W a ⊓ L.U i)
        (res (inf_le_inf_right _ (h a) : W a ⊓ L.U i ≤ L.U (c a) ⊓ L.U i) (L.g (c a) i)) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W a ⊓ W b)
        (res (inf_le_inf (h a) (h b)) (L.g (c a) (c b))) *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ L.U i ⊓ L.U j) (L.g i j))⁻¹ *
      res (inf_le_right : W a ⊓ L.U i ⊓ (W b ⊓ L.U j) ≤ W b ⊓ L.U j)
        (res (inf_le_inf_right _ (h b) : W b ⊓ L.U j ≤ L.U (c b) ⊓ L.U j) (L.g (c b) j)) := by
    intro a b i j
    rw [res_res, res_res, res_res, mul_right_comm, cocycle_on hL (c a) (c b) j _ _
      (le_inf (inf_le_left.trans (inf_le_left.trans (h a))) (inf_le_right.trans inf_le_right)),
      eq_mul_inv_iff_mul_eq]
    exact cocycle_on hL _ _ _ _ _ _
  exact fun p q => key p.1 q.1 p.2 q.2

theorem exists_finite_affine_cover [CompactSpace X] (M : LB X) (hM : M.IsLB) :
    ∃ (κ : Type) (_ : Finite κ) (W : κ → X.Opens) (c : κ → M.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (c a)) ∧ ⨆ a, W a = ⊤ := by
  have h : ∀ x : X, ∃ (W : X.Opens) (c : M.ι), IsAffineOpen W ∧ x ∈ W ∧ W ≤ M.U c := by
    intro x
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hM.cover.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hc (M.U c).isOpen
    exact ⟨W, c, hW, hx, hle⟩
  choose W c hW hx hle using h
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨s, inferInstance, fun a => W a, fun a => c a, fun a => hW a, fun a => hle a,
    top_le_iff.1 ?_⟩
  intro x _
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

theorem exists_finite_affine_charts : ∀ (X : Scheme.{0}) (L : LB X), CompactSpace X → L.IsLB → ∃ L' : LB X, Finite L'.ι ∧ L'.IsLB ∧ (∀ i, IsAffineOpen (L'.U i)) ∧ LBIso L L' := by
  intro X L _ hL
  obtain ⟨κ, hκ, W, c, hW, h, hc⟩ := exists_finite_affine_cover L hL
  exact ⟨refineLB L W c h, hκ, refineLB_isLB hL W c h hc, hW, iso_refineLB hL W c h⟩

end GlobalTheory.FinAffineCharts
