import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

def refinePull {X Y : Scheme.{0}} (A : LB Y) (π : X ⟶ Y) {I : Type} (V : I → X.Opens) (idx : I → A.ι)
    (le : ∀ l, V l ≤ π ⁻¹ᵁ A.U (idx l)) : LB X where
  «ι» := I
  U := V
  g l l' := res (show V l ⊓ V l' ≤ π ⁻¹ᵁ (A.U (idx l) ⊓ A.U (idx l')) from fun _ hy => ⟨le l hy.1, le l' hy.2⟩)
    (pullU π _ (A.g (idx l) (idx l')))

theorem gm_refinePull {X Y : Scheme.{0}} (A : LB Y) (π : X ⟶ Y) {I : Type} (V : I → X.Opens) (idx : I → A.ι)
    (le : ∀ l, V l ≤ π ⁻¹ᵁ A.U (idx l)) (y : X) (l l' : I) (h : y ∈ V l) (h' : y ∈ V l') :
    gm (𝟙 X) y (V l ⊓ V l') ((refinePull A π V idx le).g l l') =
      gm π y (A.U (idx l) ⊓ A.U (idx l')) (A.g (idx l) (idx l')) := by
  have hm : (𝟙 X : X ⟶ X) y ∈ V l ⊓ V l' := ⟨h, h'⟩
  refine (gm_res (𝟙 X) y _ hm _).trans ((gm_pull (𝟙 X) π y (A.U (idx l) ⊓ A.U (idx l'))
    ⟨le l h, le l' h'⟩ _).trans ?_)
  rw [Category.id_comp]

theorem refinePull_isLB {X Y : Scheme.{0}} (A : LB Y) (hA : A.IsLB) (π : X ⟶ Y) {I : Type} (V : I → X.Opens)
    (idx : I → A.ι) (le : ∀ l, V l ≤ π ⁻¹ᵁ A.U (idx l)) (hV : ⨆ l, V l = ⊤) : (refinePull A π V idx le).IsLB := by
  refine ⟨hV, fun (l : I) => unit_ext (V := V l) fun y hy => ?_,
    fun (i j k : I) => unit_ext (V := V i ⊓ V j ⊓ V k) fun y hy => ?_⟩
  · refine (gm_res (𝟙 X) y _ hy _).trans ((gm_refinePull A π V idx le y l l hy hy).trans ?_)
    exact (mul_eq_left.1 (gm_cocycle hA π y (le l hy) (le l hy) (le l hy))).trans (map_one _).symm
  · refine (map_mul _ _ _).trans ((congrArg₂ (· * ·)
      ((gm_res (𝟙 X) y _ hy _).trans (gm_refinePull A π V idx le y i j hy.1.1 hy.1.2))
      ((gm_res (𝟙 X) y _ hy _).trans (gm_refinePull A π V idx le y j k hy.1.2 hy.2))).trans
      ((gm_cocycle hA π y (le i hy.1.1) (le j hy.1.2) (le k hy.2)).trans
      ((gm_res (𝟙 X) y _ hy _).trans (gm_refinePull A π V idx le y i k hy.1.1 hy.2)).symm))

theorem exists_mem_splitChart {S : Scheme.{0}} (E : SplitExt S) (y : E.B.left) : ∃ j, y ∈ E.chart j := by
  classical
  choose j hj using fun k : Module.Free.ChooseBasisIndex ℤ E.X => exists_chart (E.O (E.basis k)).isLB y
  refine ⟨j, ?_⟩
  show y ∈ ((⨅ k, (E.O (E.basis k)).L.U (j k) : E.B.left.Opens) : Set E.B.left)
  rw [TopologicalSpace.Opens.coe_iInf]
  exact Set.mem_iInter.2 hj

theorem exists_affine_refinement : ∀ (S : Scheme.{0}) (E : SplitExt S) (Y : Scheme.{0}) (A : LB Y), A.IsLB → ∀ π : E.B.left ⟶ Y, ∃ N₀ : LB E.B.left, N₀.IsLB ∧ (∀ l, IsAffineOpen (N₀.U l)) ∧ (∀ l, ∃ j, N₀.U l ≤ E.chart j) ∧ Nonempty (ChartPull N₀ A π) := by
  intro S E Y A hA π
  have key : ∀ y : E.B.left, ∃ (V : E.B.left.Opens) (i : A.ι), y ∈ V ∧ IsAffineOpen V ∧ V ≤ π ⁻¹ᵁ A.U i ∧
      ∃ j, V ≤ E.chart j := fun y => by
    obtain ⟨i, hi⟩ := exists_chart hA (π y)
    obtain ⟨j, hj⟩ := exists_mem_splitChart E y
    obtain ⟨V, hV, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := π ⁻¹ᵁ A.U i ⊓ E.chart j) ⟨hi, hj⟩
    exact ⟨V, i, hy, hV, fun z hz => (hle hz).1, j, fun z hz => (hle hz).2⟩
  choose V idx hy haff le hch using key
  refine ⟨refinePull A π V idx le, refinePull_isLB A hA π V idx le ?_, haff, hch,
    ⟨⟨idx, le, fun y l l' h h' => gm_refinePull A π V idx le y l l' h h'⟩⟩⟩
  exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩

end GlobalTheory.ZH.UFib
end
