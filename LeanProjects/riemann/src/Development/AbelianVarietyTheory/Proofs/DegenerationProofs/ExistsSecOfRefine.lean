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

theorem gs_sec_compat {Y Z : Scheme.{0}} {M : LB Y} (φ : M.Sec) (r : Z ⟶ Y) (z : Z) {l l' : M.ι}
    (hl : r z ∈ M.U l) (hl' : r z ∈ M.U l') :
    gs r z (M.U l) (φ.f l) = (gm r z (M.U l ⊓ M.U l') (M.g l l')).val * gs r z (M.U l') (φ.f l') := by
  have hm : r z ∈ M.U l ⊓ M.U l' := ⟨hl, hl'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (φ.compat l l')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem exists_sec_of_refine : ∀ (Y : Scheme.{0}) (M A : LB Y), M.IsLB → A.IsLB →
    ∀ (c : ChartPull M A (𝟙 Y)) (φ : M.Sec), ∃ s : A.Sec, ∀ (l : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ M.U l → gs r z (M.U l) (φ.f l) = gs r z (A.U (c.idx l)) (s.f (c.idx l)) := by
  intro Y M A hM hA c φ
  have cle : ∀ l (y : Y), y ∈ M.U l → y ∈ A.U (c.idx l) := fun l y hy => c.le l hy
  have glue : ∀ i : A.ι, ∃ a : Γ(Y, A.U i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : M.ι),
      r z ∈ A.U i → r z ∈ M.U l →
      gs r z _ a = (gm r z (A.U i ⊓ A.U (c.idx l)) (A.g i (c.idx l))).val * gs r z (M.U l) (φ.f l) := by
    intro i
    let W : M.ι → Y.Opens := fun l => A.U i ⊓ M.U l
    have hW : ∀ l, W l ≤ A.U i ⊓ A.U (c.idx l) := fun l y hy => ⟨hy.1, cle l y hy.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, W l), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) l, r z ∈ W l →
        gs r z (W l) (u l) =
          (gm r z (A.U i ⊓ A.U (c.idx l)) (A.g i (c.idx l))).val * gs r z (M.U l) (φ.f l) :=
      ⟨fun l => (Y.presheaf.map (homOfLE (hW l)).op).hom (A.g i (c.idx l)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W l ≤ M.U l)).op).hom (φ.f l), fun Z r z l hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans (gs_unit r z _ (hW l hz) _))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (A.U i)
      (fun l => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨l, hl⟩ := exists_chart hM y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hy, hl⟩) u
      (fun l l' => fn_ext (V := W l ⊓ W l') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y l hy.1, hu _ _ y l' hy.2, gs_sec_compat φ (𝟙 Y) y hy.1.2 hy.2.2, c.g y l l' hy.1.2 hy.2.2,
          ← _root_.mul_assoc, ← Units.val_mul,
          gm_cocycle hA (𝟙 Y) y hy.1.1 (cle l y hy.1.2) (cle l' y hy.2.2)])
    refine ⟨a, fun Z r z l h₁ h₂ => ?_⟩
    have hz : r z ∈ W l := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W l)) (ha l)).trans (hu Z r z l hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun l Z r z hl => ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hM y
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit (𝟙 Y) y _ hy _) (gs_res (𝟙 Y) y _ hy _))).symm)
    rw [ha j _ (𝟙 Y) y l hy.1 hl, ha j' _ (𝟙 Y) y l hy.2 hl,
      ← gm_cocycle hA (𝟙 Y) y hy.1 hy.2 (cle l y hl), Units.val_mul, _root_.mul_assoc]
  · have m := cle l _ hl
    refine Eq.symm ((ha _ Z r z l m hl).trans ?_)
    rw [gm_self hA r z m, Units.val_one, _root_.one_mul]

end GlobalTheory.ZH.UFib
end
