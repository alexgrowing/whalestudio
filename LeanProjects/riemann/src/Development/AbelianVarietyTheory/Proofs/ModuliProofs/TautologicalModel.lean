import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Proof.TautologicalModel

section Taut

variable {X X' Y Z : Scheme.{0}}

theorem taut_le (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') (J : PUnit → L.ι) (K : PUnit → PUnit → L.ι) :
    (L.pull (p ≫ F)).U J ⊓ ((L.pull F).pull p).U K ≤ (p ≫ F) ⁻¹ᵁ (L.U (J ⟨⟩) ⊓ L.U (K ⟨⟩ ⟨⟩)) := fun _ hy =>
  ⟨mem_pull.1 hy.1, mem_pull (L := L) (F := F).1 (mem_pull (L := L.pull F) (F := p).1 hy.2)⟩

def taut (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') : LB.Iso ((L.pull F).pull p) (L.pull (p ≫ F)) :=
  ⟨fun q => res (taut_le L F p q.1 q.2) (pullU (p ≫ F) _ (L.g (q.1 ⟨⟩) (q.2 ⟨⟩ ⟨⟩)))⟩

theorem gw_taut (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') (f : Z ⟶ Y) (z : Z) (j : L.ι) (k : PUnit → PUnit → L.ι)
    (hj : (p ≫ F) (f z) ∈ L.U j) (hk : f z ∈ ((L.pull F).pull p).U k) :
    gw (taut L F p) f z j k = gm (f ≫ p ≫ F) z _ (L.g j (k ⟨⟩ ⟨⟩)) := by
  have hm : f z ∈ (L.pull (p ≫ F)).U (fun _ => j) ⊓ ((L.pull F).pull p).U k := ⟨mem_pull.2 hj, hk⟩
  exact (gm_res f z (taut_le L F p _ k) hm _).trans (gm_pull f (p ≫ F) z _ (taut_le L F p _ k hm) _)

theorem taut_isGen {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) (p : Y ⟶ X') : (taut L F p).IsGen := by
  refine (isGen_iff _).2 fun Z f z j j' k k' hj hj' hk hk' => ?_
  have h1 : (f ≫ p) z ∈ (L.pull F).U (k ⟨⟩) := mem_pull (L := L.pull F) (F := p).1 hk
  have h1' : (f ≫ p) z ∈ (L.pull F).U (k' ⟨⟩) := mem_pull (L := L.pull F) (F := p).1 hk'
  have h2 : (f ≫ p ≫ F) z ∈ L.U (k ⟨⟩ ⟨⟩) := mem_pull (L := L) (F := F).1 h1
  have h2' : (f ≫ p ≫ F) z ∈ L.U (k' ⟨⟩ ⟨⟩) := mem_pull (L := L) (F := F).1 h1'
  rw [gw_taut L F p f z j k hj hk, gw_taut L F p f z j' k' hj' hk', gm_pull_g (L.pull F) p f z k k' hk hk',
    gm_pull_g L F (f ≫ p) z _ _ h1 h1', Category.assoc,
    ← gm_cocycle hL (f ≫ p ≫ F) z (i := j) (j := j') hj hj' h2,
    ← gm_cocycle hL (f ≫ p ≫ F) z (i := j') (j := k ⟨⟩ ⟨⟩) hj' h2 h2']
  generalize gm (f ≫ p ≫ F) z _ (L.g j j') = A
  generalize gm (f ≫ p ≫ F) z _ (L.g j' (k ⟨⟩ ⟨⟩)) = B
  generalize gm (f ≫ p ≫ F) z _ (L.g (k ⟨⟩ ⟨⟩) (k' ⟨⟩ ⟨⟩)) = C
  rw [_root_.mul_comm B C, _root_.mul_assoc, inv_mul_cancel_left]

end Taut

section Rig

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]

theorem gm_rigPullOf (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) {Z : Scheme.{0}}
    (f : Z ⟶ (𝟙_ (Over S')).left) (z : Z) (j : PUnit → PUnit → L.ι)
    (hj : f z ∈ LB.wchart (L.pull F) (fun _ : PUnit => eSec G') j) :
    gm f z (LB.wchart (L.pull F) (fun _ : PUnit => eSec G') j) ((rigPullOf F e he L r).s j) =
      gm (f ≫ e) z (LB.wchart L (fun _ : PUnit => eSec G) (fun _ => j ⟨⟩ ⟨⟩)) (r.s (fun _ => j ⟨⟩ ⟨⟩)) :=
  (gm_res f z (rigPull_le F e he L j) hj _).trans (gm_pull f e z _ (rigPull_le F e he L j hj) _)

theorem rigPullOf_isGen (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) (hr : r.IsGen) :
    (rigPullOf F e he L r).IsGen := by
  intro i j
  refine unit_ext fun y hy => ?_
  have hi' := rigPull_le F e he L i hy.1
  have hj' := rigPull_le F e he L j hy.2
  refine ((gm_res _ y _ hy _).trans (gm_rigPullOf F e he L r (𝟙 _) y i hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g (L.pull F) (eSec G') (𝟙 _) y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans (gm_rigPullOf F e he L r (𝟙 _) y j hy.2)))).trans ?_
  rw [gen_trans (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) hr (𝟙 _ ≫ e) y hi' hj', trF, Fintype.prod_unique,
    zpow_one, gm_pull_g L F (𝟙 _ ≫ eSec G') y (i ⟨⟩) (j ⟨⟩) (mem_pull (L := L.pull F) (F := eSec G').1 hy.1)
      (mem_pull (L := L.pull F) (F := eSec G').1 hy.2), Category.assoc, Category.assoc, he]

end Rig

end GlobalTheory.Proof.TautologicalModel
end
