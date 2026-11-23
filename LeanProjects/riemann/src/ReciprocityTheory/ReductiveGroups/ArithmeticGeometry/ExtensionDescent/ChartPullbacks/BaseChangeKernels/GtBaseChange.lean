import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.PreLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.TransPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.CmapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.AffineSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.SurjOfCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.UnitNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.UnitsEq

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

open Semi Geo.Tor PullGtPf

attribute [local instance] SplitExt.free SplitExt.finite

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S)

lemma res_val_res {X : Scheme.{0}} {U V₁ V₂ : X.Opens} (h₁ : V₁ ≤ U) (h₂ : V₂ ≤ U) (h : V₁ ≤ V₂)
    (u : Γ(X, U)ˣ) :
    (res h₁ u).val = (X.presheaf.map (homOfLE h).op).hom (res h₂ u).val := by
  show (X.presheaf.map (homOfLE h₁).op).hom u.val =
    (X.presheaf.map (homOfLE h).op).hom ((X.presheaf.map (homOfLE h₂).op).hom u.val)
  have e : (homOfLE h₁).op = (homOfLE h₂).op ≫ (homOfLE h).op := by
    first
    | rfl
    | exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [e, Functor.map_comp]
  rfl

section Datum

variable {G : Over S} [GrpObj G] (d : E.GtDatum G)

lemma hleG (j : (pullExt f E).ChartIdx) {V : E.B.left.Opens} {V₁ : ((Over.pullback f).obj E.B).left.Opens}
    (h₁ : V₁ ≤ pullback.fst E.B.hom f ⁻¹ᵁ V) :
    (qB f d.q).left ⁻¹ᵁ V₁ ≤ pullback.fst G.hom f ⁻¹ᵁ (d.q.left ⁻¹ᵁ V) := by
  have key : ((qB f d.q).left ≫ pullback.fst E.B.hom f) ⁻¹ᵁ V
      = (pullback.fst G.hom f ≫ d.q.left) ⁻¹ᵁ V := by
    first
    | rw [qB_h]
    | exact congrArg (fun g => g ⁻¹ᵁ V) (qB_h f d.q)
  calc (qB f d.q).left ⁻¹ᵁ V₁ ≤ (qB f d.q).left ⁻¹ᵁ (pullback.fst E.B.hom f ⁻¹ᵁ V) :=
        (qB f d.q).left.preimage_mono h₁
    _ = ((qB f d.q).left ≫ pullback.fst E.B.hom f) ⁻¹ᵁ V := by
        first
        | rfl
        | exact (Scheme.preimage_comp _ _ _).symm
    _ = (pullback.fst G.hom f ≫ d.q.left) ⁻¹ᵁ V := key
    _ = pullback.fst G.hom f ⁻¹ᵁ (d.q.left ⁻¹ᵁ V) := by
        first
        | rfl
        | exact Scheme.preimage_comp _ _ _

set_option maxHeartbeats 800000 in

def datum : (pullExt f E).GtDatum ((Over.pullback f).obj G) where
  q := qB f d.q
  i := iB f E.X d.i
  q_hom := by
    haveI := d.q_hom
    exact isMonHom_of_grpPullback (isGrpPullback_pullback G f) (isGrpPullback_pullback E.B f) d.q
      (qB f d.q) (qB_h f d.q)
  i_hom := by
    haveI := d.i_hom
    exact iB_hom f E.X d.i
  q_flat := qB_flat f d.q d.q_flat
  q_surjective := qB_surj f d.q d.q_surjective
  q_affine := qB_affine f d.q d.q_affine
  isKernel := iB_isKernel f E.X d.q d.i d.isKernel
  u := uB f E d
  coord := fun j V hV h => by
    refine coord_glue (qB f d.q).left (W := (pullExt f E).chart j)
      (fun V' h' => cmap (pullExt f E).basis
        (fun k => res ((qB f d.q).left.preimage_mono h') (uB f E d j k)))
      (fun V₁ V₂ h₁ h₂ h x => cmap_comp _ _ _ _ (fun k => res_val_res _ _ _ _) x) ?_ V hV h
    intro x hx
    have hFx : pullback.fst E.B.hom f x ∈ E.chart (jj f E j) := chart_le f E j hx
    obtain ⟨V, hVa, hxV, hVle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 E.B.left.isBasis_affineOpens hFx
    refine ⟨(pullExt f E).chart j ⊓ pullback.fst E.B.hom f ⁻¹ᵁ V, inf_le_left, ⟨hx, hxV⟩,
      fun V₁ h₁ hV₁ => ?_⟩
    exact affineBCSt (qB_sq f d.q) d.q_affine hVa hV₁ (h₁.trans inf_le_right)
      (hleG f E d j (h₁.trans inf_le_right))
      (cmap E.basis (fun k => res (d.q.left.preimage_mono hVle) (d.u (jj f E j) k))) _
      (fun y => cmap_comp _ _ _ _ (fun k => appLE_res _ _ _ _ _ _) y) (d.coord (jj f E j) V hVa hVle)
  trans := fun j j' k => trans_pull (pullback.fst G.hom f) d.q.left (qB f d.q).left
    (pullback.fst E.B.hom f) (qB_h f d.q) (E.O (E.basis k)).L (j k PUnit.unit) (j' k PUnit.unit)
    (E.chart_le (jj f E j) k) (E.chart_le (jj f E j') k) ((pullExt f E).chart_le j k)
    ((pullExt f E).chart_le j' k) (d.u (jj f E j) k) (d.u (jj f E j') k)
    (d.trans (jj f E j) (jj f E j') k) (pre_le f E d j) (pre_le f E d j')
  act_le := actB_le f E d
  equiv := equivB f E d
  unit_norm := unit_normB f E d

end Datum

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V)
    (u : Γ(X, U)ˣ) : res h' (res h u) = res (h'.trans h) u := by
  ext
  exact (res_val_res (h'.trans h) h h' u).symm

private lemma gen_div_self_lemma_2 {X : Scheme.{0}} (M : LB X) (hM : M.IsLB) :
    ∃ t : LB.Gen (LB.div M M), t.IsGen := by
  refine ⟨⟨fun p => M.g p.1 p.2⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨c, d⟩
  try dsimp only [LB.div]
  have e1 := congrArg (res (show M.U a ⊓ M.U b ⊓ (M.U c ⊓ M.U d) ≤ M.U a ⊓ M.U c ⊓ M.U d from
    le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (inf_le_right.trans inf_le_right))) (hM.cocycle a c d)
  have e2 := congrArg (res (show M.U a ⊓ M.U b ⊓ (M.U c ⊓ M.U d) ≤ M.U a ⊓ M.U b ⊓ M.U d from
    le_inf inf_le_left (inf_le_right.trans inf_le_right))) (hM.cocycle a b d)
  simp only [map_mul, res_res_lemma] at e1 e2
  have e3 := eq_mul_inv_of_mul_eq e2
  rw [← e1] at e3
  exact e3.trans (mul_right_comm _ _ _)

theorem gtBaseChange : GtBaseChangeSt := by
  intro S S' f E G _ hG
  obtain ⟨d⟩ := hG
  refine ⟨pullExt f E, AddEquiv.refl _, Iso.refl _, ?_, fun χ => ?_, Nonempty.intro (datum f E d)⟩
  · first
    | exact (inferInstance : IsMonHom (𝟙 ((Over.pullback f).obj E.B)))
    | (rw [Iso.refl_hom]; infer_instance)
    | (constructor <;> simp <;> rfl)
  · show ∃ w : LB.Iso ((E.O χ).L.pull (𝟙 (pullback E.B.hom f) ≫ pullback.fst E.B.hom f))
        ((E.O χ).L.pull (mB f E).F), w.IsGen
    rw [mB_F, Category.id_comp]
    exact gen_div_self_lemma_2 _ (LB.isLB_pull (E.O χ).isLB _)

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
