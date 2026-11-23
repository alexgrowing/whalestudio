import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem imgLoc_app_res {X Y : Scheme.{0}} (a : Y ⟶ X) {U U' : X.Opens} (i : U' ⟶ U)
    (j : a ⁻¹ᵁ U' ⟶ a ⁻¹ᵁ U) (y : Γ(X, U)) :
    (Y.presheaf.map j.op).hom ((a.app U).hom y) = (a.app U').hom ((X.presheaf.map i.op).hom y) := by
  have hj : j = (TopologicalSpace.Opens.map a.base).map i := Subsingleton.elim _ _
  subst hj
  have e := a.naturality i.op
  have := congrArg (fun f => f.hom y) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

theorem imgLoc_exists {X Y : Scheme.{0}} (a : Y ⟶ X) (hinj : ∀ U : X.Opens, Function.Injective (a.app U).hom)
    (V : X.Opens) {B : Type} (W : B → X.Opens) (hV : V ≤ ⨆ b, W b) (x : Γ(Y, a ⁻¹ᵁ V))
    (hx : ∀ b, ∃ y : Γ(X, V ⊓ W b), (a.app (V ⊓ W b)).hom y =
      (Y.presheaf.map (homOfLE (extLI_preimage_mono a (inf_le_left : V ⊓ W b ≤ V))).op).hom x) :
    ∃ y : Γ(X, V), (a.app V).hom y = x := by
  choose y hy using hx
  have hcov : V ≤ ⨆ b, V ⊓ W b := by
    calc V ≤ V ⊓ ⨆ b, W b := le_inf le_rfl hV
      _ = ⨆ b, V ⊓ W b := inf_iSup_eq _ _
  have key : ∀ b (U' : X.Opens) (i : U' ⟶ V ⊓ W b), (a.app U').hom ((X.presheaf.map i.op).hom (y b)) =
      (Y.presheaf.map (homOfLE (extLI_preimage_mono a (i.le.trans inf_le_left))).op).hom x := by
    intro b U' i
    rw [← imgLoc_app_res a i (homOfLE (extLI_preimage_mono a i.le)), hy b, extLI_res_res]
  have compat : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun b => V ⊓ W b) y := by
    intro b c
    apply hinj
    exact (key b _ _).trans (key c _ _).symm
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun b => V ⊓ W b) V
    (fun b => homOfLE inf_le_left) hcov y compat
  have hcovY : a ⁻¹ᵁ V ≤ ⨆ b, a ⁻¹ᵁ (V ⊓ W b) := by
    intro z hz
    obtain ⟨b, hb⟩ := (TopologicalSpace.Opens.mem_iSup).1 (hcov hz)
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨b, hb⟩
  have hs' : ∀ b, (X.presheaf.map (homOfLE inf_le_left : V ⊓ W b ⟶ V).op).hom s = y b := hs
  refine ⟨s, ?_⟩
  refine Y.sheaf.eq_of_locally_eq' (fun b => a ⁻¹ᵁ (V ⊓ W b)) (a ⁻¹ᵁ V)
    (fun b => homOfLE (extLI_preimage_mono a inf_le_left)) hcovY _ _ (fun b => ?_)
  have h2 := imgLoc_app_res a (homOfLE inf_le_left : V ⊓ W b ⟶ V)
    (homOfLE (extLI_preimage_mono a inf_le_left)) s
  rw [hs' b, hy b] at h2
  exact h2

end GlobalTheory.Mum
