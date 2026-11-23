import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem presheaf_map_map_eq_map {V : Scheme.{0}} {A B C : V.Opens} (i : B ⟶ A) (j : C ⟶ B)
    (k : C ⟶ A) (t : Γ(V, A)) :
    (V.presheaf.map j.op).hom ((V.presheaf.map i.op).hom t) = (V.presheaf.map k.op).hom t := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.glueSection :
    ∀ {V : Scheme.{0}} (U : V → V.Opens) (_ : ∀ x, x ∈ U x) (s : ∀ x, Γ((U x : Scheme.{0}), ⊤)), (∀ (x y : V) {S : Scheme.{0}} (f : S ⟶ (U x : Scheme.{0})) (f' : S ⟶ (U y : Scheme.{0})), f ≫ (U x).ι = f' ≫ (U y).ι → f.appTop.hom (s x) = f'.appTop.hom (s y)) → ∃ s₀ : Γ(V, ⊤), ∀ x, (U x).ι.appTop.hom s₀ = s x := by
  intro V U hU s h
  have hcov : (⊤ : V.Opens) ≤ iSup U := fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩
  have compat : TopCat.Presheaf.IsCompatible V.sheaf.1 U (fun x => (U x).topIso.hom (s x)) := by
    intro x y
    have hc := h x y (V.homOfLE (inf_le_left : U x ⊓ U y ≤ U x)) (V.homOfLE inf_le_right)
      (by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι])
    rw [Scheme.homOfLE_appTop, Scheme.homOfLE_appTop] at hc
    have hc' := congrArg (U x ⊓ U y).topIso.hom.hom hc
    simp only [Scheme.Opens.topIso_hom] at hc'
    have ky : U x ⊓ U y ⟶ (U y).ι ''ᵁ ⊤ := homOfLE (inf_le_right.trans (U y).ι_image_top.ge)
    exact (presheaf_map_map_eq_map (V := V) (A := (U x).ι ''ᵁ ⊤) _ _
        (homOfLE (inf_le_left.trans (U x).ι_image_top.ge)) (s x)).trans
      ((presheaf_map_map_eq_map (V := V) (A := (U x).ι ''ᵁ ⊤) _ _ _ (s x)).symm.trans
        (hc'.trans (presheaf_map_map_eq_map (V := V) (A := (U y).ι ''ᵁ ⊤) _ _ ky (s y)))
        |>.trans (presheaf_map_map_eq_map (V := V) (A := (U y).ι ''ᵁ ⊤) _ _ ky (s y)).symm)
  obtain ⟨s₀, hs₀, -⟩ := V.sheaf.existsUnique_gluing' U ⊤ (fun x => homOfLE le_top) hcov _ compat
  refine ⟨s₀, fun x => ?_⟩
  have e := congrArg (U x).topIso.inv.hom (hs₀ x)
  rw [Iso.hom_inv_id_apply] at e
  rw [← e, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
  exact (presheaf_map_map_eq_map (V := V) _ _ _ s₀).symm
