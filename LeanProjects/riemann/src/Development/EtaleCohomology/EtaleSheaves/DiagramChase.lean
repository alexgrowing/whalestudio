import Development.EtaleCohomology.EtaleSheaves.ContStepPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.StepSPf

def PO (q : ℕ) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D) (j0 : J) (W : (D.obj j0).Opens) : Prop :=
  ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj (c.π.app j0 ⁻¹ᵁ W).toScheme) n i, ∃ (k : J) (f : k ⟶ j0)
      (y : Ht q (sch.obj (D.map f ⁻¹ᵁ W).toScheme) n i),
      pull _ (sch.map ((c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, c.w]))) _ _ y = x) ∧
  ∀ (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (D.map f ⁻¹ᵁ W).toScheme) n i),
    pull _ (sch.map ((c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, c.w]))) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map ((D.map g).resLE (D.map f ⁻¹ᵁ W) (D.map (g ≫ f) ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp]))) _ _ y = 0

def Restr : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X)
  (W : X.Opens), IsCompact (W : Set X) → PC W.toScheme → PO q D c j0 (e.hom ⁻¹ᵁ W)

def DiagramChase₂ : Prop := Hyp → MV → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X)
  (U V : X.Opens), U ⊔ V = ⊤ → PO q D c j0 (e.hom ⁻¹ᵁ U) → PO q D c j0 (e.hom ⁻¹ᵁ V) → PO q D c j0 (e.hom ⁻¹ᵁ (U ⊓ V)) →
  ∀ n i : ℤ, ∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x

theorem S_of_restr_chase (hR : Restr) (hC : DiagramChase₂) : LateralTheory.E.ContStepPf.StepS := by
  intro h hmv X U V hU hV hUV pU pV pW q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated e.inv
  have hW : IsCompact ((U ⊓ V : X.Opens) : Set X) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU V.2 hV
  exact hC h hmv q D c hc ha hcs hqs hu j0 X e U V hUV (hR q D c hc ha hcs hqs hu j0 X e U hU pU)
    (hR q D c hc ha hcs hqs hu j0 X e V hV pV) (hR q D c hc ha hcs hqs hu j0 X e (U ⊓ V) hW pW) n i

theorem po_res_zero {q : ℕ} {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (A : Z.Opens) (B B' : Y.Opens) (hB : B = B')
    (h : B ≤ φ ⁻¹ᵁ A) (h' : B' ≤ φ ⁻¹ᵁ A) (n i : ℤ) (y : Ht q (sch.obj A.toScheme) n i) :
    pull _ (sch.map (φ.resLE A B h)) _ _ y = 0 → pull _ (sch.map (φ.resLE A B' h')) (tw q i) n y = 0 := by
  subst hB; exact id

theorem restr : Restr := by
  intro q J _ _ D c hc ha hcs hqs hu j0 X e W hWc pW
  have : ∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f) := ha
  set W' : (D.obj j0).Opens := e.hom ⁻¹ᵁ W with hW'def
  have hW' : IsCompact (W' : Set (D.obj j0)) := QuasiCompact.isCompact_preimage (f := e.hom) _ W.2 hWc
  have key := pW q (opensDiagram D j0 W') (opensCone D c j0 W') (isLimitOpensCone D c hc j0 W')
    (fun f => inferInstance)
    (fun j => isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := D.map j.hom) _ W'.2 hW'))
    (fun j => by have := hqs j.left; exact (D.map j.hom ⁻¹ᵁ W').ι.isOpenEmbedding.quasiSeparatedSpace)
    (fun j => by
      have h := (hu j.left).map ((D.map j.hom ⁻¹ᵁ W').ι.appTop.hom)
      simp only [map_natCast] at h
      exact h)
    (Over.mk (𝟙 j0)) ⟨(Scheme.isoOfEq _ (by simp [hW'def])) ≪≫ e.hom.preimageIso W⟩
  intro n i
  refine ⟨fun x => ?_, fun k f y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := (key n i).1 x
    exact ⟨j.left, j.hom, y, hy⟩
  · obtain ⟨k', g, hg⟩ := (key n i).2 (Over.mk f) y hy
    have hw : g.left ≫ f = k'.hom := Over.w g
    refine ⟨k'.left, g.left, ?_⟩
    exact po_res_zero (D.map g.left) _ _ _ (by rw [hw]) _ _ n i y hg

end LateralTheory.E.StepSPf
