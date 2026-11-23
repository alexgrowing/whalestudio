import Development.EtaleCohomology.KummerTheory.ContCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.AffPf
open LateralTheory.KummerTheory.ContCut

theorem lim_of_iso {J : Type} [SmallCategory J] {K : Type 1} [Category.{0} K] {G G' : K ⥤ AddCommGrpCat.{1}}
    (e : G ≅ G') {D : J ⥤ K} (c : Cocone D) (h : Lim G c) : Lim G' c := by
  have nat : ∀ {a b : K} (f : a ⟶ b) (z : G.obj a), (G'.map f).hom ((e.hom.app a).hom z) = (e.hom.app b).hom ((G.map f).hom z) := by
    intro a b f z
    have := congrArg (fun φ => φ.hom z) (e.hom.naturality f)
    simpa using this.symm
  have inv : ∀ (a : K) (z : G'.obj a), (e.hom.app a).hom ((e.inv.app a).hom z) = z := by
    intro a z
    have := congrArg (fun φ => φ.hom z) (e.inv_hom_id_app a)
    simpa using this
  have inv' : ∀ (a : K) (z : G.obj a), (e.inv.app a).hom ((e.hom.app a).hom z) = z := by
    intro a z
    have := congrArg (fun φ => φ.hom z) (e.hom_inv_id_app a)
    simpa using this
  have natc : ∀ (j : J) (z : G.obj (D.obj j)), (G'.map (c.ι.app j)).hom ((e.hom.app (D.obj j)).hom z) =
      (e.hom.app c.pt).hom ((G.map (c.ι.app j)).hom z) := fun j z => nat (c.ι.app j) z
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := h.1 ((e.inv.app c.pt).hom x)
    refine ⟨j, (e.hom.app (D.obj j)).hom y, ?_⟩
    rw [natc, hy, inv]
  · have h0 : (G.map (c.ι.app j)).hom ((e.inv.app (D.obj j)).hom y) = 0 := by
      have h1 := natc j ((e.inv.app (D.obj j)).hom y)
      rw [inv, hy] at h1
      have h2 := congrArg (e.inv.app c.pt).hom h1
      rw [inv', map_zero] at h2
      exact h2.symm
    obtain ⟨k, f, hf⟩ := h.2 j _ h0
    refine ⟨k, f, ?_⟩
    have h1 := nat (D.map f) ((e.inv.app (D.obj j)).hom y)
    rw [inv, hf, map_zero] at h1
    exact h1

theorem Aff_of (hR : AffRing) : Aff := by
  intro hb q X _ R p hq J _ _ D c hc n i
  obtain ⟨T, ⟨e⟩, hmap, hcol⟩ := hR p
  obtain ⟨hT⟩ := hcol c hc
  have unit : ∀ A, IsUnit ((q : ℕ) : T.obj A) := by
    intro A
    obtain ⟨φ⟩ := hmap A
    simpa using hq.map φ.hom
  have key : Lim (T ⋙ Scheme.Spec.rightOp ⋙ Hf (tw q i) n) c := by
    have hB := hb q (D ⋙ T) (T.mapCocone c) hT n i
    refine ⟨fun x => ?_, fun j y hy => ?_⟩
    · obtain ⟨j, y, hy⟩ := hB.1 x (unit c.pt)
      exact ⟨j, y, hy⟩
    · obtain ⟨k, f, hf⟩ := hB.2 j y (unit (D.obj j)) hy
      exact ⟨k, f, hf⟩
  exact lim_of_iso (Functor.isoWhiskerRight e (Hf (tw q i) n)).symm c key

end LateralTheory.KummerTheory.AffPf

end
