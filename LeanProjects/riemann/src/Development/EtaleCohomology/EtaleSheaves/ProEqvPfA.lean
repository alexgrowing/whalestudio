import Development.EtaleCohomology.EtaleSheaves.ProEqvPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.ProEqvPf

theorem LateralTheory.E.ProEqvPf.stageA (hC : Cont) (H : Hyp) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A))
    {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (y : Y) {J : Type}
    [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y)
    (hc : ClopenSys y D c ι) (hp : ∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) (n : ℤ)
    (x : Ht q (sch.obj Y) n i) (hx : pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0) :
    ∃ j, pull _ (sch.map (ι j)) _ _ x = 0 := by
  obtain ⟨⟨hl⟩, hι, hD⟩ := hc
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := J)
  have e1 : pull _ (sch.map (pullback.fst ((c.π.app j0 ≫ ι j0) ≫ g) (cpt A))) (tw q i) n
      (pull _ (sch.map (c.π.app j0 ≫ ι j0)) (tw q i) n x) = pull _ (sch.map (pullback.fst ((c.π.app j0 ≫ ι j0) ≫ g) (cpt A))) (tw q i) n 0 := by
    rw [map_zero, ← pull_comp, ← Functor.map_comp]
    have : pullback.fst ((c.π.app j0 ≫ ι j0) ≫ g) (cpt A) ≫ c.π.app j0 ≫ ι j0 =
        fm (c.π.app j0 ≫ ι j0) g ≫ pullback.fst g (cpt A) := by
      unfold fm pullback.map; rw [pullback.lift_fst]
    rw [this, Functor.map_comp, pull_comp, hx, map_zero]
  have e2 := (hp j0 n).1 e1
  rw [Functor.map_comp, pull_comp] at e2
  have hcs : ∀ j, CompactSpace (D.obj j) := fun j => by
    have := (hι j).2.1; exact QuasiCompact.compactSpace_of_compactSpace (ι j)
  have hqs : ∀ j, QuasiSeparatedSpace (D.obj j) := fun j => by
    have := (hι j).1; exact quasiSeparatedSpace_of_quasiSeparated (ι j)
  obtain ⟨k, f, hk⟩ := (hC H q D c hl (fun f => (hD f).2) hcs hqs (fun j => unit_of hq (ι j ≫ g)) n i).2 j0 _ e2
  refine ⟨k, ?_⟩
  rw [← (hD f).1, Functor.map_comp, pull_comp]
  exact hk

namespace LateralTheory.E.ProEqvPf

def StageB : Prop := Cont → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (y : Y) {J : Type}
  [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
  ClopenSys y D c ι → (∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) → ∀ n : ℤ,
  ∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∃ j, Hit q i n g z (ι j)

theorem stage_of (hB : StageB) : PiLocalization₂ := by
  intro hC H q i A _ _ hq Y _ _ g y J _ _ D c ι hc hp n
  exact ⟨fun x hx => stageA hC H q i A hq g y D c ι hc hp n x hx, hB hC H q i A hq g y D c ι hc hp n⟩

theorem etale_pro_equivalence_of_continuity_mayer_vietoris_lifting_stage_glue (hC : Cont) (hM : MV) (hB : StageB) (hG : Glue) : ProEqv :=
  ProEqv_of hC hM (stage_of hB) hG

end LateralTheory.E.ProEqvPf
