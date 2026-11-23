import Development.EtaleCohomology.CohomologicalPurity.LeafFlqPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.ZlocPf

theorem res_comp {R : Type} [CommRing R] {G : Shv R} {T V W : Scheme.{0}} (f : T ⟶ V) (g : V ⟶ W) (a : Sec G W) :
    Sec.res (f ≫ g) a = Sec.res f (Sec.res g a) := by
  show (G.obj.map (f ≫ g).op).hom a = (G.obj.map f.op).hom ((G.obj.map g.op).hom a)
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_zero {R : Type} [CommRing R] {G : Shv R} {V W : Scheme.{0}} (f : V ⟶ W) :
    Sec.res f (0 : Sec G W) = 0 := by
  show (G.obj.map f.op).hom 0 = 0
  exact map_zero _

theorem map_res {R : Type} [CommRing R] {G H : Shv R} (φ : G ⟶ H) {V W : Scheme.{0}} (f : V ⟶ W) (a : Sec G W) :
    Sec.map φ (Sec.res f a) = Sec.res f (Sec.map φ a) := by
  have e := φ.hom.naturality f.op
  show (G.obj.map f.op ≫ φ.hom.app (op V)).hom a = (φ.hom.app (op W) ≫ H.obj.map f.op).hom a
  rw [e]

theorem sep {R : Type} [CommRing R] {G : Shv R} {Y : Scheme.{0}} (s : Sec G Y)
    (H : ∀ y : Y, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y), IsOpenImmersion f ∧ y ∈ Set.range f ∧ Sec.res f s = 0) : s = 0 := by
  let I := {p : Σ Z : Scheme.{0}, Z ⟶ Y // IsOpenImmersion p.2 ∧ Sec.res p.2 s = 0}
  let Zf : I → Scheme.{0} := fun i => i.1.1
  let ff : ∀ i : I, Zf i ⟶ Y := fun i => i.1.2
  have hG : Presheaf.IsSheaf (Scheme.etaleTopology) (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.cond
  have hmem : Sieve.generate (Presieve.ofArrows Zf ff) ∈ Scheme.etaleTopology Y := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff (P := (@Etale : MorphismProperty Scheme.{0}))).2 ⟨fun y => ?_, fun i => ?_⟩
    · obtain ⟨Z, f, hf, hy, hs⟩ := H y
      exact ⟨⟨⟨Z, f⟩, hf, hs⟩, hy⟩
    · haveI := i.2.1
      exact (inferInstance : Etale i.1.2)
  have hS := hG.isSheafFor _ hmem
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hS
  have hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) ff
      (fun _ => (0 : Sec G _)) := by
    intro i j Z gi gj _
    change (G.obj.map gi.op).hom 0 = (G.obj.map gj.op).hom 0
    simp
  obtain ⟨t, -, ht⟩ := hS _ hc
  have e1 := ht s (fun i => i.2.2)
  have e2 := ht 0 (fun i => res_zero (G := G) i.1.2)
  rw [e1, e2]

theorem vanish {R : Type} [CommRing R] {G : Shv R} {Y Z T : Scheme.{0}} (f : Z ⟶ Y) [IsOpenImmersion f] (g : T ⟶ Y)
    (hr : Set.range g ⊆ Set.range f) (s : Sec G Y) (h0 : Sec.res f s = 0) : Sec.res g s = 0 := by
  rw [← IsOpenImmersion.lift_fac f g hr, res_comp, h0, res_zero]

theorem pt {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (q : V.toScheme) : W.ι (X.homOfLE h q) = V.ι q := by
  rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]

theorem memι {X : Scheme.{0}} (V : X.Opens) (q : V.toScheme) : V.ι q ∈ V := by
  show V.ι q ∈ (V : Set X)
  rw [← Scheme.Opens.range_ι V]; exact ⟨q, rfl⟩

theorem lift_pt {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (y : W.toScheme) (hy : W.ι y ∈ V) :
    y ∈ Set.range (X.homOfLE h) := by
  change W.ι y ∈ (V : Set X) at hy
  rw [← Scheme.Opens.range_ι V] at hy
  obtain ⟨q, hq⟩ := hy
  refine ⟨q, W.ι.isOpenEmbedding.injective ?_⟩
  rw [pt, hq]

theorem rangeU {X : Scheme.{0}} (U : X.Opens) {V W : X.Opens} (h : V ≤ W) :
    Set.range ((V.ι ⁻¹ᵁ U).ι ≫ X.homOfLE h) ⊆ Set.range (W.ι ⁻¹ᵁ U).ι := by
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  show W.ι (((V.ι ⁻¹ᵁ U).ι ≫ X.homOfLE h) p) ∈ U
  rw [Scheme.Hom.comp_apply, pt]
  exact memι (V.ι ⁻¹ᵁ U) p

open LateralTheory.CohomologicalPurity.Cl in
theorem LeafZloc_of : LateralTheory.CohomologicalPurity.Cl.Flq.LeafZloc := by
  intro R _ K X U n
  refine ⟨?_, ?_⟩
  · intro V W h a ha
    obtain ⟨ha1, ha2⟩ := (mem_Zc a).1 ha
    refine (mem_Zc _).2 ⟨?_, ?_⟩
    · rw [← res_comp]; exact vanish _ _ (rangeU U h) a ha1
    · rw [map_res, ha2, res_zero]
  · intro W a H
    refine (mem_Zc _).2 ⟨?_, ?_⟩
    · apply sep; intro y
      obtain ⟨V, h, hxV, hb⟩ := H (W.ι ((W.ι ⁻¹ᵁ U).ι y)) (memι W _)
      obtain ⟨hb1, -⟩ := (mem_Zc _).1 hb
      let O : (W.ι ⁻¹ᵁ U).toScheme.Opens := ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) ⁻¹ᵁ V
      refine ⟨O.toScheme, O.ι, inferInstance, ?_, ?_⟩
      · rw [Scheme.Opens.range_ι]
        show ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) y ∈ V
        rw [Scheme.Hom.comp_apply]; exact hxV
      · rw [← res_comp]
        apply vanish ((V.ι ⁻¹ᵁ U).ι ≫ X.homOfLE h) _ ?_ a (by rw [res_comp]; exact hb1)
        rintro _ ⟨z, rfl⟩
        have hz : ((W.ι ⁻¹ᵁ U).ι ≫ W.ι) (O.ι z) ∈ V := memι O z
        rw [Scheme.Hom.comp_apply] at hz
        have hwU : W.ι ((W.ι ⁻¹ᵁ U).ι (O.ι z)) ∈ U := memι (W.ι ⁻¹ᵁ U) (O.ι z)
        obtain ⟨q, hq⟩ := lift_pt h _ hz
        have hqU : q ∈ (V.ι ⁻¹ᵁ U : Set V.toScheme) := by
          show V.ι q ∈ U
          rw [← pt h, hq]; exact hwU
        rw [← Scheme.Opens.range_ι] at hqU
        obtain ⟨p, hp⟩ := hqU
        exact ⟨p, by rw [Scheme.Hom.comp_apply, hp, hq, Scheme.Hom.comp_apply]⟩
    · apply sep; intro y
      obtain ⟨V, h, hxV, hb⟩ := H (W.ι y) (memι W y)
      obtain ⟨-, hb2⟩ := (mem_Zc _).1 hb
      refine ⟨V.toScheme, X.homOfLE h, inferInstance, lift_pt h y hxV, ?_⟩
      rw [← map_res]; exact hb2

end LateralTheory.CohomologicalPurity.ZlocPf
