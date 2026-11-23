import Development.EtaleCohomology.EtaleSheaves.LeafGeomPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf

namespace LateralTheory.E.LeafGeomPfLoc

theorem projective_bundle_direct_sum_zero_vertex_coordinates_restrict {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X Y : Scheme.{0}}
    (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) (j : Fin (a + b)) :
    vec0 V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) j = Scheme.Γ.map k.op (vec0 V W x j) := by
  have h := ConcreteCategory.congr_hom (((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).naturality k.op) x
  unfold vec0
  erw [h]
  rfl

theorem unit_le {X : Scheme.{0}} (f : Γ(X, ⊤)) {V : X.Opens} (h : V ≤ X.basicOpen f) :
    IsUnit ((X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom f) := by
  have hu := X.toRingedSpace.isUnit_res_basicOpen (U := ⊤) f
  have := hu.map (X.presheaf.map (homOfLE h).op).hom
  erw [← CommRingCat.comp_apply, ← Functor.map_comp] at this
  exact this

theorem unit_basicOpen {X : Scheme.{0}} (f : Scheme.Γ.obj (op X)) :
    IsUnit (Scheme.Γ.map (X.basicOpen f).ι.op f) := by
  rw [Scheme.Γ_map_op, Scheme.Opens.ι_appTop]
  exact unit_le f (X.basicOpen f).ι_image_top.le

theorem leafLocal : LeafLocal := by
  intro E a b V W n X x
  have hspan : Ideal.span (Set.range (vec0 V W x)) = ⊤ :=
    ((show Fin (n + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X)) from
      ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) x).obj 0).2
  have hcov : TopologicalSpace.IsOpenCover (fun j => X.basicOpen (vec0 V W x j)) := by
    have := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top (X := X) ⊤ (Set.range (vec0 V W x)) hspan
    refine le_antisymm le_top ?_
    rw [← this]
    exact iSup₂_le fun _ ⟨j, hj⟩ => hj ▸ le_iSup (fun j => X.basicOpen (vec0 V W x j)) j
  let 𝒰 := X.openCoverOfIsOpenCover _ hcov
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.zariskiTopology_le_etaleTopology _ 𝒰.mem_grothendieckTopology, ?_⟩
  intro Y k hk
  rw [Sieve.mem_ofArrows_iff] at hk
  obtain ⟨j, g, rfl⟩ := hk
  have hu : IsUnit (Scheme.Γ.map (g ≫ 𝒰.f j).op (vec0 V W x j)) := by
    rw [op_comp, Functor.map_comp]
    exact (unit_basicOpen (vec0 V W x j)).map (Scheme.Γ.map g.op).hom
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ : (∃ i, j = Fin.castAdd b i) ∨ ∃ i, j = Fin.natAdd a i :=
    Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun i => Or.inr ⟨i, rfl⟩) j
  · left
    simp only [First, projective_bundle_direct_sum_zero_vertex_coordinates_restrict]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hu
  · right
    simp only [Second, projective_bundle_direct_sum_zero_vertex_coordinates_restrict]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hu

theorem LeafGeom_of (h1 : LeafHalf1) (h2 : LeafHalf2) : LateralTheory.E.D2.LeafGeom :=
  LateralTheory.E.LeafGeomPf.LeafGeom_of h1 h2 leafLocal

end LateralTheory.E.LeafGeomPfLoc
