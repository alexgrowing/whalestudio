import Development.EtaleCohomology.EtaleSheaves.LeafGlueIsProperPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

set_option backward.isDefEq.respectTransparency false in
theorem sep_of_cover {X S : Scheme.{0}} (f : X ⟶ S) (U : X.OpenCover)
    (H : ∀ i j, IsClosedImmersion (pullback.map (U.f i) (U.f j) (U.f i ≫ f) (U.f j ≫ f) (𝟙 _) (𝟙 _) f
      (by simp) (by simp))) : IsSeparated f := by
  constructor
  apply IsZariskiLocalAtTarget.of_openCover (Scheme.Pullback.openCoverOfLeftRight U U f f)
  rintro ⟨i, j⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (pullbackDiagonalMapIdIso (U.f i) (U.f j) f).inv]
  have e : (pullbackDiagonalMapIdIso (U.f i) (U.f j) f).inv ≫
      (Scheme.Pullback.openCoverOfLeftRight U U f f).pullbackHom (pullback.diagonal f) (i, j) =
      pullback.map (U.f i) (U.f j) (U.f i ≫ f) (U.f j ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp only [Scheme.Cover.pullbackHom, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, pullback.lift_fst, pullback.lift_snd, Category.comp_id]
    · exact pullbackDiagonalMapIdIso_inv_snd_fst (U.f i) (U.f j) f
    · exact pullbackDiagonalMapIdIso_inv_snd_snd (U.f i) (U.f j) f
  rw [e]; exact H i j

theorem closed_of_pb {X S W P Q : Scheme.{0}} (f : X ⟶ S) (ia : P ⟶ X) (ib : Q ⟶ X) (pa : W ⟶ P)
    (pb : W ⟶ Q) (hp : IsPullback pa pb ia ib) (ga : P ⟶ S) (gb : Q ⟶ S) (hga : ia ≫ f = ga)
    (hgb : ib ≫ f = gb) (w : pa ≫ ga = pb ≫ gb)
    (hc : IsClosedImmersion (pullback.lift pa pb w)) :
    IsClosedImmersion (pullback.map ia ib (ia ≫ f) (ib ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp)) := by
  subst hga hgb
  have e : pullback.map ia ib (ia ≫ f) (ib ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp) =
      hp.isoPullback.inv ≫ pullback.lift pa pb w := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.comp_id, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_inv_fst]
    · rw [pullback.lift_snd, Category.comp_id, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_inv_snd]
  rw [e]; infer_instance

def LeafGluePullback : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsPullback (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_A A u)).toRingHom))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)).toRingHom))
    G.iA G.iB

theorem spec_w {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L) (hA : A ≤ D) (hB : B ≤ D) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hA).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Ω A)) =
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hB).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]; congr 1

def LeafSpecGenClosed : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
  (hA : A ≤ D) (hB : B ≤ D), D ≤ Algebra.adjoin Ω ((A : Set L) ∪ B) →
  IsClosedImmersion (pullback.lift _ _ (spec_w A B D hA hB))

theorem dr_le {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L) (hu : u⁻¹ ∈ B) :
    Dr Ω A u ≤ Algebra.adjoin Ω ((A : Set L) ∪ B) :=
  Algebra.adjoin_mono (Set.union_subset_union_right _ (Set.singleton_subset_iff.mpr hu))

theorem LeafGlueSep_of (hP : LeafGluePullback) (hC : LeafSpecGenClosed) :
    LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  have hD := dr_le A B u h.2.2.1
  apply sep_of_cover G.c0 (LateralTheory.E.LeafGlueIsProperPf.cov G)
  intro i j
  cases i <;> cases j
  · exact closed_of_pb G.c0 G.iB G.iB (𝟙 _) (𝟙 _) (IsKernelPair.id_of_mono G.iB) _ _ G.hcB G.hcB (by simp)
      (by exact (inferInstance : IsClosedImmersion (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap Ω B))))))
  · exact closed_of_pb G.c0 G.iB G.iA _ _ (hP Ω L A B u h G).flip _ _ G.hcB G.hcA _
      (hC Ω L B A _ _ _ (by rw [Set.union_comm]; exact hD))
  · exact closed_of_pb G.c0 G.iA G.iB _ _ (hP Ω L A B u h G) _ _ G.hcA G.hcB _ (hC Ω L A B _ _ _ hD)
  · exact closed_of_pb G.c0 G.iA G.iA (𝟙 _) (𝟙 _) (IsKernelPair.id_of_mono G.iA) _ _ G.hcA G.hcA (by simp)
      (by exact (inferInstance : IsClosedImmersion (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap Ω A))))))

end LateralTheory.E.GluedCurveChartOverlaps
