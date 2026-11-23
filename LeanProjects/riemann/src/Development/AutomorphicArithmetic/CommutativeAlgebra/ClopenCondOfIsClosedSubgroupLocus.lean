import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem clopen_forall {S : Scheme.{0}} (X F : Over S) [IsFinite F.hom] [Etale F.hom]
    (W : (X ⊗ F).left.Opens) (hW : IsClosed (W : Set (X ⊗ F).left)) :
    GlobalTheory.LevCover.ClopenCond X (fun T h => ∀ (T' : Over S) (t : T' ⟶ T) (a : T' ⟶ F),
      Set.range (lift (t ≫ h) a).left ⊆ W) := by
  have hWo : IsOpen ((W : Set (X ⊗ F).left)ᶜ) := hW.isOpen_compl
  have hWc : IsClosed ((W : Set (X ⊗ F).left)ᶜ) := W.isOpen.isClosed_compl
  have hKc : IsClosed (pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ) :=
    (pullback.fst X.hom F.hom).isClosedMap _ hWc
  have hKo : IsOpen (pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ) :=
    (pullback.fst X.hom F.hom).isOpenMap _ hWo
  refine ⟨⟨(pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ)ᶜ, hKc.isOpen_compl⟩,
    hKo.isClosed_compl, ?_⟩
  intro T h
  constructor
  · intro H
    rintro _ ⟨x, rfl⟩ ⟨z, hz, hzx⟩
    obtain ⟨q, hq1, hq2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := h.left) (g := pullback.fst X.hom F.hom) x z hzx.symm
    let T' : Over S := Over.mk (pullback.fst h.left (pullback.fst X.hom F.hom) ≫ T.hom)
    let t : T' ⟶ T := Over.homMk (pullback.fst h.left (pullback.fst X.hom F.hom)) rfl
    have ha : (pullback.snd h.left (pullback.fst X.hom F.hom) ≫ pullback.snd X.hom F.hom) ≫ F.hom
        = T'.hom := by
      simp only [T', Over.mk_hom, Category.assoc]
      rw [← pullback.condition (f := X.hom) (g := F.hom), ← Category.assoc,
        ← pullback.condition (f := h.left) (g := pullback.fst X.hom F.hom), Category.assoc, Over.w h]
    let a : T' ⟶ F :=
      Over.homMk (pullback.snd h.left (pullback.fst X.hom F.hom) ≫ pullback.snd X.hom F.hom) ha
    have hl : (lift (t ≫ h) a).left = pullback.snd h.left (pullback.fst X.hom F.hom) := by
      apply pullback.hom_ext
      · change (lift (t ≫ h) a ≫ fst X F).left = _
        rw [lift_fst]
        exact pullback.condition
      · change (lift (t ≫ h) a ≫ snd X F).left = _
        rw [lift_snd]
        rfl
    apply hz
    have hmem := H T' t a ⟨q, rfl⟩
    rw [hl, hq2] at hmem
    exact hmem
  · intro H T' t a
    rintro _ ⟨y, rfl⟩
    by_contra hy
    have e : (lift (t ≫ h) a).left ≫ pullback.fst X.hom F.hom = t.left ≫ h.left := by
      change (lift (t ≫ h) a ≫ fst X F).left = _
      rw [lift_fst]
      rfl
    apply H ⟨t.left y, rfl⟩
    refine ⟨(lift (t ≫ h) a).left y, hy, ?_⟩
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]

private theorem clopen_pre {S : Scheme.{0}} {X Y : Over S} (e : X ⟶ Y) (U : Y.left.Opens)
    (hU : IsClosed (U : Set Y.left)) :
    GlobalTheory.LevCover.ClopenCond X (fun T h => Set.range (h ≫ e).left ⊆ U) := by
  refine ⟨e.left ⁻¹ᵁ U, hU.preimage e.left.continuous, ?_⟩
  intro T h
  simp only [Over.comp_left, Set.range_subset_iff, Scheme.Hom.comp_apply, Scheme.Hom.mem_preimage, SetLike.mem_coe]

theorem UpperTheory.clopenCond_of_isClosed_subgroupLocus :
    ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [IsFinite G.hom] [Etale G.hom] (U : (X ⊗ G).left.Opens), IsClosed (U : Set (X ⊗ G).left) → GlobalTheory.LevCover.ClopenCond X (fun T h => ∀ (T' : Over S) (t : T' ⟶ T), Set.range (lift (t ≫ h) (1 : T' ⟶ G)).left ⊆ U ∧ ∀ a b : T' ⟶ G, Set.range (lift (t ≫ h) a).left ⊆ U → Set.range (lift (t ≫ h) b).left ⊆ U → Set.range (lift (t ≫ h) (a * b⁻¹)).left ⊆ U) := by
  intro S G X _ _ _ U hU
  haveI := (GlobalTheory.LevCover.finiteEtale_tensor G G).1
  haveI := (GlobalTheory.LevCover.finiteEtale_tensor G G).2
  have hUo : IsOpen (U : Set (X ⊗ G).left) := U.isOpen
  let m1 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ fst G G)
  let m2 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ snd G G)
  let m3 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ (fst G G * (snd G G)⁻¹))
  let Ws : Set (X ⊗ (G ⊗ G)).left :=
    (m1.left ⁻¹' U ∩ m2.left ⁻¹' U)ᶜ ∪ m3.left ⁻¹' U
  have hWo : IsOpen Ws :=
    ((hU.preimage m1.left.continuous).inter (hU.preimage m2.left.continuous)).isOpen_compl.union
      (hUo.preimage m3.left.continuous)
  have hWc : IsClosed Ws :=
    ((hUo.preimage m1.left.continuous).inter (hUo.preimage m2.left.continuous)).isClosed_compl.union
      (hU.preimage m3.left.continuous)
  have h1 := clopen_pre (lift (𝟙 X) (1 : X ⟶ G)) U hU
  have h2 := clopen_forall X (G ⊗ G) ⟨Ws, hWo⟩ hWc
  refine (h1.and h2).congr ?_
  intro T h
  have k0 : ∀ (T' : Over S) (t : T' ⟶ T),
      lift (t ≫ h) (1 : T' ⟶ G) = t ≫ h ≫ lift (𝟙 X) (1 : X ⟶ G) := by
    intro T' t
    simp [comp_lift]
  have k1 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m1 = lift u (c ≫ fst G G) := by
    intro T' u c
    simp [m1, comp_lift]
  have k2 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m2 = lift u (c ≫ snd G G) := by
    intro T' u c
    simp [m2, comp_lift]
  have k3 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m3 = lift u ((c ≫ fst G G) * (c ≫ snd G G)⁻¹) := by
    intro T' u c
    simp [m3, comp_lift, MonObj.comp_mul, GrpObj.comp_inv]
  have pt : ∀ {A B C : Over S} (f : A ⟶ B) (g : B ⟶ C) (y : A.left),
      (f ≫ g).left y = g.left (f.left y) := by
    intro A B C f g y
    rw [Over.comp_left, Scheme.Hom.comp_apply]
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · have := (H T (𝟙 T)).1
      rw [k0, Category.id_comp] at this
      exact this
    · intro T' t c
      rintro _ ⟨y, rfl⟩
      change (lift (t ≫ h) c).left y ∈ Ws
      by_cases hy : (lift (t ≫ h) c).left y ∈ m1.left ⁻¹' U ∩ m2.left ⁻¹' U
      · right
        let V : T'.left.Opens :=
          (lift (t ≫ h) c ≫ m1).left ⁻¹ᵁ U ⊓ (lift (t ≫ h) c ≫ m2).left ⁻¹ᵁ U
        have hyV : y ∈ V := by
          refine ⟨?_, ?_⟩
          · change (lift (t ≫ h) c ≫ m1).left y ∈ (U : Set _)
            rw [pt]
            exact hy.1
          · change (lift (t ≫ h) c ≫ m2).left y ∈ (U : Set _)
            rw [pt]
            exact hy.2
        have hVw : ∀ w, V.ι w ∈ V := by
          intro w
          have hw : V.ι w ∈ Set.range V.ι := ⟨w, rfl⟩
          rwa [Scheme.Opens.range_ι] at hw
        let T'' : Over S := Over.mk (V.ι ≫ T'.hom)
        let j : T'' ⟶ T' := Over.homMk V.ι rfl
        have eq1 : lift ((j ≫ t) ≫ h) (j ≫ c ≫ fst G G) = j ≫ (lift (t ≫ h) c ≫ m1) := by
          rw [k1, comp_lift, Category.assoc]
        have eq2 : lift ((j ≫ t) ≫ h) (j ≫ c ≫ snd G G) = j ≫ (lift (t ≫ h) c ≫ m2) := by
          rw [k2, comp_lift, Category.assoc]
        have eq3 : lift ((j ≫ t) ≫ h) ((j ≫ c ≫ fst G G) * (j ≫ c ≫ snd G G)⁻¹)
            = j ≫ (lift (t ≫ h) c ≫ m3) := by
          rw [k3, comp_lift, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
        have hA := (H T'' (j ≫ t)).2 (j ≫ c ≫ fst G G) (j ≫ c ≫ snd G G)
          (by
            rw [eq1]
            rintro _ ⟨w, rfl⟩
            rw [pt]
            exact (hVw w).1)
          (by
            rw [eq2]
            rintro _ ⟨w, rfl⟩
            rw [pt]
            exact (hVw w).2)
        obtain ⟨y', hy'⟩ : y ∈ Set.range V.ι := by
          rw [Scheme.Opens.range_ι]
          exact hyV
        have := hA ⟨y', rfl⟩
        rw [eq3, pt] at this
        change m3.left ((lift (t ≫ h) c).left y) ∈ (U : Set _)
        rw [← pt, ← hy']
        exact this
      · left
        exact hy
  · rintro ⟨H1, H2⟩ T' t
    refine ⟨?_, ?_⟩
    · rw [k0]
      rintro _ ⟨y, rfl⟩
      rw [pt]
      exact H1 ⟨t.left y, rfl⟩
    · intro a b ha hb
      rintro _ ⟨y, rfl⟩
      have hz : (lift (t ≫ h) (lift a b)).left y ∈ Ws := H2 T' t (lift a b) ⟨y, rfl⟩
      have e3 := k3 T' (t ≫ h) (lift a b)
      rw [lift_fst, lift_snd] at e3
      rw [← e3, pt]
      rcases hz with hz | hz
      · exfalso
        apply hz
        refine ⟨?_, ?_⟩
        · change (m1.left ((lift (t ≫ h) (lift a b)).left y)) ∈ (U : Set _)
          rw [← pt, k1, lift_fst]
          exact ha ⟨y, rfl⟩
        · change (m2.left ((lift (t ≫ h) (lift a b)).left y)) ∈ (U : Set _)
          rw [← pt, k2, lift_snd]
          exact hb ⟨y, rfl⟩
      · exact hz
