import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LineBundleTrivialBasicOpenOfTrivialFibreProductStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProjByBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BijectiveAppTopBaseChange

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
noncomputable section
namespace GlobalTheory.CubeLocal

theorem trivAt_id_iff {X W : Scheme.{0}} (M : LB X) (r : W ⟶ X) :
    TrivAt M (fun _ : PUnit => 𝟙 X) (fun _ => 1) r ↔ Triv (M.pull r) := by
  unfold TrivAt
  simp only [Category.comp_id]

variable {S : Scheme.{0}} (X Y Z : Over S)

theorem exists_pair_chart {T : Scheme.{0}} (t : T ⟶ S) :
    ∃ m : ((Over.pullback t).obj X ⊗ (Over.pullback t).obj Y).left ⟶ (X ⊗ Y).left,
      IsPullback m ((Over.pullback t).obj X ⊗ (Over.pullback t).obj Y).hom (X ⊗ Y).hom t := by
  set B := (Over.pullback t).obj X
  set C := (Over.pullback t).obj Y
  have hB : IsPullback (pullback.fst X.hom t) B.hom X.hom t := IsPullback.of_hasPullback _ _
  have hC : IsPullback (pullback.fst Y.hom t) C.hom Y.hom t := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := IsPullback.of_hasPullback _ _
  have hBC : IsPullback (fst B C).left (snd B C).left B.hom C.hom := IsPullback.of_hasPullback _ _
  have ho : IsPullback ((fst B C).left ≫ pullback.fst X.hom t) (snd B C).left X.hom
      (pullback.fst Y.hom t ≫ Y.hom) := by
    rw [hC.w]; exact hBC.paste_horiz hB
  obtain ⟨m, m₁, m₂⟩ : ∃ m : (B ⊗ C).left ⟶ (X ⊗ Y).left,
      m ≫ (fst X Y).left = (fst B C).left ≫ pullback.fst X.hom t ∧
      m ≫ (snd X Y).left = (snd B C).left ≫ pullback.fst Y.hom t :=
    ⟨h2.lift _ _ (by rw [ho.w, Category.assoc]), h2.lift_fst _ _ _, h2.lift_snd _ _ _⟩
  have hm : IsPullback m (snd B C).left (snd X Y).left (pullback.fst Y.hom t) :=
    IsPullback.of_right (by rw [m₁]; exact ho) m₂ h2
  refine ⟨m, ?_⟩
  rw [← Over.w (snd B C), ← Over.w (snd X Y)]
  exact hm.paste_vert hC

theorem exists_triple_chart {T : Scheme.{0}} (j : T ⟶ Z.left) :
    ∃ q : ((Over.pullback (j ≫ Z.hom)).obj X ⊗ (Over.pullback (j ≫ Z.hom)).obj Y).left ⟶ (X ⊗ Y ⊗ Z).left,
      IsPullback q ((Over.pullback (j ≫ Z.hom)).obj X ⊗ (Over.pullback (j ≫ Z.hom)).obj Y).hom
        (snd X (Y ⊗ Z) ≫ snd Y Z).left j ∧
      q ≫ (fst X (Y ⊗ Z)).left =
        (fst _ _ : _ ⟶ (Over.pullback (j ≫ Z.hom)).obj X).left ≫ pullback.fst X.hom (j ≫ Z.hom) ∧
      q ≫ (snd X (Y ⊗ Z) ≫ fst Y Z).left =
        (snd _ _ : _ ⟶ (Over.pullback (j ≫ Z.hom)).obj Y).left ≫ pullback.fst Y.hom (j ≫ Z.hom) := by
  set B := (Over.pullback (j ≫ Z.hom)).obj X
  set C := (Over.pullback (j ≫ Z.hom)).obj Y
  have hB : IsPullback (pullback.fst X.hom (j ≫ Z.hom)) B.hom X.hom (j ≫ Z.hom) := IsPullback.of_hasPullback _ _
  have hC : IsPullback (pullback.fst Y.hom (j ≫ Z.hom)) C.hom Y.hom (j ≫ Z.hom) := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst Y Z).left (snd Y Z).left Y.hom Z.hom := IsPullback.of_hasPullback _ _
  have h3 : IsPullback (fst X (Y ⊗ Z)).left (snd X (Y ⊗ Z)).left X.hom (Y ⊗ Z).hom := IsPullback.of_hasPullback _ _
  have hBB : IsPullback (fst B C).left (snd B C).left B.hom C.hom := IsPullback.of_hasPullback _ _
  obtain ⟨m, m₁, m₂⟩ : ∃ m : C.left ⟶ (Y ⊗ Z).left, m ≫ (fst Y Z).left = pullback.fst Y.hom (j ≫ Z.hom) ∧
      m ≫ (snd Y Z).left = C.hom ≫ j :=
    ⟨h2.lift _ _ (by rw [hC.w, Category.assoc]), h2.lift_fst _ _ _, h2.lift_snd _ _ _⟩
  have hm : IsPullback m C.hom (snd Y Z).left j := IsPullback.of_right (by rw [m₁]; exact hC) m₂ h2
  have mw : m ≫ (Y ⊗ Z).hom = C.hom ≫ j ≫ Z.hom := by
    rw [← Over.w (snd Y Z), ← Category.assoc, m₂, Category.assoc]
  have ho : IsPullback ((fst B C).left ≫ pullback.fst X.hom (j ≫ Z.hom)) (snd B C).left X.hom
      (m ≫ (Y ⊗ Z).hom) := by
    rw [mw]; exact hBB.paste_horiz hB
  obtain ⟨q, q₁, q₂⟩ : ∃ q : (B ⊗ C).left ⟶ (X ⊗ Y ⊗ Z).left,
      q ≫ (fst X (Y ⊗ Z)).left = (fst B C).left ≫ pullback.fst X.hom (j ≫ Z.hom) ∧
      q ≫ (snd X (Y ⊗ Z)).left = (snd B C).left ≫ m :=
    ⟨h3.lift _ _ (by rw [ho.w, Category.assoc]), h3.lift_fst _ _ _, h3.lift_snd _ _ _⟩
  have hq : IsPullback q (snd B C).left (snd X (Y ⊗ Z)).left m := IsPullback.of_right (by rw [q₁]; exact ho) q₂ h3
  refine ⟨q, ?_, q₁, ?_⟩
  · rw [← Over.w (snd B C)]
    exact hq.paste_vert hm
  · show q ≫ (snd X (Y ⊗ Z)).left ≫ (fst Y Z).left = _
    rw [← Category.assoc, q₂, Category.assoc, m₁]

variable {X Y Z}

theorem coord_eq {P A : Over S} {W : Scheme.{0}} (r : W ⟶ P.left) (c : P ⟶ A) (a : 𝟙_ (Over S) ⟶ A)
    (b : W ⟶ S) (h : r ≫ c.left = b ≫ a.left) :
    (Over.homMk r rfl : Over.mk (r ≫ P.hom) ⟶ P) ≫ c = toUnit _ ≫ a := by
  have hb : b = r ≫ P.hom := by
    have := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at this
    exact (this.trans (Category.comp_id _)).symm
  apply Over.OverMorphism.ext
  exact h.trans (by rw [hb]; rfl)

theorem trivAt_of_factor {P F T : Over S} {M : LB P.left} {i : F ⟶ P} (H : Triv (M.pull i.left))
    (x : T ⟶ P) (h : T ⟶ F) (e : h ≫ i = x) :
    TrivAt M (fun _ : PUnit => 𝟙 P.left) (fun _ => 1) x.left := by
  subst e
  exact ((trivAt_id_iff M i.left).2 H).comp h.left

theorem trivAt_face₁ {x₀ : 𝟙_ (Over S) ⟶ X} {M : LB (X ⊗ Y ⊗ Z).left}
    (H : Triv (M.pull (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))).left)) {W : Scheme.{0}}
    (r : W ⟶ (X ⊗ Y ⊗ Z).left) (b : W ⟶ S) (h : r ≫ (fst X (Y ⊗ Z)).left = b ≫ x₀.left) :
    TrivAt M (fun _ : PUnit => 𝟙 _) (fun _ => 1) r := by
  let x : Over.mk (r ≫ (X ⊗ Y ⊗ Z).hom) ⟶ X ⊗ Y ⊗ Z := Over.homMk r rfl
  have e : x ≫ _ = _ := coord_eq r _ x₀ b h
  refine trivAt_of_factor H x (x ≫ snd _ _) ?_
  clear_value x
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · simp [e]
  · simp

theorem trivAt_face₂ {y₀ : 𝟙_ (Over S) ⟶ Y} {M : LB (X ⊗ Y ⊗ Z).left}
    (H : Triv (M.pull (lift (fst X Z) (lift (toUnit (X ⊗ Z) ≫ y₀) (snd X Z))).left)) {W : Scheme.{0}}
    (r : W ⟶ (X ⊗ Y ⊗ Z).left) (b : W ⟶ S) (h : r ≫ (snd X (Y ⊗ Z) ≫ fst Y Z).left = b ≫ y₀.left) :
    TrivAt M (fun _ : PUnit => 𝟙 _) (fun _ => 1) r := by
  let x : Over.mk (r ≫ (X ⊗ Y ⊗ Z).hom) ⟶ X ⊗ Y ⊗ Z := Over.homMk r rfl
  have e : x ≫ _ = _ := coord_eq r _ y₀ b h
  refine trivAt_of_factor H x (lift (x ≫ fst _ _) (x ≫ snd _ _ ≫ snd _ _)) ?_
  clear_value x
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
  · simp
  · simp [e]
  · simp

theorem trivAt_face₃ {z₀ : 𝟙_ (Over S) ⟶ Z} {M : LB (X ⊗ Y ⊗ Z).left}
    (H : Triv (M.pull (lift (fst X Y) (lift (snd X Y) (toUnit (X ⊗ Y) ≫ z₀))).left)) {W : Scheme.{0}}
    (r : W ⟶ (X ⊗ Y ⊗ Z).left) (b : W ⟶ S) (h : r ≫ (snd X (Y ⊗ Z) ≫ snd Y Z).left = b ≫ z₀.left) :
    TrivAt M (fun _ : PUnit => 𝟙 _) (fun _ => 1) r := by
  let x : Over.mk (r ≫ (X ⊗ Y ⊗ Z).hom) ⟶ X ⊗ Y ⊗ Z := Over.homMk r rfl
  have e : x ≫ _ = _ := coord_eq r _ z₀ b h
  refine trivAt_of_factor H x (lift (x ≫ fst _ _) (x ≫ snd _ _ ≫ fst _ _)) ?_
  clear_value x
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
  · simp
  · simp
  · simp [e]

theorem geometricallyConnected_of_integral {A B : Scheme.{0}} (f : A ⟶ B) [GeometricallyIntegral f] :
    GeometricallyConnected f :=
  ⟨fun _ _ y W a b h => by
    have : IsIntegral W := GeometricallyIntegral.geometrically_isIntegral y a b h
    infer_instance⟩

theorem exists_section_baseChange {T : Scheme.{0}} (t : T ⟶ S) {A : Over S} (a : 𝟙_ (Over S) ⟶ A) :
    ∃ a' : 𝟙_ (Over T) ⟶ (Over.pullback t).obj A, ∀ W : Over T,
      (toUnit W ≫ a').left ≫ pullback.fst A.hom t = (W.hom ≫ t) ≫ a.left := by
  have w : (t ≫ a.left) ≫ A.hom = 𝟙 T ≫ t := by
    rw [Category.assoc, Over.w]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  refine ⟨Over.homMk (pullback.lift (t ≫ a.left) (𝟙 T) w) (pullback.lift_snd _ _ _), fun W => ?_⟩
  change (W.hom ≫ pullback.lift (t ≫ a.left) (𝟙 T) w) ≫ _ = _
  rw [Category.assoc, pullback.lift_fst, Category.assoc]

theorem bijective_appTop_baseChange {k : Type} [Field k] (A : Over (Sp k)) (a : 𝟙_ (Over (Sp k)) ⟶ A)
    (hp : IsProper A.hom) (hi : GeometricallyIntegral A.hom) {R : Type} [CommRing R]
    {t : Spec (CommRingCat.of R) ⟶ Sp k} {W : Scheme.{0}} {m : W ⟶ A.left} {f : W ⟶ Spec (CommRingCat.of R)}
    (H : IsPullback m f A.hom t) (R' : Type) [CommRing R'] (g : R →+* R') (W' : Scheme.{0}) (π : W' ⟶ W)
    (f' : W' ⟶ Spec (CommRingCat.of R')) (H' : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) :
    Function.Bijective f'.appTop.hom := by
  obtain ⟨g₀, hg⟩ := Spec.map_surjective (Spec.map (CommRingCat.ofHom g) ≫ t)
  have := H'.paste_horiz H
  rw [← hg] at this
  exact GlobalTheory.UniversalConstants.bijective_appTop_baseChange k A a hp hi R' g₀.hom W' _ f' this

theorem triv_locally_of_faces :
    ∀ (k : Type) [Field k] (X Y Z : Over (Sp k)) (x₀ : 𝟙_ (Over (Sp k)) ⟶ X) (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y) (z₀ : 𝟙_ (Over (Sp k)) ⟶ Z), Smooth X.hom → Smooth Y.hom → IsProper X.hom → IsProper Y.hom → IsProjBy X.hom → IsProjBy Y.hom → GeometricallyIntegral X.hom → GeometricallyIntegral Y.hom → ConnectedSpace Z.left → ∀ M : LB (X ⊗ Y ⊗ Z).left, M.IsLB → Triv (M.pull (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))).left) → Triv (M.pull (lift (fst X Z) (lift (toUnit (X ⊗ Z) ≫ y₀) (snd X Z))).left) → Triv (M.pull (lift (fst X Y) (lift (snd X Y) (toUnit (X ⊗ Y) ≫ z₀))).left) → ∀ z : Z.left, ∃ V : Z.left.Opens, z ∈ V ∧ Triv (M.pull ((snd X (Y ⊗ Z) ≫ snd Y Z).left ⁻¹ᵁ V).ι) := by
  intro k _ X Y Z x₀ y₀ z₀ sX sY pX pY jX jY iX iY cZ M hM f₁ f₂ f₃
  have smXY : Smooth (X ⊗ Y).hom := by
    change Smooth (pullback.fst X.hom Y.hom ≫ X.hom); infer_instance
  have prXY : IsProper (X ⊗ Y).hom := by
    change IsProper (pullback.fst X.hom Y.hom ≫ X.hom); infer_instance
  have gcXY : GeometricallyConnected (X ⊗ Y).hom := by
    change GeometricallyConnected (pullback.fst X.hom Y.hom ≫ X.hom)
    have := geometricallyConnected_of_integral X.hom
    have := geometricallyConnected_of_integral Y.hom
    exact GeometricallyConnected.comp _ _
  have giXY : GeometricallyIntegral (X ⊗ Y).hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ smXY gcXY
  have H := fibTriv_clopen M (fun _ : PUnit => 𝟙 _) (fun _ => 1) (snd X (Y ⊗ Z) ≫ snd Y Z).left (fun R _ j => by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_triple_chart X Y Z j
    obtain ⟨m, hm⟩ := exists_pair_chart X Y (j ≫ Z.hom)
    obtain ⟨x₁, hx⟩ := exists_section_baseChange (j ≫ Z.hom) x₀
    obtain ⟨y₁, hy⟩ := exists_section_baseChange (j ≫ Z.hom) y₀
    let B := (Over.pullback (j ≫ Z.hom)).obj X
    let C := (Over.pullback (j ≫ Z.hom)).obj Y
    have hB : IsPullback (pullback.fst X.hom (j ≫ Z.hom)) B.hom X.hom (j ≫ Z.hom) := IsPullback.of_hasPullback _ _
    have hC : IsPullback (pullback.fst Y.hom (j ≫ Z.hom)) C.hom Y.hom (j ≫ Z.hom) := IsPullback.of_hasPullback _ _
    have sB : Smooth B.hom := MorphismProperty.of_isPullback hB sX
    have sC : Smooth C.hom := MorphismProperty.of_isPullback hC sY
    have pB : IsProper B.hom := MorphismProperty.of_isPullback hB pX
    have pC : IsProper C.hom := MorphismProperty.of_isPullback hC pY
    have sm : Smooth (B ⊗ C).hom := MorphismProperty.of_isPullback hm smXY
    have pr : IsProper (B ⊗ C).hom := MorphismProperty.of_isPullback hm prXY
    have gi : GeometricallyIntegral (B ⊗ C).hom := MorphismProperty.of_isPullback hm giXY
    have pj : IsProjBy (B ⊗ C).hom := by
      obtain ⟨g₀, hg⟩ := Spec.map_surjective (j ≫ Z.hom)
      have hm' := hm
      conv at hm' => arg 4; rw [← hg]
      exact GlobalTheory.AbLaw.isProjBy_baseChange k R g₀.hom _ _ _ _ _ hm' (GlobalTheory.AbLaw.isProjBy_tensor k X Y jX jY)
    have hN : (LB.LinComb M (fun _ : PUnit => q ≫ 𝟙 _) (fun _ => 1)).IsLB := DVR.linComb_isLB _ hM _ _
    have pf := GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy R _ _ sm pj
    refine ⟨_, q, (B ⊗ C).hom, hq,
      GlobalTheory.TrivLocus.isClosed_trivLocus R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr gi,
      fun F _ g W π f' => GlobalTheory.T.lineBundle_trivial_basicOpen_of_trivial_fibre_product R B C x₁ y₁ inferInstance inferInstance pB pC
        (bijective_appTop_baseChange X x₀ pX iX hB) (bijective_appTop_baseChange Y y₀ pY iY hC)
        (bijective_appTop_baseChange (X ⊗ Y) (lift x₀ y₀) prXY giXY hm) _ hN (pf _ hN) ?_ ?_ F g W π f'⟩
    · rw [triv_pull_comp_iff]
      refine trivAt_face₂ f₂ _ (B.hom ≫ j ≫ Z.hom) ?_
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact hy B
    · rw [triv_pull_comp_iff]
      refine trivAt_face₁ f₁ _ (C.hom ≫ j ≫ Z.hom) ?_
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact hx C)
  have hclopen : IsClopen (fibTriv M (fun _ : PUnit => 𝟙 _) (fun _ => 1) (snd X (Y ⊗ Z) ≫ snd Y Z).left) :=
    ⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩
  have ne : (fibTriv M (fun _ : PUnit => 𝟙 _) (fun _ => 1) (snd X (Y ⊗ Z) ≫ snd Y Z).left).Nonempty := by
    let g : Spec (CommRingCat.of k) ⟶ Z.left := z₀.left
    refine ⟨g (default : PrimeSpectrum k), k, inferInstance, g, _, _, _, ⟨_, rfl⟩,
      IsPullback.of_hasPullback (snd X (Y ⊗ Z) ≫ snd Y Z).left g, ?_⟩
    exact trivAt_face₃ f₃ _ (pullback.snd _ g) pullback.condition
  intro z
  obtain ⟨V, hV, hT⟩ := H.1 ((hclopen.eq_univ ne).ge (Set.mem_univ z))
  exact ⟨V, hV, (trivAt_id_iff M _).1 hT⟩

end GlobalTheory.CubeLocal
