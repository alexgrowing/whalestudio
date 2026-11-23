import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElementsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactColim

abbrev altC {T : Type 1} [Category.{0} T] (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) :
    CochainComplex AddCommGrpCat.{1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ F)

abbrev altM {T : Type 1} [Category.{0} T] {X Y : CosimplicialObject T} (g : X ⟶ Y) (F : T ⥤ AddCommGrpCat.{1}) :
    altC X F ⟶ altC Y F :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map (Functor.whiskerRight g F)

theorem altM_d {T : Type 1} [Category.{0} T] {X Y : CosimplicialObject T} (g : X ⟶ Y) (F : T ⥤ AddCommGrpCat.{1})
    (n m : ℕ) (w : (altC X F).X n) :
    (altC Y F).d n m ((altM g F).f n w) = (altM g F).f m ((altC X F).d n m w) := by
  have h := ConcreteCategory.congr_hom ((altM g F).comm n m) w
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

theorem altM_comp {T : Type 1} [Category.{0} T] {X Y Z : CosimplicialObject T} (g : X ⟶ Y) (h : Y ⟶ Z)
    (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ) (w : (altC X F).X n) :
    (altM h F).f n ((altM g F).f n w) = (altM (g ≫ h) F).f n w := by
  show F.map (h.app _) (F.map (g.app _) w) = F.map (g.app _ ≫ h.app _) w
  rw [F.map_comp]
  rfl

theorem altM_comp' {T : Type 1} [Category.{0} T] {X Y Z : CosimplicialObject T} (g : X ⟶ Y) (h : Y ⟶ Z)
    (g' : X ⟶ Z) (e : g ≫ h = g') (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ) (w : (altC X F).X n) :
    (altM h F).f n ((altM g F).f n w) = (altM g' F).f n w := by
  subst e
  exact altM_comp g h F n w

theorem exact_elt {T : Type 1} [Category.{0} T] (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ)
    (h : (altC X F).ExactAt (n + 1)) (w : (altC X F).X (n + 1)) (hw : (altC X F).d (n + 1) (n + 2) w = 0) :
    ∃ v : (altC X F).X n, (altC X F).d n (n + 1) v = w := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp), ShortComplex.ab_exact_iff] at h
  exact h w hw

theorem wExact_colimit : ∀ (T : Type 1) [Category.{0} T] (N : T ⥤ AddCommGrpCat.{1}), PreservesFilteredColimitsOfSize.{0, 0} N → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (U : J ⥤ T) (X : J ⥤ CosimplicialObject T) (a : U ⋙ CosimplicialObject.const T ⟶ X) (cU : Cocone U) (cX : Cocone X) (b : (CosimplicialObject.const T).obj cU.pt ⟶ cX.pt), IsColimit cU → (∀ k : SimplexCategory, Nonempty (IsColimit (((evaluation SimplexCategory T).obj k).mapCocone cX))) → (∀ j, a.app j ≫ cX.ι.app j = (CosimplicialObject.const T).map (cU.ι.app j) ≫ b) → (∀ j, WExact N (a.app j)) → WExact N b := by
  intro T _ N hN J _ _ U X a cU cX b hU hX hab hW
  have fe := (GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements T N).1 hN
  have hNc : ∀ {A B C : T} (f : A ⟶ B) (g : B ⟶ C) (x : N.obj A), N.map (f ≫ g) x = N.map g (N.map f x) := by
    intros; simp
  have hab' : ∀ j (k : SimplexCategory), (a.app j).app k ≫ (cX.ι.app j).app k = cU.ι.app j ≫ b.app k := by
    intro j k
    exact NatTrans.congr_app (hab j) k
  have hnat : ∀ {j j' : J} (f : j ⟶ j') (k : SimplexCategory), (a.app j).app k ≫ (X.map f).app k = U.map f ≫ (a.app j').app k := by
    intro j j' f k
    exact (NatTrans.congr_app (a.naturality f) k).symm
  have hXι : ∀ {j j' : J} (f : j ⟶ j') (k : SimplexCategory), (X.map f).app k ≫ (cX.ι.app j').app k = (cX.ι.app j).app k := by
    intro j j' f k
    exact NatTrans.congr_app (cX.w f) k
  have feX : ∀ k : SimplexCategory, (∀ x : N.obj (cX.pt.obj k), ∃ j y, N.map ((cX.ι.app j).app k) y = x) ∧
      ∀ j (y : N.obj ((X.obj j).obj k)), N.map ((cX.ι.app j).app k) y = 0 → ∃ (j' : J) (f : j ⟶ j'), N.map ((X.map f).app k) y = 0 := by
    intro k
    exact fe J (X ⋙ (evaluation SimplexCategory T).obj k) _ (hX k).some
  have feU := fe J U cU hU
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, rfl⟩ := feU.1 x
    have h0 : N.map ((cX.ι.app j).app (SimplexCategory.mk 0)) (N.map ((a.app j).app (SimplexCategory.mk 0)) y) = 0 := by
      rw [← hNc, hab', hNc]; simpa using hx
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h0
    rw [← hNc, hnat, hNc] at hf
    have hk := (hW k).1 (hf.trans (map_zero _).symm)
    rw [← cU.w f, hNc]
    simp only [Functor.comp_obj] at hk
    rw [hk, map_zero]
  ·
    intro y hy
    obtain ⟨j, y', rfl⟩ := (feX _).1 y
    have hδ : ∀ {Y Z : CosimplicialObject T} (g : Y ⟶ Z) (i : Fin 2),
        Y.δ (n := 0) i ≫ g.app (SimplexCategory.mk 1) = g.app (SimplexCategory.mk 0) ≫ Z.δ (n := 0) i :=
      fun g i => g.naturality _
    set d' := N.map ((X.obj j).δ (n := 0) 0) y' - N.map ((X.obj j).δ (n := 0) 1) y' with hd'
    have h1 : N.map ((cX.ι.app j).app (SimplexCategory.mk 1)) d' = 0 := by
      rw [hd', map_sub, ← hNc, ← hNc, hδ, hδ, hNc, hNc]
      exact sub_eq_zero.mpr hy
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h1
    have h2 : N.map ((X.obj k).δ (n := 0) 0) (N.map ((X.map f).app (SimplexCategory.mk 0)) y') =
        N.map ((X.obj k).δ (n := 0) 1) (N.map ((X.map f).app (SimplexCategory.mk 0)) y') := by
      rw [← sub_eq_zero, ← hNc, ← hNc, ← hδ, ← hδ, hNc, hNc, ← map_sub]
      exact hf
    obtain ⟨x, hx⟩ := (hW k).2.1 _ h2
    refine ⟨N.map (cU.ι.app k) x, ?_⟩
    rw [← hNc, ← hab', hNc]
    simp only [Functor.comp_obj] at hx
    rw [hx, ← hNc, hXι]
  · intro n
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp), ShortComplex.ab_exact_iff]
    intro z hz
    obtain ⟨j, z', rfl⟩ := (feX _).1 z
    have h1 : (altM (cX.ι.app j) N).f (n + 2) ((altC (X.obj j) N).d (n + 1) (n + 2) z') = 0 := by
      exact (altM_d (cX.ι.app j) N (n + 1) (n + 2) z').symm.trans hz
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h1
    have h2 : (altC (X.obj k) N).d (n + 1) (n + 2) ((altM (X.map f) N).f (n + 1) z') = 0 := by
      exact (altM_d (X.map f) N (n + 1) (n + 2) z').trans hf
    obtain ⟨v, hv⟩ := exact_elt _ N n ((hW k).2.2 n) _ h2
    refine ⟨(altM (cX.ι.app k) N).f n v, ?_⟩
    show (altC cX.pt N).d n (n + 1) ((altM (cX.ι.app k) N).f n v) = (altM (cX.ι.app j) N).f (n + 1) z'
    rw [altM_d, hv]
    exact altM_comp' (X.map f) (cX.ι.app k) (cX.ι.app j) (cX.w f) N (n + 1) z'

end GlobalTheory.EtC.WExactColim
