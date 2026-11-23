import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationSepClosureIsEquivalenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafHomEquivNaturalSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentFreeSheafCechLevelSepClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCochainsHomologyAddEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeraySimplicialCocycleCoboundaryOfAcyclicLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimplicialCochainRepresentingClassAcyclicLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelAcyclicStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.GalFld

variable (R : Type) [CommRing R]

abbrev cochC (E : Spc) (F : Shv R) : CosimplicialObject AddCommGrpCat.{1} :=
  (E ⋙ free R).rightOp ⋙ preadditiveYoneda.obj F

abbrev cochX (E : Spc) (F : Shv R) : CochainComplex AddCommGrpCat.{1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (cochC R E F)

theorem cochX_d_apply (E : Spc) (F : Shv R) (m : ℕ) (x : (cochX R E F).X m) :
    (cochX R E F).d m (m + 1) x = cobd (E := E) (n := m) (show (free R).obj (E.obj (op ⦋m⦌)) ⟶ F from x) := by
  have hd : (cochX R E F).d m (m + 1) = AlgebraicTopology.AlternatingCofaceMapComplex.objD (cochC R E F) m :=
    CochainComplex.of_d (fun n => (cochC R E F).obj ⦋n⦌) (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cochC R E F)) m
  rw [hd]
  let φ : ((cochC R E F).obj ⦋m⦌ ⟶ (cochC R E F).obj ⦋m + 1⦌) →+ (cochC R E F).obj ⦋m + 1⦌ :=
    AddMonoidHom.mk' (fun f => f x) (fun f g => rfl)
  change φ (AlgebraicTopology.AlternatingCofaceMapComplex.objD _ m) = _
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, map_sum, map_zsmul, cobd]
  rfl

theorem etaleCohomology_simplicialCochain_representation_step (F : Shv R) (E : Spc) (n i : ℕ) (hi : (ComplexShape.up ℕ).prev n = i)
    (hsurj : ∀ x : H R E F n, ∃ s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd s = 0 ∧ IsCls s x)
    (hrange : ∀ x : (cochX R E F).X n, cobd (E := E) (n := n) (show (free R).obj (E.obj (op ⦋n⦌)) ⟶ F from x) = 0 →
      (IsCls (E := E) (n := n) (show (free R).obj (E.obj (op ⦋n⦌)) ⟶ F from x) 0 ↔ ∃ y : (cochX R E F).X i, (cochX R E F).d i n y = x)) :
    Nonempty (H R E F n ≃+ (cochX R E F).homology n) := by
  obtain ⟨hex, hadd, huniq, -, -⟩ := GlobalTheory.T.simplicialCochain_classes_basic_properties R F E n
  let X := cochX R E F
  let S := X.sc' i n (n + 1)
  have hg : ∀ x : S.X₂, S.g.hom x = 0 ↔ cobd (E := E) (n := n) (show (free R).obj (E.obj (op ⦋n⦌)) ⟶ F from x) = 0 := by
    intro x
    have h := cochX_d_apply R E F n x
    change (cochX R E F).d n (n+1) x = 0 ↔ _
    rw [h]
    exact Iff.rfl
  have hex' : ∀ x : AddMonoidHom.ker S.g.hom, ∃ c : H R E F n,
      IsCls (E := E) (n := n) (show (free R).obj (E.obj (op ⦋n⦌)) ⟶ F from x.1) c :=
    fun x => hex _ ((hg x.1).1 (AddMonoidHom.mem_ker.mp x.2))
  let Φ : AddMonoidHom.ker S.g.hom →+ H R E F n :=
    AddMonoidHom.mk' (fun x => Classical.choose (hex' x)) (fun a b =>
      huniq _ _ _ (Classical.choose_spec (hex' (a + b)))
        (hadd _ _ _ _ (Classical.choose_spec (hex' a)) (Classical.choose_spec (hex' b))))
  have hΦ : ∀ x, IsCls (E := E) (n := n) (show (free R).obj (E.obj (op ⦋n⦌)) ⟶ F from x.1) (Φ x) :=
    fun x => Classical.choose_spec (hex' x)
  have hsurjΦ : Function.Surjective Φ := by
    intro c
    obtain ⟨s, hs, hc⟩ := hsurj c
    refine ⟨⟨s, AddMonoidHom.mem_ker.mpr ((hg s).2 hs)⟩, ?_⟩
    exact huniq _ _ _ (hΦ _) hc
  have hker : AddMonoidHom.range S.abToCycles = Φ.ker := by
    ext x
    rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
    have hx := (hg x.1).1 (AddMonoidHom.mem_ker.mp x.2)
    constructor
    · rintro ⟨y, rfl⟩
      have h1 := (hrange _ hx).2 ⟨y, rfl⟩
      exact huniq _ _ _ (hΦ _) h1
    · intro h0
      have h1 := hΦ x
      rw [h0] at h1
      obtain ⟨y, hy⟩ := (hrange _ hx).1 h1
      exact ⟨y, Subtype.ext hy⟩
  refine ⟨?_⟩
  refine (QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurjΦ).symm.trans ?_
  refine (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans ?_
  exact ((X.homologyIsoSc' i n (n + 1) hi (CochainComplex.next ℕ n)) ≪≫ S.abHomologyIso).symm.addCommGroupIsoToAddEquiv

theorem isCls_zero (F : Shv R) (E : Spc) (n : ℕ) :
    IsCls (E := E) (n := n) (0 : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) 0 := by
  obtain ⟨hex, hadd, huniq, -, -⟩ := GlobalTheory.T.simplicialCochain_classes_basic_properties R F E n
  obtain ⟨c, hc⟩ := hex 0 (by simp [cobd])
  have h2 := hadd _ _ _ _ hc hc
  rw [add_zero] at h2
  have h3 : c = c + c := huniq _ _ _ hc h2
  have hc0 : c = 0 := by
    have := congrArg (fun z => z - c) h3
    simpa using this.symm
  rwa [hc0] at hc

theorem bridge (F : Shv R) (E : Spc)
    (hA : ∀ k m : ℕ, 0 < m → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0) (n : ℕ) :
    Nonempty (H R E F n ≃+ (cochX R E F).homology n) := by
  have hsurj := GlobalTheory.T.exists_simplicialCochain_representing_class_acyclicLevels R F E n (fun k m hm _ y => hA k m hm y)
  rcases n with _ | m
  · refine etaleCohomology_simplicialCochain_representation_step R F E 0 0 (CochainComplex.prev_nat_zero) hsurj ?_
    obtain ⟨hinj0, -⟩ := GlobalTheory.T.leray_simplicialCocycle_coboundary_of_acyclicLevels R F E 0 (fun k m hm _ y => hA k m hm y)
    intro x _
    have hd : (cochX R E F).d 0 0 = 0 := (cochX R E F).shape 0 0 (by change ¬ (0 + 1 = 0); omega)
    constructor
    · intro h
      refine ⟨0, ?_⟩
      rw [hd]
      exact (hinj0 _ h).symm
    · rintro ⟨y, rfl⟩
      rw [hd]
      exact isCls_zero R F E 0
  · refine etaleCohomology_simplicialCochain_representation_step R F E (m + 1) m (CochainComplex.prev_nat_succ m) hsurj ?_
    obtain ⟨-, hinjS⟩ := GlobalTheory.T.leray_simplicialCocycle_coboundary_of_acyclicLevels R F E m (fun k m hm _ y => hA k m hm y)
    intro x _
    constructor
    · intro h
      obtain ⟨t, ht⟩ := hinjS _ h
      exact ⟨t, (cochX_d_apply R E F m t).trans ht⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨-, -, -, hcb, -⟩ := GlobalTheory.T.simplicialCochain_classes_basic_properties R F E m
      obtain ⟨hex, -, -, -, -⟩ := GlobalTheory.T.simplicialCochain_classes_basic_properties R F E (m + 1)
      have hcc : cobd (E := E) (n := m + 1) (cobd (E := E) (n := m) (show (free R).obj (E.obj (op ⦋m⦌)) ⟶ F from y)) = 0 := by
        have h : ((cochX R E F).d m (m + 1) ≫ (cochX R E F).d (m + 1) (m + 2)) y = 0 := by
          rw [HomologicalComplex.d_comp_d]; rfl
        rw [ConcreteCategory.comp_apply] at h
        have h1 := cochX_d_apply R E F (m + 1) ((cochX R E F).d m (m + 1) y)
        have h2 := cochX_d_apply R E F m y
        rw [← h2, ← h1]
        exact h
      obtain ⟨c, hc⟩ := hex _ hcc
      have hc0 := hcb _ c hc
      rw [cochX_d_apply]
      rw [hc0] at hc
      exact hc

section Cech
variable {Y X : Scheme.{0}} (f : Y ⟶ X)

theorem cechPt_congr (k : ℕ) {U : Scheme.{0}} {x x' : U ⟶ X} {y y' : Fin (k + 1) → (U ⟶ Y)}
    (h : ∀ i, y i ≫ f = x) (h' : ∀ i, y' i ≫ f = x') (hx : x = x') (hy : y = y') :
    cechPt f k x y h = cechPt f k x' y' h' := by
  subst hx hy; rfl

theorem cechPt_map (k : ℕ) {U V : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y))
    (h : ∀ i, y i ≫ f = x) :
    ((cech f).obj (op ⦋k⦌)).map g.op (cechPt f k x y h) =
      cechPt f k (g ≫ x) (fun i => g ≫ y i) (fun i => by rw [Category.assoc, h i]) := by
  have key : yoneda.map g ≫ WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x)
      (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i]) =
      WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map (g ≫ x))
      (fun i => yoneda.map (g ≫ y i)) (fun i => by rw [← yoneda.map_comp, Category.assoc, h i]) := by
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc]
      erw [WidePullback.lift_π, WidePullback.lift_π]
      simp
    · rw [Category.assoc]
      erw [WidePullback.lift_base, WidePullback.lift_base]
      simp
  have := congrArg (fun φ => φ.app (op V) (𝟙 V)) key
  simp only [FunctorToTypes.comp] at this
  unfold cechPt
  have hn := ConcreteCategory.congr_hom ((WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x)
      (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i])).naturality g.op) (𝟙 U)
  refine hn.symm.trans (Eq.trans ?_ this)
  simp

theorem cechPt_δ (m : ℕ) (i : Fin (m + 2)) {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (m + 2) → (U ⟶ Y))
    (h : ∀ j, y j ≫ f = x) :
    ((cech f).δ i).app (op U) (cechPt f (m + 1) x y h) =
      cechPt f m x (fun j => y (i.succAbove j)) (fun j => h _) := by
  have key : WidePullback.lift (arrows := fun _ : Fin (m + 2) => yoneda.map f) (yoneda.map x)
      (fun j => yoneda.map (y j)) (fun j => by rw [← yoneda.map_comp, h j]) ≫ (cech f).δ i =
      WidePullback.lift (arrows := fun _ : Fin (m + 1) => yoneda.map f) (yoneda.map x)
      (fun j => yoneda.map (y (i.succAbove j))) (fun j => by rw [← yoneda.map_comp, h _]) := by
    dsimp only [SimplicialObject.δ, cech, Arrow.cechNerve]
    apply WidePullback.hom_ext
    · intro j
      erw [Category.assoc, WidePullback.lift_π, WidePullback.lift_π, WidePullback.lift_π]
      rfl
    · erw [Category.assoc, WidePullback.lift_base, WidePullback.lift_base, WidePullback.lift_base]
  have := congrArg (fun φ => φ.app (op U) (𝟙 U)) key
  simp only [FunctorToTypes.comp] at this
  exact this
end Cech

section Gal
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

abbrev fK : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Ω))

def galPt (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) : Sx (cech (fK K Ω)) k (Spec (CommRingCat.of Ω)) :=
  cechPt (fK K Ω) k (fK K Ω) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω)))
    (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)

theorem galPt_mul (k : ℕ) (τ : Ω ≃ₐ[K] Ω) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) :
    ((cech (fK K Ω)).obj (op ⦋k⦌)).map (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))).op (galPt K Ω k σ) =
      galPt K Ω k (fun i => τ * σ i) := by
  rw [galPt, cechPt_map]
  apply cechPt_congr
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => τ.commutes x
  · funext i
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

theorem galPt_face (m : ℕ) (i : Fin (m + 2)) (σ : Fin (m + 2) → (Ω ≃ₐ[K] Ω)) :
    ((cech (fK K Ω)).δ i).app (op (Spec (CommRingCat.of Ω))) (galPt K Ω (m + 1) σ) =
      galPt K Ω m (σ ∘ i.succAbove) := by
  rw [galPt, cechPt_δ]
  rfl

variable (R : Type) [CommRing R] (F : Shv R) (M : Type) [AddCommGroup M]
  (e : M ≃+ Sec F (Spec (CommRingCat.of Ω)))

def galE (m : ℕ) : (cochC R (cech (fK K Ω)) F).obj ⦋m⦌ →+ ((Fin (m + 1) → (Ω ≃ₐ[K] Ω)) → M) where
  toFun s σ := e.symm (val (show (free R).obj ((cech (fK K Ω)).obj (op ⦋m⦌)) ⟶ F from s) _ (galPt K Ω m σ))
  map_zero' := by
    funext σ
    have h := ((GlobalTheory.T.freeEtaleModuleSheaf_hom_equiv_natural_sections R ((cech (fK K Ω)).obj (op ⦋m⦌)) F).2.2.2.2.2 0 0 0 _ (galPt K Ω m σ)).2
    rw [zero_smul, zero_smul] at h
    simp only [Pi.zero_apply]
    rw [← map_zero e.symm]
    exact congrArg e.symm h
  map_add' a b := by
    funext σ
    have h := ((GlobalTheory.T.freeEtaleModuleSheaf_hom_equiv_natural_sections R ((cech (fK K Ω)).obj (op ⦋m⦌)) F).2.2.2.2.2 a b 0 _ (galPt K Ω m σ)).1
    simp only [Pi.add_apply]
    rw [← map_add e.symm]
    exact congrArg e.symm h

theorem galE_apply (m : ℕ) (s : (cochC R (cech (fK K Ω)) F).obj ⦋m⦌) (σ : Fin (m + 1) → (Ω ≃ₐ[K] Ω)) :
    galE K Ω R F M e m s σ = e.symm (val (show (free R).obj ((cech (fK K Ω)).obj (op ⦋m⦌)) ⟶ F from s) _ (galPt K Ω m σ)) := rfl

end Gal

theorem cohomology_field_addEquiv_galois : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (M : Rep.{0} R (Ω ≃ₐ[K] Ω)) [GroundTheory.ProfCoh.IsDiscreteRep M] (e : M ≃+ Sec F (Spec (CommRingCat.of Ω))), (∀ (σ : Ω ≃ₐ[K] Ω) (m : M), e (M.ρ σ m) = Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (e m)) → ∀ n : ℕ, Nonempty (H R (sp K) F n ≃+ GroundTheory.ProfCoh.cohomology M n) := by
  intro R _ F hF K Ω _ _ _ _ M _ e he n
  have hρ : ∀ (τ : Ω ≃ₐ[K] Ω) (v : Sec F (Spec (CommRingCat.of Ω))),
      M.ρ τ (e.symm v) = e.symm (Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) v) := by
    intro τ v
    apply e.injective
    rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hinj : ∀ m, Function.Injective (galE K Ω R F M e m) := by
    intro m a b hab
    apply (GlobalTheory.T.galoisDescent_freeSheaf_cechLevel_sepClosure R F hF K Ω m).1
    funext σ
    have := congrFun hab σ
    rw [galE_apply, galE_apply] at this
    exact e.symm.injective this
  have himg : ∀ m (φ : (Fin (m + 1) → (Ω ≃ₐ[K] Ω)) → M), (∃ c, galE K Ω R F M e m c = φ) ↔
      IsLocallyConstant φ ∧ ∀ (τ : Ω ≃ₐ[K] Ω) (σ : Fin (m + 1) → (Ω ≃ₐ[K] Ω)), φ (fun i => τ * σ i) = M.ρ τ (φ σ) := by
    intro m φ
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨?_, ?_⟩
      · exact ((GlobalTheory.T.galoisDescent_freeSheaf_cechLevel_sepClosure R F hF K Ω m).2.1 c).comp e.symm
      · intro τ σ
        rw [galE_apply, galE_apply, hρ, ← galPt_mul,
          (GlobalTheory.T.freeEtaleModuleSheaf_hom_equiv_natural_sections R ((cech (fK K Ω)).obj (op ⦋m⦌)) F).2.2.1]
    · rintro ⟨hlc, heq⟩
      obtain ⟨s, hs⟩ := (GlobalTheory.T.galoisDescent_freeSheaf_cechLevel_sepClosure R F hF K Ω m).2.2 (fun σ => e (φ σ)) (hlc.comp e) (by
        intro τ σ
        rw [heq, he])
      refine ⟨s, ?_⟩
      funext σ
      exact (congrArg e.symm (hs σ)).trans (e.symm_apply_apply _)
  have hface : ∀ m (i : Fin (m + 2)) (c : (cochC R (cech (fK K Ω)) F).obj ⦋m⦌) (σ : Fin (m + 2) → (Ω ≃ₐ[K] Ω)),
      galE K Ω R F M e (m + 1) ((cochC R (cech (fK K Ω)) F).δ i c) σ = galE K Ω R F M e m c (σ ∘ i.succAbove) := by
    intro m i c σ
    have h4 := (GlobalTheory.T.freeEtaleModuleSheaf_hom_equiv_natural_sections R ((cech (fK K Ω)).obj (op ⦋m⦌)) F).2.2.2.1 _ ((cech (fK K Ω)).δ i) c
      (Spec (CommRingCat.of Ω)) (galPt K Ω (m + 1) σ)
    rw [galE_apply, galE_apply, ← galPt_face, ← h4]
    rfl
  obtain ⟨b⟩ := bridge R F (cech (fK K Ω)) (fun k m hm y => GlobalTheory.T.cohomology_cech_level_eq_zero_of_pos R F hF K Ω k m hm y) n
  obtain ⟨c⟩ := GlobalTheory.T.homogeneousCochains_homology_addEquiv_alt R (Ω ≃ₐ[K] Ω) M (cochC R (cech (fK K Ω)) F) (galE K Ω R F M e) hinj himg hface n
  exact ⟨(AddEquiv.ofBijective (pull R (cechAug (fK K Ω)) F n) (GlobalTheory.T.etaleCechAugmentation_sepClosure_isEquivalence R F hF K Ω n)).trans (b.trans c)⟩

example : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (M : Rep.{0} R (Ω ≃ₐ[K] Ω)) [GroundTheory.ProfCoh.IsDiscreteRep M] (e : M ≃+ Sec F (Spec (CommRingCat.of Ω))), (∀ (σ : Ω ≃ₐ[K] Ω) (m : M), e (M.ρ σ m) = Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (e m)) → ∀ n : ℕ, Nonempty (H R (sp K) F n ≃+ GroundTheory.ProfCoh.cohomology M n) := cohomology_field_addEquiv_galois

end GlobalTheory.EtC.GalFld

end
