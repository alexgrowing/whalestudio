import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

def precompHom {C : Type*} [Category C] [CartesianMonoidalCategory C] {M P Q : C} [MonObj M] (f : P ⟶ Q) :
    (Q ⟶ M) →* (P ⟶ M) where
  toFun := fun g => f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' := fun g₁ g₂ => MonObj.comp_mul f g₁ g₂

theorem comp_list_prod {C : Type*} [Category C] [CartesianMonoidalCategory C] {M P Q : C} [MonObj M]
    (f : P ⟶ Q) {m : ℕ} (u : Fin m → (Q ⟶ M)) :
    f ≫ (List.ofFn u).prod = (List.ofFn fun c => f ≫ u c).prod := by
  have h := map_list_prod (precompHom (M := M) f) (List.ofFn u)
  rw [List.map_ofFn] at h
  exact h

theorem translate_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {m : ℕ} (v' : Fin m → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (cf : Fin m → Γ(X, U.1)) (va : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left) {S : Type} [CommRing S]
    (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ GlobalTheory.LogKS.chart U →
    ∀ (g' : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G) (y : Fin m → (overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G)),
    (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) → IsCombAtG t (GlobalTheory.LogKS.chart U) v' cf va →
    g'.left = spMap (algebraMap S (DualNumber S)) ≫ g₀ → (∀ c, (y c).left = spMap (dualMap φ) ≫ v' c) →
    (∀ c, smT (g₀ ≫ t.G.hom) 0 (y c) = 1) ∧
      ∀ w, GlobalTheory.LogKS.IsTranslate t φ g₀ va w →
        w = (g' * (List.ofFn fun c => smT (g₀ ≫ t.G.hom) (φ (cf c)) (y c)).prod).left := by
  intro E _ _ _ H X t U m v' cf va S _ φ g₀ hg g' y hTan hComb hg' hy
  have hr0 : (epsMul (0 : S)).comp (dualMap φ) =
      ((algebraMap S (DualNumber S)).comp φ).comp (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom := by
    apply RingHom.ext
    intro r
    ext <;> simp [epsMul, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hra : (dualMap φ).comp (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) =
      (algebraMap S (DualNumber S)).comp φ := by
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨fun c => ?_, fun w hw => ?_⟩
  · let gA : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ Over.mk (GlobalTheory.LogKS.chart U) :=
      Over.homMk (spMap ((algebraMap S (DualNumber S)).comp φ)) (by
        show spMap _ ≫ GlobalTheory.LogKS.chart U = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom
        rw [hg, spMap_comp, Category.assoc])
    have h1 : gA ≫ (1 : Over.mk (GlobalTheory.LogKS.chart U) ⟶ t.G) = 1 := MonObj.comp_one gA
    apply Over.OverMorphism.ext
    rw [← h1, smT_left, Over.comp_left, hy c, ← (hTan c).2]
    simp only [gA, Over.homMk_left]
    rw [← Category.assoc, spMap_comp', hr0, spMap_comp, Category.assoc]
  · obtain ⟨g'', V, h1, h2, h3⟩ := hw
    obtain ⟨u, hu, hprod⟩ := hComb
    have hg'' : g'' = g' := Over.OverMorphism.ext (h1.trans hg'.symm)
    let bA : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ tEpsG (GlobalTheory.LogKS.chart U) :=
      Over.homMk (spMap (dualMap φ)) (by
        show spMap (dualMap φ) ≫ spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U =
          spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom
        rw [hg, ← Category.assoc, spMap_comp', hra, spMap_comp, Category.assoc])
    have hV : V = bA ≫ (List.ofFn u).prod := by
      apply Over.OverMorphism.ext
      rw [h2, Over.comp_left, hprod]
      rfl
    have hbAu : ∀ c, bA ≫ u c = smT (g₀ ≫ t.G.hom) (φ (cf c)) (y c) := by
      intro c
      apply Over.OverMorphism.ext
      rw [Over.comp_left, hu c, smT_left, hy c]
      simp only [bA, Over.homMk_left]
      rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', Formalism.L2.Pj.dualMap_comp_epsMul]
    rw [← h3, hg'', hV, comp_list_prod]
    simp only [hbAu]

end GlobalTheory.LogKSDiv
