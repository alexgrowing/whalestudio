import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTestOfGeometricTestStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricTestMapClassicalPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreImageTestIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IndepOfNestedSpecialFibreImagesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.CoreTests

theorem image_iff {T H B G B' F P : Scheme.{0}} (h : H ⟶ B) (s : T ⟶ B) (g : G ⟶ B') (s' : T ⟶ B')
    (r : F ⟶ G) (q : F ⟶ T) (cart : IsPullback r q g s') (u : H ⟶ P) (v : G ⟶ P)
    (e : pullback h s ≅ F) (e₁ : e.hom ≫ q = pullback.snd _ _) (e₂ : e.hom ≫ r ≫ v = pullback.fst _ _ ≫ u)
    (x : T ⟶ P) :
    (∃ c : T ⟶ H, c ≫ h = s ∧ c ≫ u = x) ↔ ∃ c' : T ⟶ G, c' ≫ g = s' ∧ c' ≫ v = x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨pullback.lift c (𝟙 T) (by simpa using hc) ≫ e.hom ≫ r, ?_, ?_⟩
    · simp only [Category.assoc]
      rw [cart.w, reassoc_of% e₁, pullback.lift_snd_assoc, Category.id_comp]
    · simp only [Category.assoc]
      rw [e₂, pullback.lift_fst_assoc]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨cart.lift c (𝟙 T) (by simpa using hc) ≫ e.inv ≫ pullback.fst _ _, ?_, ?_⟩
    · simp only [Category.assoc]
      rw [pullback.condition, ← reassoc_of% e₁, e.inv_hom_id_assoc, cart.lift_snd_assoc, Category.id_comp]
    · simp only [Category.assoc]
      rw [← e₂, e.inv_hom_id_assoc, cart.lift_fst_assoc]

theorem exists_test (hL : GlobalTheory.UT.LL) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J)
    (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (hS : S.Big) (hG : ρ.HasGeo)
    (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (hy : ex.core.Cl y) :
    ∃ τ : ex.core.Test y, ∀ x : Sp (GlobalTheory.ZJ.kb p) ⟶ Q.P.left, x ≫ Q.P.hom = GlobalTheory.ZJ.rPt p ≫ y →
      ((∃ c : Sp (GlobalTheory.ZJ.kb p) ⟶ τ.H.left, c ≫ τ.H.hom = GlobalTheory.ZJ.rPt p ≫ spMap τ.j ∧ c ≫ τ.f ≫ Q.G.ι = x) ↔
        (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  obtain ⟨y₀, t, c, ⟨tm⟩⟩ := (GlobalTheory.T.exists_geometricTest_map_classicalPoint hL o Ω S ρ M U₀ EE hB Q hS hG).1 p y hy
  obtain ⟨τ, e, e₁, e₂⟩ := GlobalTheory.T.exists_uniformisationTest_of_geometricTest hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t c tm hS
  refine ⟨τ, fun x hx => ?_⟩
  exact (image_iff _ _ _ _ _ _ t.mod.cart.1 _ _ e e₁ e₂ x).trans
    (GlobalTheory.T.specialFibre_image_test_independent hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS x hx)

end GlobalTheory.ZH.CoreTests

theorem GlobalTheory.ZH.Clos.Ext.hasTests_and_indep : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.HasTests ∧ ex.core.Indep := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG
  have key := GlobalTheory.ZH.CoreTests.exists_test hL o Ω S ρ M U₀ EE hB Q ex hS hG
  have hT : ex.core.HasTests := fun p _ y hy => ⟨(key p y hy).choose⟩
  refine ⟨hT, GlobalTheory.T.indep_of_nested_special_fibre_images _ hT fun p _ y y' hy hy' hr => ?_⟩
  obtain ⟨τ, hτ⟩ := key p y hy
  obtain ⟨τ', hτ'⟩ := key p y' hy'
  refine ⟨τ, τ', fun c hc => ?_⟩
  have hx : (c ≫ τ.f ≫ Q.G.ι) ≫ Q.P.hom = GlobalTheory.ZJ.rPt p ≫ y := by
    have h : c ≫ τ.f ≫ ex.core.GG.hom = GlobalTheory.ZJ.rPt p ≫ y := by
      rw [τ.f_over, reassoc_of% hc, τ.fac]
    simp only [Category.assoc]
    exact h
  obtain ⟨c', hc', hf⟩ := (hτ' _ (hx.trans hr)).2 ((hτ _ hx).1 ⟨c, hc, rfl⟩)
  refine ⟨c', hc', ?_⟩
  have : Mono ex.core.G.ι := inferInstance
  rw [← cancel_mono ex.core.G.ι, Category.assoc, Category.assoc]
  exact hf
