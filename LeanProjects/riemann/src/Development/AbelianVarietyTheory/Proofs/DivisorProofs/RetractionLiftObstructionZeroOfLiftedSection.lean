import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObstructionPullbackEqZeroOfNaturalLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalChartLiftsOfMorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijectiveStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem appLE_apply_of_eq_id {X : Scheme.{0}} {g : X ⟶ X} (hg : g = 𝟙 X) {U V : X.Opens} (e : V ≤ g ⁻¹ᵁ U)
    (e' : V ≤ U) (x : Γ(X, U)) : (g.appLE U V e).hom x = (X.presheaf.map (homOfLE e').op).hom x := by
  subst hg
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  rfl

theorem appLE_appLE_of_retr {X₀ Z₀ : Scheme.{0}} {j₀ : X₀ ⟶ Z₀} {f₀ : Z₀ ⟶ X₀} (hjf : j₀ ≫ f₀ = 𝟙 X₀)
    (U : X₀.Opens) (U' : Z₀.Opens) (U'' : X₀.Opens) (e₁ : U' ≤ f₀ ⁻¹ᵁ U) (e₂ : U'' ≤ j₀ ⁻¹ᵁ U')
    (e : U'' ≤ U) (x : Γ(X₀, U)) :
    (j₀.appLE U' U'' e₂).hom ((f₀.appLE U U' e₁).hom x) = (X₀.presheaf.map (homOfLE e).op).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact appLE_apply_of_eq_id hjf _ e x

theorem ext_tri_res_pull1 {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁]
    {X X' X'' : Scheme.{0}} {ψ : X'' ⟶ X'} {φ : X' ⟶ X} {s' : X' ⟶ Sp R₀} {s'' : X'' ⟶ Sp R₀}
    (h' : ψ ≫ s' = s'' ≫ spMap (RingHom.id R₀)) (a : CatCoh.H1 (ext R₁ (OAff s'))) :
    (extMap R₁ (cechTriplePullbackSecond (φ := φ) h')).pull1 ((extMap R₁ (pairRes φ s')).pull1 a) =
      (extMap R₁ (cechTripleRestrictFirst ψ φ s'')).pull1 ((extMap R₁ (pairPull h')).pull1 a) := by
  rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
  refine CoefMap.pullCohomologyOne_eq_of_natTrans ((extMap R₁ (pairRes φ s')).comp (extMap R₁ (cechTriplePullbackSecond (φ := φ) h')))
    ((extMap R₁ (pairPull h')).comp (extMap R₁ (cechTripleRestrictFirst ψ φ s''))) { app U := 𝟙 _ } (fun U b ↦ ?_) a
  erw [mp_id]
  induction b using TensorProduct.induction_on with
  | zero => (erw [map_zero]) <;> rfl
  | tmul x y => rfl
  | add x y hx hy => erw [map_add, map_add, hx, hy]

theorem retractionLiftObstruction_zero_of_liftedSection_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (j₀ : X₀ ⟶ Z₀) (hj : j₀ ≫ t₀ = s₀ ≫ spMap (RingHom.id R₀)) (j : X ⟶ Z), j₀ ≫ f₀ = 𝟙 X₀ → j ≫ t = s → i ≫ j = j₀ ≫ k → ∀ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l → ∀ (w : GlobForm s₀) (c : GlobalTheory.CatCoh.H1 (ext R₁ (OAff t₀))), (ofSys S).IsOb1 (pairPre S' f₀) (pairPull h) l α w ((extMap R₁ (pairRes f₀ t₀)).pull1 c) → IsExtendedPullbackDegOne R₁ hj c 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ Z₀ X Z s₀ t₀ s t i k hi hkk S S' P P' f₀ h j₀ hj j hjf hjt hij l hl w c hob
  obtain ⟨l', hl'L, hl'N⟩ := GlobalTheory.T.exists_natural_chart_lifts_of_morphism R R₀ I hI π hπ hk Z₀ X₀ Z X t₀ s₀ t s k i hkk hi S' S P' P j₀ hj j hjt hij
  have hle : ∀ T : (Triple j₀ f₀)ᵒᵖ, T.unop.1.1 ≤ T.unop.1.2.2 := fun T x hx ↦ by
    have h1 := T.unop.2.2 (T.unop.2.1 hx)
    have e := congrArg (fun g : X₀ ⟶ X₀ ↦ g.base x) hjf
    simp at e
    exact e ▸ h1
  let L'' : Pre I π (OTriple j₀ f₀ s₀) := (ofSys S).restrict (cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀))
  let u : ∀ T : (Triple j₀ f₀)ᵒᵖ, (pairPre S' f₀).B ((cechTriplePullbackSecond (φ := f₀) hj).G.obj T) →ₐ[R] L''.B T :=
    fun T ↦ l' ((cechTripleProjFirstSecond j₀ f₀).obj T)
  let v : ∀ T : (Triple j₀ f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj ((cechTriplePullbackSecond (φ := f₀) hj).G.obj T)) →ₐ[R] L''.B T :=
    fun T ↦ mp S.F (homOfLE (hle T)).op
  have hvan := GlobalTheory.T.obstructionPullback_eq_zero_of_naturalLift_alt R R₀ I hI π hπ hk R₁ α (AffOp X₀) (OAff s₀) (Pair f₀)ᵒᵖ (OPair f₀ t₀) (ofSys S)
    (pairPre S' f₀) (pairPull h) l (Triple j₀ f₀)ᵒᵖ (OTriple j₀ f₀ s₀) L'' (cechTriplePullbackSecond hj) u v hl
    (fun T b ↦ hl'L ((cechTripleProjFirstSecond j₀ f₀).obj T) b)
    (fun T T' a b ↦ by
      have e1 : (cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀)).map a = (pairFst j₀).map ((cechTripleProjFirstSecond j₀ f₀).map a) :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      have e2 : (pairFst f₀).map ((cechTripleProjSecondThird j₀ f₀).map a) = (pairSnd j₀).map ((cechTripleProjFirstSecond j₀ f₀).map a) :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      change mp S.F ((cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀)).map a) (l' ((cechTripleProjFirstSecond j₀ f₀).obj T) b) =
        l' ((cechTripleProjFirstSecond j₀ f₀).obj T') (mp S'.F ((pairFst f₀).map ((cechTripleProjSecondThird j₀ f₀).map a)) b)
      rw [e1, e2]
      exact hl'N ((cechTripleProjFirstSecond j₀ f₀).map a) b)
    (fun T b ↦ by
      change S.p _ (mp S.F _ b) = (j₀.appLE _ _ _).hom ((f₀.appLE _ _ _).hom (S.p _ b))
      exact (S.nat _ b).trans (appLE_appLE_of_retr hjf _ _ _ _ _ (hle T) _).symm)
    (fun T T' a b ↦ by
      change mp S.F _ (mp S.F _ b) = mp S.F _ (mp S.F _ b)
      exact (mp_comp S.F _ _ b).symm.trans ((congrArg (fun q ↦ mp S.F q b)
        (Quiver.Hom.unop_inj (Subsingleton.elim _ _))).trans (mp_comp S.F _ _ b)))
    w ((extMap R₁ (pairRes f₀ t₀)).pull1 c) hob
  rw [ext_tri_res_pull1] at hvan
  have inj := (GlobalTheory.T.cechPairRestrict_baseChange_bijective R₀ R₁ Z₀ X₀ s₀ j₀).2 X₀ f₀
  unfold IsExtendedPullbackDegOne
  rw [map_zero]
  exact inj (hvan.trans (map_zero _).symm)

end GlobalTheory.Obs
