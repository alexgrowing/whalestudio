import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.AXO

def USt {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module R M],
    (∀ m : M, (∀ T, m ⊗ₜ[R] (1 : F.obj T) = 0) → m = 0) ∧
    ∀ y : ∀ T, M ⊗[R] F.obj T, (∀ (T T' : C) (φ : T ⟶ T'), ((mp F φ).toLinearMap.lTensor M) (y T) = y T') →
      ∃ m : M, ∀ T, y T = m ⊗ₜ[R] 1

section Tri

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

theorem composite_restriction_pull_injective (ψ : X'' ⟶ X') (φ : X' ⟶ X) (s'' : X'' ⟶ Sp R'') :
    Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 := by
  intro x y e
  obtain ⟨x0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 x
  obtain ⟨y0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 y
  have k : ∀ c, (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull1 c := fun c ↦ by
    rw [← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c
  rw [k, k] at e
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s''
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s'') _ H (triple_cover_affine ψ φ s'')
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s'') _ H (triple_cover_affine ψ φ s'')
    (exists_triple_below_two ψ φ s'')
  rw [CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg e]

theorem isPullO_comp {ρ : R →+* R''} (hρ : τ.comp σ = ρ) (h : φ ≫ s = s' ≫ spMap σ)
    (h' : ψ ≫ s' = s'' ≫ spMap τ) (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap ρ) (a : HO1 s) (a' : HO1 s')
    (a'' : HO1 s'') (p : IsPullO h a a') (p' : IsPullO h' a' a'') : IsPullO h'' a a'' := by
  subst hρ
  apply composite_restriction_pull_injective ψ φ s''
  have p0 : (pairPull h).pull1 a = (pairRes φ s').pull1 a' := p
  have p1 : (pairPull h').pull1 a' = (pairRes ψ s'').pull1 a'' := p'
  have t1 : (cechTripleRestrictComposite ψ φ s'').pull1 ((pairPull h'').pull1 a) =
      (cechTriplePullbackSecond h').pull1 ((pairPull h).pull1 a) := by
    rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
      ((pairPull h).comp (cechTriplePullbackSecond h')) { app U := 𝟙 _ } (fun U b ↦ by
        erw [mp_id]
        exact congrArg (fun q ↦ q.hom b) (Scheme.Hom.appLE_comp_appLE ψ φ U.unop.1.2.2.1 U.unop.1.2.1.1
          U.unop.1.1.1 U.unop.2.2 U.unop.2.1)) a
  have t2 : (cechTriplePullbackSecond (φ := φ) h').pull1 ((pairRes φ s').pull1 a') =
      (cechTripleRestrictFirst ψ φ s'').pull1 ((pairPull h').pull1 a') := by
    rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) a'
  have t3 : (cechTripleRestrictFirst ψ φ s'').pull1 ((pairRes ψ s'').pull1 a'') =
      (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 a'') := by
    rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) a''
  change (cechTripleRestrictComposite ψ φ s'').pull1 ((pairPull h'').pull1 a) =
    (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 a'')
  rw [t1, p0, t2, p1, t3]

theorem isPullO_comp' {ρ : R →+* R''} (hρ : τ.comp σ = ρ) (h : φ ≫ s = s' ≫ spMap σ)
    (h' : ψ ≫ s' = s'' ≫ spMap τ) (χ : X'' ⟶ X) (hχ : χ = ψ ≫ φ) (h'' : χ ≫ s = s'' ≫ spMap ρ) (a : HO1 s)
    (a' : HO1 s') (a'' : HO1 s'') (p : IsPullO h a a') (p' : IsPullO h' a' a'') : IsPullO h'' a a'' := by
  subst hχ; exact isPullO_comp hρ h h' h'' a a' a'' p p'

theorem HO1_eq_zero_of_isAffine [IsAffine X] (s : X ⟶ Sp R) (c : HO1 s) : c = 0 := by
  let T0 : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  refine H1.eq_zero_of_isInitial (F := OAff s) (T₀ := op T0) ?_ c
  exact Limits.IsInitial.ofUniqueHom (fun V ↦ (homOfLE (show V.unop ≤ T0 from
    show V.unop.1 ≤ ⊤ from le_top)).op) (fun _ _ ↦ Subsingleton.elim _ _)

end Tri

variable {R : Type} [CommRing R]

def pO {Y Z : Over (Sp R)} (f : Y ⟶ Z) : HO1 Z.hom →ₗ[R] HO1 Y.hom := pullHO1 (wOver f)

theorem pO_spec {Y Z : Over (Sp R)} (f : Y ⟶ Z) (c : HO1 Z.hom) (c' : HO1 Y.hom) :
    IsPullO (wOver f) c c' ↔ c' = pO f c :=
  ⟨fun e ↦ e.eq_pullHO1, fun e ↦ e ▸ isPullO_pullHO1 _ c⟩

theorem isPullO_id' {X : Scheme.{0}} (s : X ⟶ Sp R) (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R))
    (c : HO1 s) : IsPullO h c c :=
  CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X) (fun _ _ ↦ rfl) c

theorem isPullO_id {X : Scheme.{0}} (s : X ⟶ Sp R) (φ : X ⟶ X) (hφ : φ = 𝟙 X)
    (h : φ ≫ s = s ≫ spMap (RingHom.id R)) (c : HO1 s) : IsPullO h c c := by
  subst hφ; exact isPullO_id' s h c

theorem pO_id (Y : Over (Sp R)) (c : HO1 Y.hom) : pO (𝟙 Y) c = c :=
  ((pO_spec _ _ _).1 (isPullO_id Y.hom (𝟙 Y : Y ⟶ Y).left (Over.id_left Y) _ c)).symm

theorem pO_comp {X Y Z : Over (Sp R)} (f : X ⟶ Y) (g : Y ⟶ Z) (c : HO1 Z.hom) :
    pO (f ≫ g) c = pO f (pO g c) :=
  ((pO_spec _ _ _).1 (isPullO_comp' (RingHom.id_comp _) (wOver g) (wOver f) (f ≫ g).left
    (Over.comp_left _ _ _ f g) (wOver (f ≫ g)) c (pO g c) (pO f (pO g c))
    (isPullO_pullHO1 _ c) (isPullO_pullHO1 _ _))).symm

theorem HO1_base_eq_zero (c : HO1 (𝟙_ (Over (Sp R))).hom) : c = 0 :=
  haveI : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Sp R))
  HO1_eq_zero_of_isAffine _ c

end MainStatements.Hodge.Pf.AXO
