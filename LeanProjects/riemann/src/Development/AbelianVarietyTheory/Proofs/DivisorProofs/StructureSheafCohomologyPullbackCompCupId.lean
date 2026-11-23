import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechDR

section Glob

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C C' C'' : Type} [Category.{0} C] [Category.{0} C'] [Category.{0} C'']
  {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''}

theorem pullGlob1_comp (m : CoefMap σ F F') (n : CoefMap τ F' F'') (ω : Glob1 F) :
    pullGlob1 (m.comp n) ω = pullGlob1 n (pullGlob1 m ω) :=
  Subtype.ext (funext fun _ ↦ (SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) _).symm)

theorem pullGlob1_eq_of_natTrans (m : CoefMap σ F F') {σ' : R →+* R'} (m' : CoefMap σ' F F')
    (θ : m.G ⟶ m'.G) (h : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b) (ω : Glob1 F) :
    pullGlob1 m ω = pullGlob1 m' ω :=
  Subtype.ext (funext fun T ↦ by
    change q1 m T (ω.1 _) = q1 m' T (ω.1 _)
    rw [ω.2 (θ.app T), cechDeRhamCoefMapOneForms_eq_of_natTrans m m' θ h])

end Glob

section Triple

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {ψ : X'' ⟶ X'} {φ : X' ⟶ X}

variable (ψ φ) in

theorem cechTripleRestrictComposite_comp_pairRestrict (s'' : X'' ⟶ Sp R'') :
    (∀ c : HO1 s'', (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull1 c) ∧
    (∀ c : HO2 s'', (cechTripleRestrictComposite ψ φ s'').pull2 ((pairRes (ψ ≫ φ) s'').pull2 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull2 c) ∧
    (∀ c : GlobForm s'', pullGlob1 (cechTripleRestrictComposite ψ φ s'') (pullGlob1 (pairRes (ψ ≫ φ) s'') c) =
      pullGlob1 (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))) c) := by
  refine ⟨fun c ↦ ?_, fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c
  · rw [← CoefMap.pullCohomologyTwo_comp]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c
  · rw [← pullGlob1_comp]
    exact pullGlob1_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c

variable (ψ φ) in

theorem cechTripleRestrictComposite_injective_cohomology_forms (s'' : X'' ⟶ Sp R'') :
    Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 ∧ Function.Injective (cechTripleRestrictComposite ψ φ s'').pull2 ∧
      Function.Injective (pullGlob1 (cechTripleRestrictComposite ψ φ s'')) := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s''
  have hcov := triple_cover_affine ψ φ s''
  have hdir := exists_triple_below_two ψ φ s''
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s'') _ H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s'') _ H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s'') _ H hcov hdir
  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s'' _ hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s'' _ hcov hdir
  have i1 := _root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg
  have i2 := GlobalTheory.T.comma_descent_injective _ _ hs hg hv
  have ig := (_root_.GlobalTheory.restrict_glob1_bijective _ _ hs1 hg1).1
  have k := cechTripleRestrictComposite_comp_pairRestrict ψ φ s''
  refine ⟨fun x y e ↦ ?_, fun x y e ↦ ?_, fun x y e ↦ ?_⟩
  · obtain ⟨x0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 x
    obtain ⟨y0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 y
    rw [k.1, k.1] at e
    rw [i1 e]
  · obtain ⟨x0, rfl⟩ := (pairRes_pull2_bijective (ψ ≫ φ) s'').2 x
    obtain ⟨y0, rfl⟩ := (pairRes_pull2_bijective (ψ ≫ φ) s'').2 y
    rw [k.2.1, k.2.1] at e
    rw [i2 e]
  · obtain ⟨x0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').2.1.2 x
    obtain ⟨y0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').2.1.2 y
    rw [k.2.2, k.2.2] at e
    rw [ig e]

theorem tri_pull_pullO (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) :
    (∀ a : HO1 s, (cechTripleRestrictComposite ψ φ s'').pull1 ((pairPull h'').pull1 a) =
      (cechTriplePullbackSecond h').pull1 ((pairPull h).pull1 a)) ∧
    (∀ a : HO2 s, (cechTripleRestrictComposite ψ φ s'').pull2 ((pairPull h'').pull2 a) =
      (cechTriplePullbackSecond h').pull2 ((pairPull h).pull2 a)) ∧
    (∀ a : GlobForm s, pullGlob1 (cechTripleRestrictComposite ψ φ s'') (pullGlob1 (pairPull h'') a) =
      pullGlob1 (cechTriplePullbackSecond h') (pullGlob1 (pairPull h) a)) := by
  refine ⟨fun a ↦ ?_, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
      ((pairPull h).comp (cechTriplePullbackSecond h')) { app U := 𝟙 _ } (fun U b ↦ by
        erw [mp_id]
        exact congrArg (fun q ↦ q.hom b) (Scheme.Hom.appLE_comp_appLE ψ φ U.unop.1.2.2.1 U.unop.1.2.1.1
          U.unop.1.1.1 U.unop.2.2 U.unop.2.1)) a
  · rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
      ((pairPull h).comp (cechTriplePullbackSecond h')) { app U := 𝟙 _ } (fun U b ↦ by
        erw [mp_id]
        exact congrArg (fun q ↦ q.hom b) (Scheme.Hom.appLE_comp_appLE ψ φ U.unop.1.2.2.1 U.unop.1.2.1.1
          U.unop.1.1.1 U.unop.2.2 U.unop.2.1)) a
  · rw [← pullGlob1_comp, ← pullGlob1_comp]
    exact pullGlob1_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
      ((pairPull h).comp (cechTriplePullbackSecond h')) { app U := 𝟙 _ } (fun U b ↦ by
        erw [mp_id]
        exact congrArg (fun q ↦ q.hom b) (Scheme.Hom.appLE_comp_appLE ψ φ U.unop.1.2.2.1 U.unop.1.2.1.1
          U.unop.1.1.1 U.unop.2.2 U.unop.2.1)) a

theorem tri_res_pullO (h' : ψ ≫ s' = s'' ≫ spMap τ) :
    (∀ a : HO1 s', (cechTriplePullbackSecond (φ := φ) h').pull1 ((pairRes φ s').pull1 a) =
      (cechTripleRestrictFirst ψ φ s'').pull1 ((pairPull h').pull1 a)) ∧
    (∀ a : HO2 s', (cechTriplePullbackSecond (φ := φ) h').pull2 ((pairRes φ s').pull2 a) =
      (cechTripleRestrictFirst ψ φ s'').pull2 ((pairPull h').pull2 a)) ∧
    (∀ a : GlobForm s', pullGlob1 (cechTriplePullbackSecond (φ := φ) h') (pullGlob1 (pairRes φ s') a) =
      pullGlob1 (cechTripleRestrictFirst ψ φ s'') (pullGlob1 (pairPull h') a)) := by
  refine ⟨fun a ↦ ?_, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) a
  · rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) a
  · rw [← pullGlob1_comp, ← pullGlob1_comp]
    exact pullGlob1_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) a

variable (ψ φ) in

theorem tri_res_resO (s'' : X'' ⟶ Sp R'') :
    (∀ a : HO1 s'', (cechTripleRestrictFirst ψ φ s'').pull1 ((pairRes ψ s'').pull1 a) =
      (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 a)) ∧
    (∀ a : HO2 s'', (cechTripleRestrictFirst ψ φ s'').pull2 ((pairRes ψ s'').pull2 a) =
      (cechTripleRestrictComposite ψ φ s'').pull2 ((pairRes (ψ ≫ φ) s'').pull2 a)) ∧
    (∀ a : GlobForm s'', pullGlob1 (cechTripleRestrictFirst ψ φ s'') (pullGlob1 (pairRes ψ s'') a) =
      pullGlob1 (cechTripleRestrictComposite ψ φ s'') (pullGlob1 (pairRes (ψ ≫ φ) s'') a)) := by
  refine ⟨fun a ↦ ?_, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) a
  · rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) a
  · rw [← pullGlob1_comp, ← pullGlob1_comp]
    exact pullGlob1_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) a

end Triple

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR

section Maps

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {ψ : X'' ⟶ X'} {φ : X' ⟶ X}

theorem pairRes_pullHO2 (h : φ ≫ s = s' ≫ spMap σ) (a : HO2 s) :
    (pairRes φ s').pull2 (pullHO2 h a) = (pairPull h).pull2 a :=
  (LinearEquiv.ofBijective (pairRes φ s').pull2 (pairRes_pull2_bijective φ s')).apply_symm_apply _

theorem eq_pullHO2 (h : φ ≫ s = s' ≫ spMap σ) {a : HO2 s} {b : HO2 s'}
    (e : (pairPull h).pull2 a = (pairRes φ s').pull2 b) : b = pullHO2 h a :=
  (pairRes_pull2_bijective φ s').1 (e.symm.trans (pairRes_pullHO2 h a).symm)

theorem pullHO1_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HO1 s) :
    pullHO1 h' (pullHO1 h a) = pullHO1 h'' a := by
  refine IsPullO.eq_pullHO1 h'' ((cechTripleRestrictComposite_injective_cohomology_forms ψ φ s'').1 ?_)
  have p0 : (pairPull h).pull1 a = (pairRes φ s').pull1 (pullHO1 h a) := isPullO_pullHO1 h a
  have p1 : (pairPull h').pull1 (pullHO1 h a) = (pairRes ψ s'').pull1 (pullHO1 h' (pullHO1 h a)) :=
    isPullO_pullHO1 h' _
  rw [(tri_pull_pullO h h' h'').1, p0, (tri_res_pullO h').1, p1, (tri_res_resO ψ φ s'').1]

theorem pullHO2_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HO2 s) :
    pullHO2 h' (pullHO2 h a) = pullHO2 h'' a := by
  refine eq_pullHO2 h'' ((cechTripleRestrictComposite_injective_cohomology_forms ψ φ s'').2.1 ?_)
  rw [(tri_pull_pullO h h' h'').2.1, ← pairRes_pullHO2 h, (tri_res_pullO h').2.1, ← pairRes_pullHO2 h',
    (tri_res_resO ψ φ s'').2.1]

theorem pullForm_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : GlobForm s) :
    pullForm h' (pullForm h a) = pullForm h'' a := by
  refine IsPullForm.eq_pullForm h'' ((cechTripleRestrictComposite_injective_cohomology_forms ψ φ s'').2.2 ?_)
  have p0 : pullGlob1 (pairPull h) a = pullGlob1 (pairRes φ s') (pullForm h a) := isPullForm_pullForm h a
  have p1 : pullGlob1 (pairPull h') (pullForm h a) = pullGlob1 (pairRes ψ s'') (pullForm h' (pullForm h a)) :=
    isPullForm_pullForm h' _
  rw [(tri_pull_pullO h h' h'').2.2, p0, (tri_res_pullO h').2.2, p1, (tri_res_resO ψ φ s'').2.2]

theorem pullHH1_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HH1 s) :
    pullHH1 h' (pullHH1 h a) = pullHH1 h'' a :=
  IsPull1.eq_pullHH1 h'' ((isPull_comp h h' h'').1 _ _ _ (isPull1_pullHH1 h a) (isPull1_pullHH1 h' _))

theorem pullHH2_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HH2 s) :
    pullHH2 h' (pullHH2 h a) = pullHH2 h'' a :=
  IsPull2.eq_pullHH2 h'' ((isPull_comp h h' h'').2 _ _ _ (isPull2_pullHH2 h a) (isPull2_pullHH2 h' _))

theorem pullHO2_cup (h : φ ≫ s = s' ≫ spMap σ) (a b : HO1 s) :
    pullHO2 h (cup _ a b) = cup _ (pullHO1 h a) (pullHO1 h b) := by
  refine (eq_pullHO2 h ?_).symm
  rw [CoefMap.pullCohomologyTwo_cup, CoefMap.pullCohomologyTwo_cup, isPullO_pullHO1 h a, isPullO_pullHO1 h b]

theorem pullHH2_cupHH (h : φ ≫ s = s' ≫ spMap σ) (a b : HH1 s) :
    pullHH2 h (cupHH s a b) = cupHH s' (pullHH1 h a) (pullHH1 h b) :=
  (IsPull2.eq_pullHH2 h ((isPull1_pullHH1 h a).cup (isPull1_pullHH1 h b))).symm

theorem toHO1_pullHH1 (h : φ ≫ s = s' ≫ spMap σ) (a : HH1 s) :
    toHO1 s' (pullHH1 h a) = pullHO1 h (toHO1 s a) :=
  IsPullO.eq_pullHO1 h (isPull1_pullHH1 h a).toO

theorem pullHO1_id (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : HO1 s) : pullHO1 h c = c :=
  (IsPullO.eq_pullHO1 h (CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X)
    (fun _ _ ↦ rfl) c)).symm

theorem pullHO2_id (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : HO2 s) : pullHO2 h c = c :=
  (eq_pullHO2 h (CoefMap.pullCohomologyTwo_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X)
    (fun _ _ ↦ rfl) c)).symm

theorem pullForm_id (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : GlobForm s) : pullForm h c = c :=
  (IsPullForm.eq_pullForm h (pullGlob1_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X)
    (fun _ _ ↦ rfl) c)).symm

theorem pullHH1_id (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : HH1 s) : pullHH1 h c = c :=
  (IsPull1.eq_pullHH1 h (isPull1_id h c)).symm

theorem pullHH2_id (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : HH2 s) : pullHH2 h c = c :=
  (IsPull2.eq_pullHH2 h (isPull2_id h c)).symm

end Maps

end GlobalTheory.CechDR

namespace GlobalTheory.AbCoh

theorem pull_comp_cup_id : (∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (R'' : Type) [CommRing R''] (X'' : Scheme.{0}) (s'' : X'' ⟶ Sp R'') (τ : R' →+* R'') (ψ : X'' ⟶ X') (h' : ψ ≫ s' = s'' ≫ spMap τ) (ρ : R →+* R'') (χ : X'' ⟶ X) (h'' : χ ≫ s = s'' ≫ spMap ρ), χ = ψ ≫ φ → (∀ r, ρ r = τ (σ r)) → (∀ a, pullHO1 h' (pullHO1 h a) = pullHO1 h'' a) ∧ (∀ a, pullHO2 h' (pullHO2 h a) = pullHO2 h'' a) ∧ (∀ a, GlobalTheory.CechDR.pullForm h' (GlobalTheory.CechDR.pullForm h a) = GlobalTheory.CechDR.pullForm h'' a) ∧ (∀ a, pullHH1 h' (pullHH1 h a) = pullHH1 h'' a) ∧ ∀ a, pullHH2 h' (pullHH2 h a) = pullHH2 h'' a) ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ), (∀ a b, pullHO2 h (cup _ a b) = cup _ (pullHO1 h a) (pullHO1 h b)) ∧ (∀ a b, pullHH2 h (cupHH s a b) = cupHH s' (pullHH1 h a) (pullHH1 h b)) ∧ ∀ a, toHO1 s' (pullHH1 h a) = pullHO1 h (toHO1 s a)) ∧ ∀ (R : Type) [CommRing R] (A : Over (Sp R)), (∀ a, pO1 (𝟙 A) a = a) ∧ (∀ a, structureSheafH2Pullback (𝟙 A) a = a) ∧ (∀ a, pF (𝟙 A) a = a) ∧ (∀ a, deRhamH1Pullback (𝟙 A) a = a) ∧ ∀ a, deRhamH2Pullback (𝟙 A) a = a := by
  refine ⟨?_, ?_, ?_⟩
  · intro R R' _ _ X X' s s' σ φ h R'' _ X'' s'' τ ψ h' ρ χ h'' hχ hρ
    subst hχ
    obtain rfl : ρ = τ.comp σ := RingHom.ext hρ
    exact ⟨pullHO1_comp h h' h'', pullHO2_comp h h' h'', pullForm_comp h h' h'', pullHH1_comp h h' h'',
      pullHH2_comp h h' h''⟩
  · intro R R' _ _ X X' s s' σ φ h
    exact ⟨pullHO2_cup h, pullHH2_cupHH h, toHO1_pullHH1 h⟩
  · intro R _ A
    exact ⟨pullHO1_id (ovw (𝟙 A)), pullHO2_id (ovw (𝟙 A)), pullForm_id (ovw (𝟙 A)),
      pullHH1_id (ovw (𝟙 A)), pullHH2_id (ovw (𝟙 A))⟩

end GlobalTheory.AbCoh
