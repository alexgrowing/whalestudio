import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveBis
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupTangentLiftStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieA
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieB

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieFin

noncomputable section

namespace PositivityTheory.HtPt.Htat

namespace Lie

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem loc_of_charts {R : Type} [CommRing R] (x : Sp R ⟶ S) {J : Type} [Finite J] (f : J → R)
    (hf : Ideal.span (Set.range f) = ⊤) (hch : ∀ i, LieChart G x (f i)) {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) (i : J) {F : Type} [AddCommGroup F] [Module R F] [Module (Localization.Away (f i)) F]
    [IsScalarTower R (Localization.Away (f i)) F] (y : Sp (Localization.Away (f i)) ⟶ S) (hy : y = ptAt x (f i))
    (Mi : LieModel G y F) (r : E →ₗ[R] F)
    (hr : ∀ e, (Mi.pt (r e)).left = spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ (M.pt e).left) :
    IsLocalizedModule (Submonoid.powers (f i)) r := by
  subst hy
  choose P iA iM iL ist ifin iproj m nat using hch
  have hix : ∀ g : Idx f, ∃ i, f i ∣ g.1 := fun g => g.2
  choose ix hix using hix
  have hqc : ∀ (g g' : Idx f) (h : g.1 ∣ g'.1) (t : R), g'.1 = g.1 * t →
      ∀ r : (P (ix g) →ₗ[R] Localization.Away g.1) →ₗ[R] (P (ix g') →ₗ[R] Localization.Away g'.1),
      (∀ y, ((m (ix g') _ (unit_of_dvd (hix g'))).pt (r y)).left =
        spMap (dualMap (cmap h).toRingHom) ≫ ((m (ix g) _ (unit_of_dvd (hix g))).pt y).left) →
      IsLocalizedModule (Submonoid.powers t) r := by
    intro g g' h t ht r hr
    have hu' : IsUnit (algebraMap R (Localization.Away g'.1) (f (ix g))) :=
      unit_of_dvd ((hix g).trans h)
    obtain ⟨e, he⟩ := exists_equiv (R := R) (ptAt x g'.1) (m (ix g) _ hu') (m (ix g') _ (unit_of_dvd (hix g')))
    haveI := cmap_loc h ht
    haveI hcr := GlobalTheory.T.localized_module_base_change R (P (ix g)) (Localization.Away g.1) (Localization.Away g'.1) (f (ix g)) t
      (unit_of_dvd (hix g)) (cmap h) (cmap_loc h ht)
    have hrr : r = (e : _ →ₗ[R] _) ∘ₗ LinearMap.compRight R (cmap h).toLinearMap := by
      refine LinearMap.ext fun y => pt_left_inj (m (ix g') _ (unit_of_dvd (hix g'))) ?_
      rw [hr]
      refine Eq.trans ?_ (he _).symm
      exact (nat (ix g) _ _ (unit_of_dvd (hix g)) hu' (cmap h) y).symm
    rw [hrr]
    exact IsLocalizedModule.of_linearEquiv _ _ _
  obtain ⟨ρ, hρ, hloc⟩ := loc_of_family x f hf M (fun g => P (ix g) →ₗ[R] Localization.Away g.1)
    (fun g => m (ix g) _ (unit_of_dvd (hix g))) hqc
  obtain ⟨e, he⟩ := exists_equiv (R := R) (ptAt x (f i))
    (m (ix ⟨f i, i, dvd_rfl⟩) _ (unit_of_dvd (hix ⟨f i, i, dvd_rfl⟩))) Mi
  have hrr : r = (e : _ →ₗ[R] _) ∘ₗ ρ ⟨f i, i, dvd_rfl⟩ :=
    LinearMap.ext fun y => pt_left_inj Mi ((hr y).trans ((he _).trans (hρ ⟨f i, i, dvd_rfl⟩ y)).symm)
  rw [hrr]
  haveI := hloc i
  exact IsLocalizedModule.of_linearEquiv _ _ _

variable (G) in

def SmChart {R : Type} [CommRing R] (x : Sp R ⟶ S) (f : R) : Prop :=
  ∃ (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (_ : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V),
    RingHom.Smooth (G.hom.appLE V U hUV).hom ∧ ∃ u : Γ(G.left, U) →+* Localization.Away f,
      (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec

theorem SmChart.lieChart {R : Type} [CommRing R] {x : Sp R ⟶ S} {f : R} (h : SmChart G x f) : LieChart G x f := by
  obtain ⟨U, V, hU, hV, hUV, hsm, u, hu⟩ := h
  exact lieChart_of_smooth_chart S G R x f U V hU hV hUV hsm u hu

theorem unit_away {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (f : R) :
    IsUnit (algebraMap R (Localization.Away (algebraMap R R' f)) f) := by
  rw [IsScalarTower.algebraMap_apply R R' (Localization.Away (algebraMap R R' f))]
  exact IsLocalization.Away.algebraMap_isUnit _

theorem pt_eq {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (g : R') :
    spMap (algebraMap R (Localization.Away g)) ≫ x = ptAt (spMap (algebraMap R R') ≫ x) g := by
  rw [ptAt, ← Category.assoc, spMap_comp', ← IsScalarTower.algebraMap_eq]

theorem SmChart.base {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {x : Sp R ⟶ S} {f : R}
    (h : SmChart G x f) : SmChart G (spMap (algebraMap R R') ≫ x) (algebraMap R R' f) := by
  obtain ⟨U, V, hU, hV, hUV, hsm, u, hu⟩ := h
  let κ : Localization.Away f →+* Localization.Away (algebraMap R R' f) :=
    IsLocalization.Away.lift f (unit_away (R' := R') f)
  have hκ : κ.comp (algebraMap R _) = algebraMap R _ := IsLocalization.Away.lift_comp f _
  refine ⟨U, V, hU, hV, hUV, hsm, κ.comp u, ?_⟩
  rw [ChartDer.one_left] at hu ⊢
  simp only [Over.mk_hom] at hu ⊢
  have e := pt_eq x (algebraMap R R' f)
  rw [← hκ, ← spMap_comp'] at e
  rw [← spMap_comp' u κ, Category.assoc (spMap κ), ← hu]
  refine (congrArg (· ≫ η[G].left) e.symm).trans ?_
  simp only [Category.assoc]

theorem exists_cover [Smooth G.hom] {R : Type} [CommRing R] (x : Sp R ⟶ S) :
    ∃ (J : Type) (_ : Finite J) (f : J → R), Ideal.span (Set.range f) = ⊤ ∧ ∀ i, SmChart G x (f i) := by
  have hspan : Ideal.span {f : R | SmChart G x f} = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨f, hf, h⟩ := GlobalTheory.T.smooth_group_tangent_lift S G R x p
    exact hf (hle (Ideal.subset_span h))
  obtain ⟨s, hs, hsp⟩ := (Ideal.span_eq_top_iff_finite _).mp hspan
  refine ⟨s, inferInstance, fun i => i, ?_, fun i => hs i.2⟩
  rw [Subtype.range_coe_subtype]
  exact hsp

theorem isBaseChange_lie [Smooth G.hom] {R : Type} [CommRing R] (x : Sp R ⟶ S) {L : Type} [AddCommGroup L]
    [Module R L] (M : LieModel G x L) (R' : Type) [CommRing R'] [Algebra R R'] (L' : Type) [AddCommGroup L']
    [Module R' L'] [Module R L'] [IsScalarTower R R' L'] (M' : LieModel G (spMap (algebraMap R R') ≫ x) L')
    (β : L →ₗ[R] L') (hβ : ∀ e, (M'.pt (β e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left) :
    IsBaseChange R' β := by
  obtain ⟨J, _, f, hf, hch⟩ := exists_cover (G := G) x
  have hf' : Ideal.span (Set.range fun i => algebraMap R R' (f i)) = ⊤ := by
    have := congrArg (Ideal.map (algebraMap R R')) hf
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  let φ : R' ⊗[R] L →ₗ[R'] L' := β.liftBaseChange R'
  have hφ : ∀ e, φ (1 ⊗ₜ e) = β e := fun e => by
    rw [LinearMap.liftBaseChange_tmul, one_smul]
  have hbij : Function.Bijective φ := by
    refine bijective_of_cover _ hf' φ fun i => ?_
    obtain ⟨P, _, _, _, _, _, _, m, nat⟩ := (hch i).lieChart
    let A := Localization.Away (f i)
    let C := Localization.Away (algebraMap R R' (f i))
    have hA : IsUnit (algebraMap R A (f i)) := IsLocalization.Away.algebraMap_isUnit _
    have hC : IsUnit (algebraMap R C (f i)) := unit_away (f i)
    let κ : A →+* C := IsLocalization.Away.lift (f i) hC
    have hκ : κ.comp (algebraMap R A) = algebraMap R C := IsLocalization.Away.lift_comp _ _
    letI : Algebra A C := κ.toAlgebra
    haveI : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' hκ.symm
    let c : A →ₐ[R] C := IsScalarTower.toAlgHom R A C
    obtain ⟨a, ha⟩ := exists_trL (R := R') (spMap (algebraMap R R') ≫ x) (spMap (algebraMap R C) ≫ x)
      (algebraMap R' C) (fun _ => rfl) (pt_eq x _).symm M' (m C hC)
    obtain ⟨ρ, hρ⟩ := exists_trL (R := R) x (spMap (algebraMap R A) ≫ x) (algebraMap R A) (fun _ => rfl) rfl M
      (m A hA)
    have l1 : IsLocalizedModule (Submonoid.powers (algebraMap R R' (f i))) a :=
      loc_of_charts (spMap (algebraMap R R') ≫ x) (fun i => algebraMap R R' (f i)) hf'
        (fun i => (hch i).base.lieChart) M' i _ (pt_eq x _) (m C hC) a ha
    have l2 : IsLocalizedModule (Submonoid.powers (f i)) ρ :=
      loc_of_charts x f hf (fun i => (hch i).lieChart) M i _ rfl (m A hA) ρ hρ
    have b2 : IsBaseChange A ρ := (isLocalizedModule_iff_isBaseChange (Submonoid.powers (f i)) A ρ).1 l2
    let g : (P →ₗ[R] A) →ₗ[A] (P →ₗ[R] C) :=
      { toFun := fun w => c.toLinearMap ∘ₗ w
        map_add' := fun w w' => LinearMap.comp_add _ _ _
        map_smul' := fun r w => LinearMap.ext fun p => by
          show κ (r * w p) = r • κ (w p)
          rw [map_mul, Algebra.smul_def]
          rfl }
    have b3 : IsBaseChange C g := isBaseChange_hom
      (fun w r p => GlobalTheory.CompanionTheory.LocHom.map_away_smul (AlgHom.id R A) w r p)
      (fun w r p => GlobalTheory.CompanionTheory.LocHom.map_away_smul c w r p) g fun _ _ => rfl
    have b4 := b2.comp b3
    have e : (g.restrictScalars R) ∘ₗ ρ = ((a ∘ₗ φ).restrictScalars R) ∘ₗ (TensorProduct.mk R R' L 1) := by
      refine LinearMap.ext fun l => pt_left_inj (m C hC) ?_
      show ((m C hC).pt (c.toLinearMap ∘ₗ ρ l)).left = ((m C hC).pt (a (φ (1 ⊗ₜ l)))).left
      rw [nat A C hA hC c, hρ, ha, hφ, hβ, ← Category.assoc, ← Category.assoc, spMap_dual_comp, spMap_dual_comp,
        ← IsScalarTower.algebraMap_eq, ← hκ]
      rfl
    rw [e] at b4
    have b5 : IsBaseChange C (a ∘ₗ φ) := (TensorProduct.isBaseChange R L R').of_comp b4
    exact ⟨P →ₗ[R] C, inferInstance, inferInstance, a, l1,
      (isLocalizedModule_iff_isBaseChange (Submonoid.powers (algebraMap R R' (f i))) C _).2 b5⟩
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective φ hbij) hφ

end Lie

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct in
open GlobalTheory.CompanionTheory.Ar in
theorem lie_proj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), Module.Finite R L ∧ Module.Projective R L ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (L' : Type) [AddCommGroup L'] [Module R' L'] [Module R L'] [IsScalarTower R R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →ₗ[R] L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → IsBaseChange R' β := by
  intro S G _ _ R _ x L _ _ M
  obtain ⟨J, _, f, hf, hch⟩ := Lie.exists_cover (G := G) x
  obtain ⟨h1, h2⟩ := lieModel_finite_projective S G R x J f hf (fun i => (hch i).lieChart) L M
  exact ⟨h1, h2, fun R' _ _ L' _ _ _ _ M' β hβ => Lie.isBaseChange_lie x M R' L' M' β hβ⟩

end PositivityTheory.HtPt.Htat
