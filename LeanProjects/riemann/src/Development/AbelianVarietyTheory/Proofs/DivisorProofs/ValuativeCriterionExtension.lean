import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls.ExtLoc

theorem exists_stalk_hom_of_closedPoint (Y : Scheme.{0}) (y : Y) (W : Type) [CommRing W] [IsLocalRing W]
    (q : Sp W ⟶ Y) (hy : q (IsLocalRing.closedPoint W) = y) :
    ∃ φ : Y.presheaf.stalk y ⟶ CommRingCat.of W, Spec.map φ ≫ Y.fromSpecStalk y = q := by
  subst hy
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of W) q⟩

theorem mem_range_of_forall_dominating (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (s : K)
    (h : ∀ V : ValuationSubring K, LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring → s ∈ V) :
    s ∈ (algebraMap R K).range := by
  haveI : IsIntegrallyClosedIn (LocalSubring.range (algebraMap R K)).toSubring K := by
    rw [Subring.isIntegrallyClosedIn_iff]
    intro s hs
    set A := (LocalSubring.range (algebraMap R K)).toSubring
    letI : Algebra R A :=
      ((algebraMap R K).codRestrict A (fun y => show algebraMap R K y ∈ Set.range (algebraMap R K) from
        ⟨y, rfl⟩)).toAlgebra
    haveI : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.IsIntegral R A := by
      refine Algebra.IsIntegral.of_surjective (Algebra.ofId R A) ?_
      rintro ⟨_, y, rfl⟩
      exact ⟨y, rfl⟩
    have hs' : _root_.IsIntegral R s := isIntegral_trans s hs
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hs'
    simp only [A, LocalSubring.range_toSubring]
    exact ⟨y, hy⟩
  by_contra hs
  obtain ⟨V, hle, hsV⟩ :=
    LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (R := LocalSubring.range (algebraMap R K)) (x := s)
      (fun h' => hs (by rwa [LocalSubring.range_toSubring] at h'))
  exact hsV (h V hle)

theorem extends_of_forall_dominating : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (Y : Scheme.{0}) (p : Sp K ⟶ Y) (y : Y), (∀ (V : ValuationSubring K) (ρ : R →+* V), IsLocalHom ρ → V.subtype.comp ρ = algebraMap R K → ∃ q : Sp V ⟶ Y, spMap V.subtype ≫ q = p ∧ q (IsLocalRing.closedPoint V) = y) → ∃ q : Sp R ⟶ Y, spMap (algebraMap R K) ≫ q = p := by
  intro R _ _ _ _ K _ _ _ Y p y h
  have key : ∀ V : ValuationSubring K, LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring →
      ∃ φ : Y.presheaf.stalk y ⟶ CommRingCat.of V,
        Spec.map (φ ≫ CommRingCat.ofHom V.subtype) ≫ Y.fromSpecStalk y = p := by
    intro V hV
    obtain ⟨h1, h2⟩ := (GlobalTheory.localSubring_range_le_valuationSubring_iff_isLocalHom _ V).1 hV
    obtain ⟨q, hq, hy⟩ := h V ((algebraMap R K).codRestrict V h1) h2 rfl
    obtain ⟨φ, hφ⟩ := exists_stalk_hom_of_closedPoint Y y V q hy
    refine ⟨φ, ?_⟩
    rw [Spec.map_comp, Category.assoc, hφ]
    exact hq
  obtain ⟨V₀, hV₀⟩ := (LocalSubring.range (algebraMap R K)).exists_le_valuationSubring
  obtain ⟨φ₀, hφ₀⟩ := key V₀ hV₀
  set θ : Y.presheaf.stalk y ⟶ CommRingCat.of K := φ₀ ≫ CommRingCat.ofHom V₀.subtype with hθ
  have hmem : ∀ s, θ.hom s ∈ (algebraMap R K).range := by
    intro s
    refine mem_range_of_forall_dominating R K _ fun V hV => ?_
    obtain ⟨φ, hφ⟩ := key V hV
    have e : θ = φ ≫ CommRingCat.ofHom V.subtype :=
      Spec.map_injective ((cancel_mono (Y.fromSpecStalk y)).1 (hφ₀.trans hφ.symm))
    rw [e]
    exact (φ.hom s).2
  let e : R ≃+* (algebraMap R K).range := RingEquiv.ofBijective (algebraMap R K).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective R K (congrArg Subtype.val hab),
      (algebraMap R K).rangeRestrict_surjective⟩
  let θ' : Y.presheaf.stalk y ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (e.symm.toRingHom.comp (θ.hom.codRestrict _ hmem))
  have hθ' : θ' ≫ CommRingCat.ofHom (algebraMap R K) = θ := by
    ext s
    exact congrArg Subtype.val (e.apply_symm_apply ⟨θ.hom s, hmem s⟩)
  refine ⟨Spec.map θ' ≫ Y.fromSpecStalk y, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, hθ']
  exact hφ₀

end GlobalTheory.FlagCls.ExtLoc
