import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenRestrictAffineOpenStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesKaehlerBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendLinearIndependentDifferentialsStatement
import GroundTheory.PAdicHodge.ACrisGalois
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LogPair.ChartPt

theorem cstOn_res {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) :
    cstOn f V = (resG X h).comp (cstOn f U) := by
  unfold cstOn resG
  rw [← CommRingCat.hom_comp, Category.assoc]
  congr 2
  exact (Scheme.Hom.appLE_map f _ _).symm

theorem smooth_cstOn {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) [Smooth f] {U : X.Opens}
    (hU : IsAffineOpen U) : (cstOn f U).Smooth := by
  have hs := HasRingHomProperty.appLE (P := @Smooth) f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  unfold cstOn
  exact (RingHom.Smooth.propertyIsLocal.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv _).2 hs

theorem isEtCoord_basicOpen {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {U : X.Opens}
    (hU : IsAffineOpen U) {d : ℕ} (t : Fin d → Γ(X, U)) (h : Γ(X, U))
    (H : letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra;
      (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away h))
        (fun a => algebraMap Γ(X, U) (Localization.Away h) (t a))).Etale) :
    IsEtCoord f (X.basicOpen h) (fun a => resG X (X.basicOpen_le h) (t a)) := by
  letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra
  letI : Algebra Γ(X, U) Γ(X, X.basicOpen h) := (resG X (X.basicOpen_le h)).toAlgebra
  have hl : IsLocalization.Away h Γ(X, X.basicOpen h) := hU.isLocalization_basicOpen h
  let φ := IsLocalization.algEquiv (Submonoid.powers h) (Localization.Away h) Γ(X, X.basicOpen h)
  have H' := RingHom.Etale.respectsIso.1 _ φ.toRingEquiv H
  unfold IsEtCoord
  convert H' using 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun a => ?_)
  · rw [cstOn_res f (X.basicOpen_le h)]
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
    rw [IsScalarTower.algebraMap_apply R Γ(X, U) (Localization.Away h), AlgEquiv.commutes]
    rfl
  · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
    rw [AlgEquiv.commutes]
    rfl

end GlobalTheory.LogPair.ChartPt

noncomputable section
namespace GlobalTheory.LogPair.ChartPt

theorem resG_comp {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG X h' (resG X h a) = resG X (h'.trans h) a := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem exists_chart : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Smooth f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (U : X.Opens) (c : ∀ i, (L i).ι) (hc : ∀ i, U ≤ (L i).U (c i)) (x : X) (K : Type) [Field K] [Algebra Γ(X, U) K], IsAffineOpen U → x ∈ U → (∀ a : Γ(X, U), algebraMap Γ(X, U) K a ≠ 0 ↔ x ∈ X.basicOpen a) → (letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra; Module.finrank K (K ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]) = d ∧ LinearIndependent K (fun i : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0} => (1 : K) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) (resG X (hc i) ((σ i).f (c i))))) → ∃ C : SncChart f d L σ, x ∈ C.U := by
  intro R _ X f _ d s L σ U c hc x K _ _ hU hxU hK H
  classical
  letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra
  obtain ⟨hd, hli⟩ := H
  have : Algebra.Smooth R Γ(X, U) := smooth_cstOn f hU
  obtain ⟨t, e', het, htli⟩ := GlobalTheory.T.extend_linear_independent_differentials R Γ(X, U) K d
    {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0}
    (fun i => resG X (hc i.1) ((σ i.1).f (c i.1))) hd hli
  obtain ⟨h, hh, het2⟩ := GlobalTheory.T.etale_coordinates_kaehler_basis R Γ(X, U) K d t hd htli
  have hV := isEtCoord_basicOpen f hU t h het2
  let sf : Fin s → Γ(X, U) := fun i => resG X (hc i) ((σ i).f (c i))
  let q : Fin s → Γ(X, U) := fun j => if algebraMap Γ(X, U) K (sf j) = 0 then 1 else sf j
  let g : Γ(X, U) := h * ∏ j, q j
  have hgW : X.basicOpen g ≤ X.basicOpen h := by
    simp only [g, Scheme.basicOpen_mul]; exact inf_le_left
  have hgs : ∀ i, algebraMap Γ(X, U) K (sf i) ≠ 0 → X.basicOpen g ≤ X.basicOpen (sf i) := by
    intro i hi
    obtain ⟨k, hk⟩ : sf i ∣ g := by
      have hq : q i = sf i := if_neg hi
      exact dvd_mul_of_dvd_right (hq ▸ Finset.dvd_prod_of_mem q (Finset.mem_univ i)) h
    rw [hk, Scheme.basicOpen_mul]; exact inf_le_left
  have hxg : x ∈ X.basicOpen g := by
    rw [← hK]
    simp only [g, map_mul, map_prod]
    refine mul_ne_zero hh (Finset.prod_ne_zero_iff.2 fun j _ => ?_)
    simp only [q]; split_ifs with hj
    · simp
    · exact hj
  have hgU : X.basicOpen g ≤ U := X.basicOpen_le g
  have hEt := GlobalTheory.T.isEtaleCoordinatesOnOpen_restrict_affineOpen R X f (X.basicOpen h) (X.basicOpen g) hgW d _ (hU.basicOpen h) (hU.basicOpen g) hV
  have hunit : ∀ i, algebraMap Γ(X, U) K (sf i) ≠ 0 → IsUnit (resG X hgU (sf i)) := by
    intro i hi
    have h1 : IsUnit (resG X (X.basicOpen_le (sf i)) (sf i)) := X.toRingedSpace.isUnit_res_basicOpen (sf i)
    have h2 := h1.map (resG X (hgs i hi))
    rwa [resG_comp] at h2
  refine ⟨{
      U := X.basicOpen g
      affine := hU.basicOpen g
      t := fun a => resG X hgU (t a)
      etale := ?_
      c := c
      le := fun i => hgU.trans (hc i)
      e := fun i => if hi : algebraMap Γ(X, U) K (sf i) = 0 then some (e' ⟨i, hi⟩) else none
      inj := ?_
      u := fun i => if hi : algebraMap Γ(X, U) K (sf i) = 0 then 1 else (hunit i hi).unit
      eq := ?_ }, hxg⟩
  · convert hEt using 2 with a
    rw [resG_comp]
  · intro i j a hi hj
    split_ifs at hi hj with h1 h2
    have := e'.injective ((Option.some_injective _ hi).trans (Option.some_injective _ hj).symm)
    exact congrArg Subtype.val this
  · intro i
    by_cases hi : algebraMap Γ(X, U) K (sf i) = 0
    · rw [dif_pos hi, dif_pos hi]
      simp only [Units.val_one, one_mul, Option.elim_some]
      rw [het ⟨i, hi⟩, resG_comp]
    · rw [dif_neg hi, dif_neg hi]
      simp only [IsUnit.unit_spec, Option.elim_none, mul_one]
      rw [resG_comp]

end GlobalTheory.LogPair.ChartPt
