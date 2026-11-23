import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledBackProjCoordinateRatioOverlapDiv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped GlobalTheory.ProjSpace
namespace GlobalTheory.PD.XCover.Integ
attribute [local instance] MvPolynomial.gradedAlgebra
variable {d : ℕ}

theorem ratioSec_eq_ratio (i j : Fin (d + 1)) : ratioSec d i j = GlobalTheory.ProjSpace.ratio ℂ d i j := by
  rw [ratioSec, GlobalTheory.ProjFrac.awayToSection_mk]
  exact GlobalTheory.ProjFrac.frac_eq (by ring)

theorem basicOpen_ratioSec (a i : Fin (d + 1)) :
    (PSpace ℂ d).basicOpen (ratioSec d a i) = chart d a ⊓ chart d i := by
  rw [ratioSec_eq_ratio]
  exact GlobalTheory.ProjSpace.basicOpen_ratioOn

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem basicOpen_prod (φ : Z ⟶ PSpace ℂ d) (a : Fin (d + 1)) (T : Finset (Fin (d + 1))) :
    Z.basicOpen (φ.app (chart d a) (∏ i ∈ T, ratioSec d a i)) =
      φ ⁻¹ᵁ chart d a ⊓ T.inf fun i => φ ⁻¹ᵁ chart d i := by
  rw [← Scheme.preimage_basicOpen]
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Scheme.basicOpen_of_isUnit _ isUnit_one, Finset.inf_empty, inf_top_eq]
  | insert j T hj ih =>
    rw [Finset.prod_insert hj, Scheme.basicOpen_mul, Scheme.Hom.preimage_inf, ih, basicOpen_ratioSec,
      Scheme.Hom.preimage_inf, Finset.inf_insert, inf_inf_inf_comm, inf_idem]

theorem rat_eq (φ : Z ⟶ PSpace ℂ d) (a j : Fin (d + 1)) (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) :
    rat φ a j = Z.presheaf.germ (φ ⁻¹ᵁ chart d a) (genericPoint Z) ha (φ.app (chart d a) (ratioSec d a j)) := by
  rw [rat, dif_pos ha]

theorem germ_const (p : Z ⟶ Sp ℂ) [inst : Algebra ℂ Z.functionField] (hinst : inst = ffAlg p)
    (φ : Z ⟶ PSpace ℂ d) (hφ : φ ≫ PSpace.str ℂ d = p) (a : Fin (d + 1))
    (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) (c : ℂ) :
    Z.presheaf.germ (φ ⁻¹ᵁ chart d a) (genericPoint Z) ha (φ.app (chart d a) (algebraMap ℂ Γ(PSpace ℂ d, chart d a) c)) =
      algebraMap ℂ Z.functionField c := by
  subst hinst hφ
  rw [GlobalTheory.ProjSpace.algebraMap_sections_eq]
  simp only [Scheme.Hom.appLE, ffAlg, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp, RingHom.comp_apply,
    Scheme.Hom.comp_appTop]
  generalize (CommRingCat.Hom.hom (Scheme.Hom.app (PSpace.str ℂ d) ⊤))
    ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv) c) = w
  have e := ConcreteCategory.congr_hom (φ.naturality (homOfLE (le_top : chart d a ≤ ⊤)).op) w
  simp only [ConcreteCategory.comp_apply] at e
  erw [e, TopCat.Presheaf.germ_res_apply]
  rfl

theorem germ_mem_adjoin (p : Z ⟶ Sp ℂ) [inst : Algebra ℂ Z.functionField] (hinst : inst = ffAlg p)
    (φ : Z ⟶ PSpace ℂ d) (hφ : φ ≫ PSpace.str ℂ d = p) (a : Fin (d + 1))
    (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) (t : Γ(PSpace ℂ d, chart d a)) :
    Z.presheaf.germ (φ ⁻¹ᵁ chart d a) (genericPoint Z) ha (φ.app (chart d a) t) ∈
      Algebra.adjoin ℂ (Set.range (rat φ a)) := by
  obtain ⟨q, rfl⟩ := GlobalTheory.ProjSpace.aeval_ratio_surjective ℂ d a t
  induction q using MvPolynomial.induction_on with
  | C c => rw [aeval_C, germ_const p hinst φ hφ a ha c]; exact Subalgebra.algebraMap_mem _ c
  | add q r hq hr => rw [map_add, map_add, map_add]; exact add_mem hq hr
  | mul_X q j hq =>
    rw [map_mul, map_mul, map_mul, aeval_X, ← ratioSec_eq_ratio, ← rat_eq φ a j ha]
    exact mul_mem hq (Algebra.subset_adjoin ⟨j, rfl⟩)

theorem rat_eq_crd [Algebra ℂ Z.functionField] (φ : Z ⟶ PSpace ℂ d) (a j : Fin (d + 1))
    (h0 : genericPoint Z ∈ φ ⁻¹ᵁ chart d 0) (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) :
    rat φ a j = algebraMap (fld φ) Z.functionField (crd φ j / crd φ a) := by
  rw [map_div₀]
  exact (rat_overlap d Z φ 0 a j h0 ha).2

end GlobalTheory.PD.XCover.Integ

open GlobalTheory.PD.XCover.Integ in

theorem GlobalTheory.PD.XCover.germ_mem_rB : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i)), (Z.presheaf.germ _ (genericPoint Z) h).hom f ∈ rB ℂ Z.functionField (crd φ) I := by
  intro d Z _ p _ inst hinst φ _ hφ hgen I hI h f
  obtain ⟨a, ha⟩ := hI
  have hV : IsAffineOpen (chart d a) := GlobalTheory.ProjSpace.isAffineOpen_chart ℂ d a
  have hU : IsAffineOpen (φ ⁻¹ᵁ chart d a) := hV.preimage φ
  have hsub : Algebra.adjoin ℂ (Set.range (rat φ a)) ≤
      (rA ℂ (crd φ) I).map (IsScalarTower.toAlgHom ℂ (fld φ) Z.functionField) := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact ⟨crd φ j / crd φ a, Algebra.subset_adjoin ⟨a, ha, j, rfl⟩, (rat_eq_crd φ a j (hgen 0) (hgen a)).symm⟩
  have hint : ∀ y : Γ(Z, φ ⁻¹ᵁ chart d a),
      IsIntegral (rA ℂ (crd φ) I) ((Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom y) := by
    intro y
    obtain ⟨P, hPm, hP⟩ := IsIntegralHom.isIntegral_app φ _ hV y
    set G := (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom
    have hlift : P.map (G.comp (φ.app (chart d a)).hom) ∈
        Polynomial.lifts (algebraMap (rA ℂ (crd φ) I) Z.functionField) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨x, hx, hxy⟩ := hsub (germ_mem_adjoin p hinst φ hφ a (hgen a) (P.coeff n))
      exact ⟨⟨x, hx⟩, hxy⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hPm.map _)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, Polynomial.eval_map, ← Polynomial.hom_eval₂, hP, map_zero]
  set s := φ.app (chart d a) (∏ i ∈ I, ratioSec d a i) with hs
  have hbo : Z.basicOpen s = I.inf fun i => φ ⁻¹ᵁ chart d i := by
    rw [hs, basicOpen_prod]
    exact inf_eq_right.2 (Finset.inf_le (f := fun i => φ ⁻¹ᵁ chart d i) ha)
  have hgs : (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom s = ∏ i ∈ I, rat φ a i := by
    rw [hs, map_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => (rat_eq φ a i (hgen a)).symm
  have hinv : (∏ i ∈ I, rat φ a i)⁻¹ = algebraMap (fld φ) Z.functionField (∏ i ∈ I, crd φ a / crd φ i) := by
    rw [map_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [rat_eq_crd φ a i (hgen 0) (hgen a), ← map_inv₀, inv_div]
  have hne : (∏ i ∈ I, rat φ a i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => (rat_overlap d Z φ a i i (hgen a) (hgen i)).1
  suffices H : ∀ (W : Z.Opens) (hW : W = Z.basicOpen s) (h : genericPoint Z ∈ W) (f : Γ(Z, W)),
      (Z.presheaf.germ _ (genericPoint Z) h).hom f ∈ rB ℂ Z.functionField (crd φ) I from H _ hbo.symm h f
  rintro W rfl h f
  haveI := hU.isLocalization_basicOpen s
  obtain ⟨⟨y, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers s) f
  dsimp only at e
  have hres : ∀ z : Γ(Z, φ ⁻¹ᵁ chart d a), (Z.presheaf.germ _ (genericPoint Z) h).hom
      (algebraMap Γ(Z, φ ⁻¹ᵁ chart d a) Γ(Z, Z.basicOpen s) z) = (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom z :=
    fun z => Z.presheaf.germ_res_apply (homOfLE (Z.basicOpen_le s)) _ h z
  have e' := congrArg (Z.presheaf.germ _ (genericPoint Z) h).hom e
  rw [map_mul, hres, hres, map_pow, hgs] at e'
  have hf : (Z.presheaf.germ _ (genericPoint Z) h).hom f =
      (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom y * ((∏ i ∈ I, rat φ a i)⁻¹) ^ n := by
    rw [inv_pow, ← e', mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hne), mul_one]
  have hr : (∏ i ∈ I, crd φ a / crd φ i) ∈ rA ℂ (crd φ) I :=
    prod_mem fun i hi => Algebra.subset_adjoin ⟨i, hi, a, rfl⟩
  have hA : IsIntegral (rA ℂ (crd φ) I)
      (algebraMap (fld φ) Z.functionField (∏ i ∈ I, crd φ a / crd φ i)) :=
    isIntegral_algebraMap (R := rA ℂ (crd φ) I) (A := Z.functionField) (x := ⟨_, hr⟩)
  rw [hf, hinv]
  exact (Subalgebra.mem_restrictScalars ℂ).2 ((hint y).mul (hA.pow n))
