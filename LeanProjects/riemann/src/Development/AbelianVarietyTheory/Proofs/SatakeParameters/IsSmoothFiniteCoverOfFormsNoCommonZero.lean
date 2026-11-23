import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicIndependentPulledBackProjCoordinateRatiStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledBackProjCoordinateRatioOverlapDivStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ProjectiveChartAffineCover
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermChartInterIntegralCoordinateRatiosStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionFieldIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteProjectionFunctionField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AffineGermSubalgebraSmooth

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

variable {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace ℂ N)

theorem resG_fRatio {n : ℕ} {a g : MvPolynomial (Fin (N + 1)) ℂ} (ha : a ∈ grading ℂ N n) (hg : g ∈ grading ℂ N n)
    {W : X.Opens} (hW : W ≤ fOpen ι g) {V : (PSpace ℂ N).Opens} (hV : V ≤ Proj.basicOpen (grading ℂ N) g)
    (hWV : W ≤ ι ⁻¹ᵁ V) :
    resG X hW (fRatio ι a g ha hg) = (ι.appLE V W hWV).hom (frac (grading ℂ N) V a g ha hg hV) := by
  have e : fRatio ι a g ha hg = (ι.appLE (Proj.basicOpen (grading ℂ N) g) (fOpen ι g) le_rfl).hom
      (frac (grading ℂ N) _ a g ha hg le_rfl) := by
    unfold fRatio; rw [Scheme.Hom.app_eq_appLE]; rfl
  rw [e]
  exact (resG_appLE ι _ hW _).trans (appLE_resG ι hV hWV _).symm

theorem basicOpen_fRatio_le {n : ℕ} {a g : MvPolynomial (Fin (N + 1)) ℂ} (ha : a ∈ grading ℂ N n)
    (hg : g ∈ grading ℂ N n) : X.basicOpen (fRatio ι a g ha hg) ≤ fOpen ι a := by
  have e : X.basicOpen (fRatio ι a g ha hg) =
      ι ⁻¹ᵁ (PSpace ℂ N).basicOpen (frac (grading ℂ N) _ a g ha hg le_rfl) :=
    (Scheme.preimage_basicOpen ι _).symm
  rw [e, basicOpen_frac]
  exact ι.preimage_mono inf_le_right

variable {d n : ℕ} (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ) (hf : ∀ i, f i ∈ grading ℂ N n)

theorem isCoordFamily_fRatio (hcov : ⨆ i, fOpen ι (f i) = ⊤) :
    IsCoordFamily (fun i => fOpen ι (f i)) (fun i j => fRatio ι (f j) (f i) (hf j) (hf i)) where
  cover := hcov
  self i := fRatio_self ι (f i) (hf i)
  mul i j k := by
    have hWV : fOpen ι (f i) ⊓ fOpen ι (f j) ≤
        ι ⁻¹ᵁ (Proj.basicOpen (grading ℂ N) (f i) ⊓ Proj.basicOpen (grading ℂ N) (f j)) :=
      fun x hx => ⟨hx.1, hx.2⟩
    rw [resG_fRatio ι (hf j) (hf i) _ inf_le_left hWV, resG_fRatio ι (hf k) (hf j) _ inf_le_right hWV,
      resG_fRatio ι (hf k) (hf i) _ inf_le_left hWV, ← map_mul]
    exact congrArg _ (frac_mul_eq (by ring))
  basicOpen_le i j := basicOpen_fRatio_le ι (hf j) (hf i)

def formMap (p : X ⟶ Sp ℂ) (hcov : ⨆ i, fOpen ι (f i) = ⊤) : X ⟶ PSpace ℂ d :=
  (isCoordFamily_fRatio ι f hf hcov).toHom p

variable (p : X ⟶ Sp ℂ) (hcov : ⨆ i, fOpen ι (f i) = ⊤)

theorem formMap_preimage (i : Fin (d + 1)) : formMap ι f hf p hcov ⁻¹ᵁ chart ℂ d i = fOpen ι (f i) :=
  (isCoordFamily_fRatio ι f hf hcov).toHom_preimage p i

theorem formMap_str : formMap ι f hf p hcov ≫ PSpace.str ℂ d = p :=
  (isCoordFamily_fRatio ι f hf hcov).toHom_str p

theorem pullRatio_formMap (i j : Fin (d + 1)) :
    pullRatio (formMap ι f hf p hcov) (fOpen ι (f i)) i (formMap_preimage ι f hf p hcov i).ge j =
      fRatio ι (f j) (f i) (hf j) (hf i) :=
  (isCoordFamily_fRatio ι f hf hcov).pullRatio_toHom p i j

theorem isAffineOpen_fOpen [IsClosedImmersion ι] {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N n)
    (hn : 0 < n) : IsAffineOpen (fOpen ι g) :=
  (Proj.isAffineOpen_basicOpen (grading ℂ N) g hg hn).preimage ι

theorem isFinite_formMap [IsClosedImmersion ι] (hp : ι ≫ PSpace.str ℂ N = p) (hn : 0 < n) :
    IsFinite (formMap ι f hf p hcov) := by
  haveI := isProper_str ℂ N
  haveI := isProper_str ℂ d
  have h1 : IsProper (formMap ι f hf p hcov ≫ PSpace.str ℂ d) := by
    rw [formMap_str, ← hp]; infer_instance
  exact IsFinite.iff_isProper_and_isAffineHom.2 ⟨IsProper.of_comp _ (PSpace.str ℂ d),
    isAffineHom_of_isAffineOpen_preimage_chart _ fun i => by
      rw [formMap_preimage]; exact isAffineOpen_fOpen ι (hf i) hn⟩

theorem germ_appLE {Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens) (W : X.Opens) (h : W ≤ φ ⁻¹ᵁ U) (x : X) (hx : x ∈ W)
    (s : Γ(Y, U)) : (X.presheaf.germ W x hx).hom ((φ.appLE U W h).hom s) =
      (X.presheaf.germ (φ ⁻¹ᵁ U) x (h hx)).hom ((φ.app U).hom s) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

theorem ratioSec_eq (i j : Fin (d + 1)) : XCover.ratioSec d i j = ratio ℂ d i j :=
  (awayToSection_mk _ 1 _).trans (frac_eq (by ring))

theorem rat_formMap [IsIntegral X] (j : Fin (d + 1)) (hg : genericPoint X ∈ fOpen ι (f 0)) :
    XCover.rat (formMap ι f hf p hcov) 0 j =
      (X.presheaf.germ (fOpen ι (f 0)) (genericPoint X) hg).hom (fRatio ι (f j) (f 0) (hf j) (hf 0)) := by
  have hmem : genericPoint X ∈ formMap ι f hf p hcov ⁻¹ᵁ XCover.chart d 0 :=
    (formMap_preimage ι f hf p hcov 0).ge hg
  rw [XCover.rat, dif_pos hmem, ← pullRatio_formMap ι f hf p hcov 0 j, pullRatio, germ_appLE, ratioSec_eq]

open XCover in

theorem exists_finCover_of_isFinite {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    [inst : Algebra ℂ X.functionField] (hinst : inst = ffAlg p) (φ : X ⟶ PSpace ℂ d) [IsFinite φ]
    (hφ : φ ≫ PSpace.str ℂ d = p) (hgen : ∀ i, genericPoint X ∈ φ ⁻¹ᵁ XCover.chart d i) :
    IsFinCover ℂ X.functionField (crd φ) ∧ IsAffCover p (fun i => φ ⁻¹ᵁ XCover.chart d i) (rB ℂ X.functionField (crd φ)) := by
  have hrat := GlobalTheory.T.pulledBackProjCoordinateRatio_overlap_div d X φ
  have h00 : rat φ 0 0 = 1 := by
    obtain ⟨h1, h2⟩ := hrat 0 0 0 (hgen 0) (hgen 0)
    rw [div_self h1] at h2
    exact h2
  have hch := GlobalTheory.T.projective_chart_affine_cover d X φ
  have hne : ∀ I : Finset (Fin (d + 1)), genericPoint X ∈ I.inf fun i => φ ⁻¹ᵁ XCover.chart d i := by
    intro I
    induction I using Finset.induction_on with
    | empty => simp
    | insert a s _ ih => rw [Finset.inf_insert]; exact ⟨hgen a, ih⟩
  have hring : ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ y, y ∈ rB ℂ X.functionField (crd φ) I ↔
      ∃ f : Γ(X, I.inf fun i => φ ⁻¹ᵁ XCover.chart d i), (X.presheaf.germ _ (genericPoint X) (hne I)).hom f = y := by
    intro I hI y
    constructor
    · exact GlobalTheory.T.chart_function_field_integral d X p hinst φ hφ hgen I hI (hne I) y
    · rintro ⟨f, rfl⟩
      exact GlobalTheory.T.genericGerm_chartInter_integral_coordinateRatios d X p hinst φ hφ hgen I hI (hne I) f
  have h1 : crd φ 0 = 1 := Subtype.ext h00
  haveI : CharZero (fld φ) := charZero_of_injective_algebraMap (algebraMap ℂ (fld φ)).injective
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  refine ⟨IsFinCover.of_charZero ⟨?_, ?_, ?_⟩ (GlobalTheory.T.finite_projection_function_field d X p hinst φ hφ hgen) ?_,
    ⟨?_, fun I hI => hch.2 I hI, hch.1, hne, hring⟩⟩
  · intro i h
    exact (hrat 0 i i (hgen 0) (hgen i)).1 (by simpa [crd_val] using congrArg (fun z : fld φ => (z : X.functionField)) h)
  · simp only [h1, div_one]
    exact AlgebraicIndependent.of_comp (fld φ).val (GlobalTheory.T.algebraicIndependent_pulledBackProjCoordinateRatios d X p hinst φ hφ hgen)
  · simp only [h1, div_one]
    rw [eq_top_iff]
    intro z _
    have hle : fld φ ≤ (IntermediateField.adjoin ℂ (Set.range fun j : Fin d => crd φ j.succ)).map (fld φ).val := by
      show IntermediateField.adjoin ℂ _ ≤ _
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨j, rfl⟩
      induction j using Fin.cases with
      | zero => rw [h00]; exact one_mem _
      | succ k => exact (IntermediateField.mem_map _).2 ⟨crd φ k.succ, IntermediateField.subset_adjoin ℂ _ ⟨k, rfl⟩, rfl⟩
    obtain ⟨w, hw, hwz⟩ := (IntermediateField.mem_map _).1 (hle z.2)
    have : w = z := Subtype.ext hwz
    rwa [← this]
  · intro i
    exact GlobalTheory.T.affine_germ_subalgebra_smooth X p hinst _ (hch.2 {i} (Finset.singleton_nonempty i)) (hne {i}) _
      (hring {i} (Finset.singleton_nonempty i))
  · subst hinst
    rfl

theorem isFinCover_of_forms : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    [inst : Algebra ℂ X.functionField], inst = ffAlg p → ∀ (N : ℕ) (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι →
    ι ≫ PSpace.str ℂ N = p → ∀ (n : ℕ) (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ)
    (hf : ∀ i, f i ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n → (⨆ i, GlobalTheory.EtProj.fOpen ι (f i) = ⊤) →
    ∀ hg : (∀ i, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (f i)), ∃ (F : IntermediateField ℂ X.functionField)
    (x : Fin (d + 1) → F), IsFinCover ℂ X.functionField x ∧
    IsAffCover p (fun i => GlobalTheory.EtProj.fOpen ι (f i)) (rB ℂ X.functionField x) ∧
    ∀ j, algebraMap F X.functionField (x j) = (X.presheaf.germ (GlobalTheory.EtProj.fOpen ι (f 0)) (genericPoint X) (hg 0)).hom
      (GlobalTheory.EtProj.fRatio ι (f j) (f 0) (hf j) (hf 0)) := by
  intro X _ p d _ inst hinst N ι hι hp n f hf hn hcov hg
  haveI : IsFinite (formMap ι f hf p hcov) := isFinite_formMap ι f hf p hcov hp hn
  have hpre := formMap_preimage ι f hf p hcov
  obtain ⟨h1, h2⟩ := exists_finCover_of_isFinite p d hinst (formMap ι f hf p hcov) (formMap_str ι f hf p hcov)
    fun i => (hpre i).ge (hg i)
  have hU : (fun i => formMap ι f hf p hcov ⁻¹ᵁ XCover.chart d i) = fun i => fOpen ι (f i) := funext hpre
  rw [hU] at h2
  exact ⟨_, _, h1, h2, fun j => rat_formMap ι f hf p hcov j (hg 0)⟩

end GlobalTheory.EtProj
