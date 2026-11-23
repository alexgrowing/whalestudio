import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictPull1InjectiveOfSepGlue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Pull1RestrictSurjectiveOfComma
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatFamilyExtend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleOneFormsCoboundaryOfRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictGlob1Bijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullHyp1RestrictInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullHyp1RestrictSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepOfFactoringCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueCommaOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocOAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPowSmulEqZeroOfResBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoFormExistsPowSmulEqZeroOfIsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairBelowTwo

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CechDR

open CatCoh

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem pairRes_bijective (φ : X' ⟶ X) (s' : X' ⟶ Sp R') :
    Function.Bijective (pairRes φ s').pull1 ∧ Function.Bijective (pullGlob1 (pairRes φ s')) ∧
      Function.Bijective (pullHyp1 (pairRes φ s')) := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') (pairFst φ) H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) hcov hdir
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' (pairFst φ) hcov
  have b1 : Function.Bijective (pairRes φ s').pull1 :=
    ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg, _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩
  have bg := _root_.GlobalTheory.restrict_glob1_bijective _ _ hs1 hg1
  exact ⟨b1, bg, _root_.GlobalTheory.CechDR.pullHyp1_restrict_injective _ _ b1.1 (_root_.GlobalTheory.compat_family_extend _ _ hs hg) bg.1,
    _root_.GlobalTheory.CechDR.pullHyp1_restrict_surjective _ _ b1.2 (_root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict _ _ hs1 hg1) bg.2 hs2⟩

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)

theorem existsUnique_isPull1 (c : HH1 s) : ∃! c', IsPull1 h c c' := by
  obtain ⟨c', hc, hu⟩ := (pairRes_bijective φ s').2.2.existsUnique (pullHyp1 (pairPull h) c)
  exact ⟨c', hc.symm, fun y hy ↦ hu y hy.symm⟩

theorem existsUnique_isPullO (c : HO1 s) : ∃! c', IsPullO h c c' := by
  obtain ⟨c', hc, hu⟩ := (pairRes_bijective φ s').1.existsUnique ((pairPull h).pull1 c)
  exact ⟨c', hc.symm, fun y hy ↦ hu y hy.symm⟩

theorem existsUnique_isPullForm (ω : GlobForm s) : ∃! ω', IsPullForm h ω ω' := by
  obtain ⟨ω', hω, hu⟩ := (pairRes_bijective φ s').2.1.existsUnique (pullGlob1 (pairPull h) ω)
  exact ⟨ω', hω.symm, fun y hy ↦ hu y hy.symm⟩

def pairResEquiv1 (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : HH1 s' ≃ₗ[R'] Hyp1 (OPair φ s') :=
  LinearEquiv.ofBijective (pullHyp1 (pairRes φ s')) (pairRes_bijective φ s').2.2

def pairResEquivO (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : HO1 s' ≃ₗ[R'] CatCoh.H1 (OPair φ s') :=
  LinearEquiv.ofBijective (pairRes φ s').pull1 (pairRes_bijective φ s').1

def pairResEquivForm (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : GlobForm s' ≃ₗ[R'] Glob1 (OPair φ s') :=
  LinearEquiv.ofBijective (pullGlob1 (pairRes φ s')) (pairRes_bijective φ s').2.1

def pullHH1 : HH1 s →ₛₗ[σ] HH1 s' :=
  (pairResEquiv1 φ s').symm.toLinearMap.comp (pullHyp1 (pairPull h))

def pullHO1 : HO1 s →ₛₗ[σ] HO1 s' :=
  (pairResEquivO φ s').symm.toLinearMap.comp (pairPull h).pull1

def pullForm : GlobForm s →ₛₗ[σ] GlobForm s' :=
  (pairResEquivForm φ s').symm.toLinearMap.comp (pullGlob1 (pairPull h))

theorem isPull1_pullHH1 (c : HH1 s) : IsPull1 h c (pullHH1 h c) :=
  ((pairResEquiv1 φ s').apply_symm_apply _).symm

theorem isPullO_pullHO1 (c : HO1 s) : IsPullO h c (pullHO1 h c) :=
  ((pairResEquivO φ s').apply_symm_apply _).symm

theorem isPullForm_pullForm (ω : GlobForm s) : IsPullForm h ω (pullForm h ω) :=
  ((pairResEquivForm φ s').apply_symm_apply _).symm

theorem IsPull1.eq_pullHH1 {c : HH1 s} {c' : HH1 s'} (e : IsPull1 h c c') : c' = pullHH1 h c :=
  (existsUnique_isPull1 h c).unique e (isPull1_pullHH1 h c)

theorem IsPullO.eq_pullHO1 {c : HO1 s} {c' : HO1 s'} (e : IsPullO h c c') : c' = pullHO1 h c :=
  (existsUnique_isPullO h c).unique e (isPullO_pullHO1 h c)

theorem IsPullForm.eq_pullForm {ω : GlobForm s} {ω' : GlobForm s'} (e : IsPullForm h ω ω') :
    ω' = pullForm h ω :=
  (existsUnique_isPullForm h ω).unique e (isPullForm_pullForm h ω)

end GlobalTheory.CechDR
