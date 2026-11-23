import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClassMapCorrespondenceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeComponentsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentStarCompatibleOfLabellingAgreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTypeVectorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.GoodAll

theorem goodFTAll_of_local : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.RowTrue hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → LabTie D L → (∀ k, TameGen.DepthZeroCuspidal (D.host.g k)) → (∀ (I : Ident D) rc, IsRc hL T I rc → ∀ k v, TameGen.TameParam (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2)) → (∀ (I : Ident D) cp, IsComp I rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x) → GoodFTAll D := by
  intro hG hZ hL D T Rw rep L hRow hDep hLT hDZ hTP hVec σ
  obtain ⟨I⟩ := GlobalTheory.T.nonempty_typePlaceCompletionIdent D
  obtain ⟨rc, hrc, hcls⟩ := GlobalTheory.T.exists_class_map_correspondence hL D T I
  obtain ⟨cp, hcomp, hcp⟩ := GlobalTheory.T.exists_type_components hL D T I rc hrc Rw rep hRow hDep
  have hP : LabParam D L rc :=
    GlobalTheory.SerSys.Bridge.labParam_of D L rc hG (GlobalTheory.T.tame_support_compatible hZ hL D T I rc hrc) hDZ (hTP I rc hrc)
  have hSC := GlobalTheory.T.seriesIdempotentStarCompatible_of_labelling_agree hG D L hLT
  obtain ⟨V, _, _, ρ, W, x, hconj, hx0, hxW, hxe⟩ := hVec I cp hcomp σ
  exact GlobalTheory.T.conjugate_type_vector D Rw L rc cp hLT hP hcls hSC hcp V ρ W σ hconj x hx0 hxW hxe

end GlobalTheory.GoodAll
