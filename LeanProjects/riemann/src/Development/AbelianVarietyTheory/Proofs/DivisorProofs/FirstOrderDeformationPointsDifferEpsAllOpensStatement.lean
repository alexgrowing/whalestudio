import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderDeformationPointsDifferEpsAllOpens
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstOrderDeformation_points_differ_eps_allOpens : ∀ {K : Type} [Field K] {A : Over (Sp K)} {A' : Over (Sp (DualNumber K))} {i : A.left ⟶ A'.left} (hi : i ≫ A'.hom = A.hom ≫ GlobalTheory.DeRham.epsRed K) {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} (hm' : IsPullback m' A'.hom h y1) (him : i ≫ m' = m) (U : X.affineOpens) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1) (Ω : Z.affineOpens) (hΩ : Ω.1 ≤ h ⁻¹ᵁ U.1) {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)) (S : Sp (DualNumber B) ⟶ A.left) (hS : S ≫ A.hom = spMap ((algebraMap B (DualNumber B)).comp (baseMap K B))) (hSx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S = x) (l₁ l₂ : Sp B ⟶ A'.left) (hl₁ : l₁ ≫ A'.hom = spMap (algebraMap (DualNumber K) B)) (hl₂ : l₂ ≫ A'.hom = spMap (algebraMap (DualNumber K) B)) (hΩ₁ : ⊤ ≤ (l₁ ≫ m') ⁻¹ᵁ Ω.1) (hΩ₂ : ⊤ ≤ (l₂ ≫ m') ⁻¹ᵁ Ω.1) (h₂ : ∀ f, ∃ c : B, valR (l₂ ≫ m') Ω.1 f = valR (x ≫ m) Ω.1 f + algebraMap (DualNumber K) B DualNumber.eps * c) (h₁₂ : ∀ f, valR (l₁ ≫ m') Ω.1 f - valR (l₂ ≫ m') Ω.1 f = algebraMap (DualNumber K) B DualNumber.eps * (valR (S ≫ m) Ω.1 f).snd) (O : A'.left.Opens) (hxO : ⊤ ≤ x ⁻¹ᵁ (i ⁻¹ᵁ O)) (f : Γ(A'.left, O)), valR l₁ O f - valR l₂ O f = algebraMap (DualNumber K) B DualNumber.eps * (valR S (i ⁻¹ᵁ O) ((i.app O).hom f)).snd := by
  first | exact @GlobalTheory.CechKS.valR_sub_eq_eps_mul_of_affine | exact GlobalTheory.CechKS.valR_sub_eq_eps_mul_of_affine | (intros; apply GlobalTheory.CechKS.valR_sub_eq_eps_mul_of_affine <;> assumption)
