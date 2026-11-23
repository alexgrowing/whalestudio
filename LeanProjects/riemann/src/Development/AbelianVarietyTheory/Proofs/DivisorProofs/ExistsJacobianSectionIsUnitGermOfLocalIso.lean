import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace MorJac

open TopForm

section Ring

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] {α : k →+* A} {β : k →+* B}
  {D : ℕ}

theorem isFreeGen_formMap {ρ : A →+* B} (hρ : letI := ρ.toAlgebra; Algebra.FormallyEtale A B)
    (h : ρ.comp α = β) {ω : Forms α D} (hω : IsFreeGen A ω) :
    IsFreeGen B (TopForm.formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)

theorem formallyEtale_of_bijective {ρ : A →+* B} (hρ : Function.Bijective ρ) :
    letI := ρ.toAlgebra; Algebra.FormallyEtale A B := by
  letI := ρ.toAlgebra
  exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId A B) hρ)

end Ring

theorem formallyEtale_germ {Y : Scheme.{0}} {T : Y.Opens} (hT : IsAffineOpen T) (y : Y)
    (hy : y ∈ T) : letI := (Y.presheaf.germ T y hy).hom.toAlgebra;
      Algebra.FormallyEtale Γ(Y, T) (Y.presheaf.stalk y) := by
  letI := (Y.presheaf.germ T y hy).hom.toAlgebra
  haveI := hT.isLocalization_stalk ⟨y, hy⟩
  exact Algebra.FormallyEtale.of_isLocalization (hT.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl

end MorJac

end GlobalTheory

namespace GlobalTheory

namespace MorJac

open TopForm

variable {k : Type} [CommRing k] {Y X : Scheme.{0}} {p : Y ⟶ Sp k} {σ : X ⟶ Y} {D : ℕ}
  [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D (σ ≫ p)]

variable (p σ) in

theorem comp_eq : σ ≫ p = (σ ≫ p) ≫ spMap (RingHom.id k) := by
  rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]

variable (K : CanonLB p D) (K' : CanonLB (σ ≫ p) D)

theorem coeff_pullForm_eq_mul (i : K.bundle.ι) (j : K'.bundle.ι) {V : Y.Opens}
    (hV : V ≤ K.bundle.U i) {W : X.Opens} (hW : W ≤ K'.bundle.U j) (h : W ≤ σ ⁻¹ᵁ V)
    (η : FormsOn p D V) :
    K'.coeff j hW (pullForm (comp_eq p σ) h η) =
      (σ.appLE V W h).hom (K.coeff i hV η) *
        K'.coeff j hW (pullForm (comp_eq p σ) (h.trans (σ.preimage_mono hV)) (K.om i)) := by
  refine GlobalTheory.LB.fun_ext_of_cover (fun T : {T : Y.Opens // IsAffineOpen T ∧ T ≤ V} =>
    W ⊓ σ ⁻¹ᵁ T.1) (fun _ => inf_le_left) (fun x hx => ?_) fun T => ?_
  · obtain ⟨T, hT⟩ := Opens.mem_iSup.1 (le_iSup_affine V (h hx))
    exact Opens.mem_iSup.2 ⟨T, hx, hT⟩
  · have h₀ : resForm T.2.2 η = resG Y T.2.2 (K.coeff i hV η) • resForm (T.2.2.trans hV) (K.om i) :=
      (K.isFrame i).resForm_eq_coeff_smul hV η T.2.1 T.2.2
    have h₁ := congrArg (pullForm (comp_eq p σ) (inf_le_right : W ⊓ σ ⁻¹ᵁ T.1 ≤ _)) h₀
    rw [map_smulₛₗ, pullForm_resForm, pullForm_resForm, GlobalTheory.LB.appLE_resG] at h₁
    rw [map_mul, K'.resG_coeff, K'.resG_coeff, resForm_pullForm, resForm_pullForm, h₁, map_smul,
      smul_eq_mul, GlobalTheory.LB.resG_appLE]

def jacLoc (a : (LB.div K'.bundle (K.bundle.pull σ)).ι) :
    Γ(X, (LB.div K'.bundle (K.bundle.pull σ)).U a) :=
  K'.coeff a.1 inf_le_left
    (pullForm (comp_eq p σ) (inf_le_right.trans (GlobalTheory.LB.pull_U_le σ a.2)) (K.om (a.2 PUnit.unit)))

theorem resG_jacLoc (a : (LB.div K'.bundle (K.bundle.pull σ)).ι) {W : X.Opens}
    (e : W ≤ (LB.div K'.bundle (K.bundle.pull σ)).U a) :
    resG X e (jacLoc K K' a) = K'.coeff a.1 (e.trans inf_le_left)
      (pullForm (comp_eq p σ) ((e.trans inf_le_right).trans (GlobalTheory.LB.pull_U_le σ a.2))
        (K.om (a.2 PUnit.unit))) := by
  exact (K'.resG_coeff a.1 _ e _).trans (congrArg _ (resForm_pullForm _ _ _ _))

end MorJac

end GlobalTheory

namespace GlobalTheory

namespace MorJac

open TopForm

variable {k : Type} [CommRing k] {Y X : Scheme.{0}} {p : Y ⟶ Sp k} {σ : X ⟶ Y} {D : ℕ}
  [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D (σ ≫ p)]
  (K : CanonLB p D) (K' : CanonLB (σ ≫ p) D)

theorem ger_jacLoc (y : X) (t t' : (LB.div K'.bundle (K.bundle.pull σ)).ι)
    (h : y ∈ (LB.div K'.bundle (K.bundle.pull σ)).U t)
    (h' : y ∈ (LB.div K'.bundle (K.bundle.pull σ)).U t') :
    ger y h (jacLoc K K' t) =
      tr (LB.div K'.bundle (K.bundle.pull σ)) y t t' * ger y h' (jacLoc K K' t') := by
  have hl : (LB.div K'.bundle (K.bundle.pull σ)).U t ⊓ (LB.div K'.bundle (K.bundle.pull σ)).U t' ≤
      (LB.div K'.bundle (K.bundle.pull σ)).U t := inf_le_left
  have hr : (LB.div K'.bundle (K.bundle.pull σ)).U t ⊓ (LB.div K'.bundle (K.bundle.pull σ)).U t' ≤
      (LB.div K'.bundle (K.bundle.pull σ)).U t' := inf_le_right
  have hy : y ∈ (LB.div K'.bundle (K.bundle.pull σ)).U t ⊓ (LB.div K'.bundle (K.bundle.pull σ)).U t' :=
    ⟨h, h'⟩
  rw [← ger_resG hl y hy, ← ger_resG hr y hy, resG_jacLoc, resG_jacLoc]
  have hWi := (hl.trans inf_le_right).trans (GlobalTheory.LB.pull_U_le σ t.2)
  have hWi' := (hr.trans inf_le_right).trans (GlobalTheory.LB.pull_U_le σ t'.2)
  have hV := le_inf hWi hWi'
  have e1 := K'.coeff_change t.1 t'.1 (hl.trans inf_le_left) (hr.trans inf_le_left)
    (pullForm (comp_eq p σ) hWi (K.om (t.2 PUnit.unit)))
  have e2 : pullForm (comp_eq p σ) hWi' (K.om (t'.2 PUnit.unit)) =
      pullForm (comp_eq p σ) hV (resForm inf_le_right (K.om (t'.2 PUnit.unit))) :=
    (pullForm_resForm _ _ _ _).symm
  have e3 := coeff_pullForm_eq_mul K K' (t.2 PUnit.unit) t'.1 inf_le_left (hr.trans inf_le_left) hV
    (resForm inf_le_right (K.om (t'.2 PUnit.unit)))
  have hg : K.coeff (t.2 PUnit.unit) inf_le_left (resForm inf_le_right (K.om (t'.2 PUnit.unit))) =
      (K.bundle.g (t.2 PUnit.unit) (t'.2 PUnit.unit) : Γ(Y, _)) := by
    rw [CanonLB.g_eq_ratio]; rfl
  have hσy : σ y ∈ K.bundle.U (t.2 PUnit.unit) ⊓ K.bundle.U (t'.2 PUnit.unit) := hV hy
  have u2 : (((Units.map (σ.stalkMap y).hom.toMonoidHom (tr K.bundle (σ y) (t.2 PUnit.unit)
      (t'.2 PUnit.unit))) : (X.presheaf.stalk y)ˣ) : X.presheaf.stalk y) =
      (σ.stalkMap y).hom (ger (σ y) hσy (K.bundle.g (t.2 PUnit.unit) (t'.2 PUnit.unit)).val) := by
    rw [Units.coe_map, val_tr K.bundle (σ y) hσy]; rfl
  rw [e1, e2, e3, hg, map_mul, map_mul, ger_resG]
  have e4 := ger_appLE σ hV y hy (K.bundle.g (t.2 PUnit.unit) (t'.2 PUnit.unit)).val
  rw [e4, tr_div _ _ y h h', tr_pull _ σ y h.2 h'.2, Units.val_mul, mul_assoc]
  rw [← u2]
  rw [Units.inv_mul_cancel_left]
  congr 1
  exact (val_tr K'.bundle y _).symm

end MorJac

end GlobalTheory

namespace GlobalTheory

namespace MorJac

open TopForm
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {k : Type} [CommRing k] {Y X : Scheme.{0}} {p : Y ⟶ Sp k} {σ : X ⟶ Y} {D : ℕ}
  [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D (σ ≫ p)]
  (K : CanonLB p D) (K' : CanonLB (σ ≫ p) D)

theorem isUnit_ger_jacLoc (x : X) (hx : Function.Bijective (σ.stalkMap x).hom)
    (a : (LB.div K'.bundle (K.bundle.pull σ)).ι) (ha : x ∈ (LB.div K'.bundle (K.bundle.pull σ)).U a) :
    IsUnit (ger x ha (jacLoc K K' a)) := by
  have hxi : σ x ∈ K.bundle.U (a.2 PUnit.unit) := mem_pull.1 ha.2
  obtain ⟨T, hT, hyT, hTU⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hxi
  obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show x ∈ (LB.div K'.bundle (K.bundle.pull σ)).U a ⊓ σ ⁻¹ᵁ T from ⟨ha, hyT⟩)
  have hT' : IsAffineOpen T := hT
  have hW' : IsAffineOpen W := hW
  have hWa : W ≤ (LB.div K'.bundle (K.bundle.pull σ)).U a := hWU.trans inf_le_left
  have hWT : W ≤ σ ⁻¹ᵁ T := hWU.trans inf_le_right
  rw [← ger_resG hWa x hxW, resG_jacLoc]
  have hWj : W ≤ K'.bundle.U a.1 := hWa.trans inf_le_left
  have hWi : W ≤ σ ⁻¹ᵁ K.bundle.U (a.2 PUnit.unit) :=
    (hWa.trans inf_le_right).trans (GlobalTheory.LB.pull_U_le σ a.2)
  have e2 : pullForm (comp_eq p σ) hWi (K.om (a.2 PUnit.unit)) =
      pullForm (comp_eq p σ) hWT (resForm hTU (K.om (a.2 PUnit.unit))) :=
    (pullForm_resForm _ _ _ _).symm
  have hω := ((K.isFrame (a.2 PUnit.unit)).res hT' hTU).gen
  have hω' := ((K'.isFrame a.1).res hW' hWj).gen
  have rel := K'.coeff_smul_om a.1 hW' hWj (pullForm (comp_eq p σ) hWi (K.om (a.2 PUnit.unit)))
  have hβ : (σ.stalkMap x).hom.comp ((ger (σ x) hyT).comp (algX p T)) =
      (ger x hxW).comp (algX (σ ≫ p) W) := by
    ext c
    have e := DFunLike.congr_fun (appLE_comp_algX (comp_eq p σ) hWT) c
    simp only [RingHom.comp_apply, RingHom.id_apply] at e ⊢
    rw [← e, ger_appLE σ hWT x hxW]
  letI : RingHomCompTriple (σ.appLE T W hWT).hom (ger x hxW)
      ((ger x hxW).comp (σ.appLE T W hWT).hom) := ⟨rfl⟩
  letI : RingHomCompTriple (ger (σ x) hyT) (σ.stalkMap x).hom
      ((ger x hxW).comp (σ.appLE T W hWT).hom) :=
    ⟨RingHom.ext fun c => (ger_appLE σ hWT x hxW c).symm⟩
  have key := LinearMap.congr_fun (forms_ext
    (φ := (TopForm.formMap D (σ.stalkMap x).hom hβ).comp
      (TopForm.formMap D (ger (σ x) hyT) (rfl : _ = (ger (σ x) hyT).comp (algX p T))))
    (ψ := (TopForm.formMap D (ger x hxW) (rfl : _ = (ger x hxW).comp (algX (σ ≫ p) W))).comp
      (pullForm (comp_eq p σ) hWT)) fun f => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, formMap_dForm, formMap_dForm]
      change _ = TopForm.formMap D (ger x hxW) _ (pullForm (comp_eq p σ) hWT (dOn p f))
      rw [pullForm_dOn, formMap_dForm]
      congr 1
      funext b
      exact (ger_appLE σ hWT x hxW (f b)).symm) (resForm hTU (K.om (a.2 PUnit.unit)))
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← e2, ← rel] at key
  have e6 := (TopForm.formMap D (ger x hxW) (rfl : _ = (ger x hxW).comp (algX (σ ≫ p) W))).map_smulₛₗ
    (K'.coeff a.1 hWj (pullForm (comp_eq p σ) hWi (K.om (a.2 PUnit.unit)))) (resForm hWj (K'.om a.1))
  rw [e6] at key
  have fg1 := isFreeGen_formMap (formallyEtale_of_bijective hx) hβ
    (isFreeGen_formMap (formallyEtale_germ hT' (σ x) hyT) rfl hω)
  have fg2 := isFreeGen_formMap (formallyEtale_germ hW' x hxW)
    (rfl : _ = (ger x hxW).comp (algX (σ ≫ p) W)) hω'
  rw [key] at fg1
  exact fg2.smul_iff.1 fg1

end MorJac

end GlobalTheory

namespace GlobalTheory

open MorJac

theorem exists_jacobian_section_isUnit_germ : ∀ (F : Type) [Field F] (Y X : Scheme.{0})
    (p : Y ⟶ Sp F) (σ : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d p] [SmoothOfRelativeDimension d (σ ≫ p)] (K : CanonLB p d)
    (K' : CanonLB (σ ≫ p) d),
    ∃ J : H0 (σ ≫ p) (LB.div K'.bundle (K.bundle.pull σ)) ⊤, ∀ x : X,
      Function.Bijective (σ.stalkMap x).hom →
      ∀ (a : (LB.div K'.bundle (K.bundle.pull σ)).ι) (ha : x ∈ (LB.div K'.bundle (K.bundle.pull σ)).U a),
        IsUnit (H0.germ a x (memTop x) ha J) := by
  intro F _ Y X p σ d _ _ K K'
  have hB : (LB.div K'.bundle (K.bundle.pull σ)).IsLB :=
    LB.isLB_div K'.isLB (Semi.LB.isLB_linComb K.isLB (K := PUnit) (fun _ => σ) (fun _ => 1))
  obtain ⟨J, hJ⟩ := H0.exists_of_germs (p := σ ≫ p) (O := ⊤) hB
    (fun t => (LB.div K'.bundle (K.bundle.pull σ)).U t) (fun t => t) (fun _ => le_top)
    (fun _ => le_rfl) (fun y _ => Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top y)))
    (jacLoc K K') (fun y t t' h h' => ger_jacLoc K K' y t t' h h')
  refine ⟨J, fun x hx a ha => ?_⟩
  exact (congrArg IsUnit (hJ a x ha)).mpr (isUnit_ger_jacLoc K K' x hx a ha)

end GlobalTheory
