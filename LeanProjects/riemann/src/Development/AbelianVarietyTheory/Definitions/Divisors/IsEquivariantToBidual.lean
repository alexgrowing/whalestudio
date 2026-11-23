import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC pullbackSections)
open GlobalTheory.DualPull (adj adj_app pull_ext appLE_resG resG_appLE theta toCut ofCut cutEquiv)
open GlobalTheory.VB GlobalTheory.Conormal

namespace GlobalTheory.LieVB

section Eigen

variable {X Y : Scheme.{0}} {F G : X.Modules} {O : Type} [CommRing O] {ρ : O →+* End F}
  {ρ' : O →+* End G} (σ : O →+* Γ(X, ⊤))

def eigenQuotMap {φ : F ⟶ G} (h : IsEquivariant ρ ρ' φ) : eigenQuot ρ σ ⟶ eigenQuot ρ' σ :=
  eigenDesc (φ ≫ eigenπ ρ' σ) fun a => by
    rw [← Category.assoc, h a, Category.assoc, act_eigenπ, Linear.comp_smul]

@[reassoc (attr := simp)] theorem eigenπ_eigenQuotMap {φ : F ⟶ G} (h : IsEquivariant ρ ρ' φ) :
    eigenπ ρ σ ≫ eigenQuotMap σ h = φ ≫ eigenπ ρ' σ := eigenπ_desc _ _ _ _

theorem isEquivariant_inv {φ : F ≅ G} (h : IsEquivariant ρ ρ' φ.hom) :
    IsEquivariant ρ' ρ φ.inv := fun a => by
  rw [Iso.comp_inv_eq, Category.assoc, h a, Iso.inv_hom_id_assoc]

@[simps] def eigenIso {φ : F ≅ G} (h : IsEquivariant ρ ρ' φ.hom) : eigen ρ σ ≅ eigen ρ' σ where
  hom := eigenMap σ h
  inv := eigenMap σ (isEquivariant_inv h)
  hom_inv_id := by rw [← cancel_mono (eigenι _ _)]; simp
  inv_hom_id := by rw [← cancel_mono (eigenι _ _)]; simp

@[simps] def eigenQuotIso {φ : F ≅ G} (h : IsEquivariant ρ ρ' φ.hom) :
    eigenQuot ρ σ ≅ eigenQuot ρ' σ where
  hom := eigenQuotMap σ h
  inv := eigenQuotMap σ (isEquivariant_inv h)
  hom_inv_id := by rw [← cancel_epi (eigenπ _ _)]; simp
  inv_hom_id := by rw [← cancel_epi (eigenπ _ _)]; simp

variable (ρ)

theorem eigenι_comp_act {c : O →+* O} (hc : Function.Involutive c) (a : O) :
    eigenι (ρ.comp c) σ ≫ act ρ a = σ.comp c a • eigenι (ρ.comp c) σ := by
  have := eigenι_act (ρ.comp c) σ (c a)
  rwa [act, RingHom.comp_apply, hc] at this

def eigenConjIso {c : O →+* O} (hc : Function.Involutive c) :
    eigen (ρ.comp c) σ ≅ eigen ρ (σ.comp c) where
  hom := eigenLift (eigenι _ _) (eigenι_comp_act ρ σ hc)
  inv := eigenLift (eigenι _ _) fun a => by
    have := eigenι_act ρ (σ.comp c) (c a)
    rwa [RingHom.comp_apply, hc] at this
  hom_inv_id := by
    rw [← cancel_mono (eigenι _ _), Category.assoc, eigenLift_ι, eigenLift_ι, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (eigenι _ _), Category.assoc, eigenLift_ι, eigenLift_ι, Category.id_comp]

@[reassoc (attr := simp)] theorem eigenConjIso_hom_ι {c : O →+* O} (hc : Function.Involutive c) :
    (eigenConjIso ρ σ hc).hom ≫ eigenι _ _ = eigenι _ _ :=
  eigenLift_ι ρ _ _ (eigenι_comp_act ρ σ hc)

def eigenQuotConjIso {c : O →+* O} (hc : Function.Involutive c) :
    eigenQuot (ρ.comp c) σ ≅ eigenQuot ρ (σ.comp c) where
  hom := eigenDesc (eigenπ _ _) fun a => by
    have := act_eigenπ ρ (σ.comp c) (c a)
    rwa [RingHom.comp_apply, hc] at this
  inv := eigenDesc (eigenπ _ _) fun a => by
    have := act_eigenπ (ρ.comp c) σ (c a)
    rwa [act, RingHom.comp_apply, hc] at this
  hom_inv_id := by rw [← cancel_epi (eigenπ _ _)]; simp
  inv_hom_id := by rw [← cancel_epi (eigenπ _ _)]; simp

@[reassoc (attr := simp)] theorem eigenπ_eigenQuotConjIso_hom {c : O →+* O}
    (hc : Function.Involutive c) : eigenπ _ _ ≫ (eigenQuotConjIso ρ σ hc).hom = eigenπ _ _ := by
  simp only [eigenQuotConjIso, eigenπ_desc]

theorem smul_eq_smulHom_comp (a : Γ(X, ⊤)) (φ : F ⟶ G) : a • φ = smulHom F a ≫ φ :=
  (smulHom_comp φ a).symm

theorem dualMap_smul (a : Γ(X, ⊤)) (φ : F ⟶ G) : dualMap (a • φ) = a • dualMap φ := by
  rw [smul_eq_smulHom_comp, dualMap_comp, dualMap_smulHom]
  rfl

def dualQuotHom : dual (eigenQuot ρ σ) ⟶ eigen (dualAct ρ) σ :=
  eigenLift (dualMap (eigenπ ρ σ)) fun a => by
    rw [act_dualAct, ← dualMap_comp, act_eigenπ, dualMap_smul]

instance isIso_dualQuotHom : IsIso (dualQuotHom ρ σ) := by
  refine Twist.isIso_of_bijective _ fun V => ⟨Function.Injective.of_comp
    (f := (eigenι (dualAct ρ) σ).app V) (QCoh.injective_app_of_mono (dualMap (eigenπ ρ σ)) V),
    fun s => ?_⟩
  let l := (eigenι (dualAct ρ) σ).app V s
  have hl (a : O) : act ρ a ≫ toCut l = σ a • toCut l := by
    ext W t
    apply (cutEquiv V W).injective
    have := congrArg (fun m => dualApp m (DualPull.cutO_le' V W) (resM F (DualPull.cutO_le V W) t))
      (mem_eigenSub_iff.1 ((eigenSub (dualAct ρ) σ).incl_app_mem s) a)
    refine ((DualPull.toCut_app l W _).trans ?_).trans (DualPull.cutEquiv_smul V W _ _).symm
    refine (congrArg _ (app_resM (act ρ a) _ t).symm).trans (this.trans ?_)
    rw [dualApp_smul, resG_resG]
    exact congrArg₂ (fun x y : Γ(X, DualPull.cutO V W) => x * y) (resG_resG _ _ _).symm rfl
  refine ⟨ofCut (eigenDesc _ hl), (eigenSub (dualAct ρ) σ).incl_app_injective V
    (dual_ext fun W h t => ?_)⟩
  refine (DualPull.dualApp_ofCut _ h ((eigenπ ρ σ).app W t)).trans ?_
  rw [show (eigenDesc _ hl).app W ((eigenπ ρ σ).app W t) = (toCut l).app W t from
    congr(($(eigenπ_desc ρ σ _ hl)).app W t), DualPull.toCut_app, ← dualApp_resM, resM_resM,
    resM_self]
  rfl

def dualQuotIso : dual (eigenQuot ρ σ) ≅ eigen (dualAct ρ) σ := asIso (dualQuotHom ρ σ)

@[reassoc (attr := simp)] theorem dualQuotIso_hom_ι :
    (dualQuotIso ρ σ).hom ≫ eigenι _ _ = dualMap (eigenπ ρ σ) := by
  simp only [dualQuotIso, asIso_hom, dualQuotHom, eigenLift_ι]

theorem isEquivariant_toBidual : IsEquivariant ρ (dualAct (dualAct ρ)) (cartierDualToBidual F) := fun a =>
  toBidual_naturality_dualSheafTranspose (act ρ a)

def pullbackQuotIso (f : Y ⟶ X) : eigenQuot (pullAct ρ f) (f.appTop.hom.comp σ) ≅
    (Scheme.Modules.pullback f).obj (eigenQuot ρ σ) where
  hom := eigenDesc ((Scheme.Modules.pullback f).map (eigenπ ρ σ)) fun a => by
    rw [act_pullAct, ← Functor.map_comp, act_eigenπ, pullback_map_smul]; rfl
  inv := adj f (eigenDesc ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
    (eigenπ (pullAct ρ f) (f.appTop.hom.comp σ))) fun a => by
      rw [← Adjunction.homEquiv_naturality_left, smul_eq_smulHom_comp,
        ← Adjunction.homEquiv_naturality_left, pullback_map_smulHom, ← smul_eq_smulHom_comp]
      exact congrArg _ (act_eigenπ (pullAct ρ f) _ a))
  hom_inv_id := by
    rw [← cancel_epi (eigenπ _ _), eigenπ_desc_assoc, Category.comp_id, adj,
      ← Adjunction.homEquiv_naturality_left_symm, eigenπ_desc, Equiv.symm_apply_apply]
  inv_hom_id := by
    rw [← cancel_epi ((Scheme.Modules.pullback f).map (eigenπ ρ σ)), ← Category.assoc, adj,
      ← Adjunction.homEquiv_naturality_left_symm, eigenπ_desc, Equiv.symm_apply_apply, eigenπ_desc,
      Category.comp_id]

@[reassoc (attr := simp)] theorem eigenπ_pullbackQuotIso_hom (f : Y ⟶ X) :
    eigenπ _ _ ≫ (pullbackQuotIso ρ σ f).hom = (Scheme.Modules.pullback f).map (eigenπ ρ σ) := by
  simp only [pullbackQuotIso, eigenπ_desc]

theorem hom_ext_of_isFrame {κ : Type} [Fintype κ] {e : κ → Γ(F, ⊤)} (he : IsFrame e)
    {φ ψ : F ⟶ G} (h : ∀ i, φ.app ⊤ (e i) = ψ.app ⊤ (e i)) : φ = ψ := by
  ext V s
  refine congr($((he.basis le_top).ext (f₁ := QCoh.appLinear φ V) (f₂ := QCoh.appLinear ψ V)
    fun i => ?_) s)
  rw [IsFrame.basis_apply]
  exact (app_resM φ _ _).trans ((congrArg _ (h i)).trans (app_resM ψ _ _).symm)

end Eigen

theorem isFrame_d_Spec {R A : CommRingCat.{0}} [Algebra R A] (ε : A →ₐ[R] R)
    {π : Spec A ⟶ Spec R} {e : Spec R ⟶ Spec A} (he : e ≫ π = 𝟙 _)
    (hπ : π = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hε : e = Spec.map (CommRingCat.ofHom ε.toRingHom)) {κ : Type} [Fintype κ]
    (b : Module.Basis κ R (AugCot ε)) (a : κ → A) (hb : ∀ i, b i = AugCot.d ε (a i)) :
    IsFrame fun i => d he (W := ⊤) (V := ⊤) le_top ((Scheme.ΓSpecIso A).inv (a i)) := by
  subst hπ hε
  exact IsChart.isFrame_d he ⟨isAffineOpen_top _, isAffineOpen_top _, le_top, le_top⟩ ε
    (Scheme.ΓSpecIso R).inv.hom (Scheme.ΓSpecIso A).inv.hom
    (IsPushout.of_vert_isIso (g := (Scheme.ΓSpecIso R).inv) (inl := (Scheme.ΓSpecIso A).inv)
      ⟨Scheme.ΓSpecIso_inv_naturality _⟩)
    (fun x => congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ε.toRingHom)) x).symm)
    b a hb

end GlobalTheory.LieVB
