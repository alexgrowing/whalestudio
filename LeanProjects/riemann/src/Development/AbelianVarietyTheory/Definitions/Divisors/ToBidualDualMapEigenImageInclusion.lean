import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC structureModule)
open GlobalTheory.VB

namespace GlobalTheory.LieVB

variable {X Y : Scheme.{0}} {F G H : X.Modules} {O : Type} [CommRing O]

variable (F) in

@[reassoc (attr := simp)] theorem toBidual_dual_comp_dualMap :
    cartierDualToBidual (dual F) ≫ dualMap (cartierDualToBidual F) = 𝟙 _ := by
  ext V l : 3
  exact dual_ext fun W h s => congrArg (dualApp l h) (resM_self _ s)

instance mono_toBidual_dual : Mono (cartierDualToBidual (dual F)) :=
  mono_of_mono_fac (toBidual_dual_comp_dualMap F)

theorem mono_toBidual_of_mono (i : G ⟶ F) [Mono i] [Mono (cartierDualToBidual F)] : Mono (cartierDualToBidual G) :=
  mono_of_mono_fac (toBidual_naturality_dualSheafTranspose i).symm

theorem mono_toBidual_of_isVectorBundle {r : ℕ} (h : IsVB F r) : Mono (cartierDualToBidual F) :=
  have := h.isIso_toBidual_of_local_frames
  inferInstance

def IsRegularFn (D : Γ(X, ⊤)) : Prop :=
  ∀ (V : X.Opens) (a : Γ(X, V)), resG X (le_top : V ≤ ⊤) D * a = 0 → a = 0

theorem isRegularFn_of_isUnit {D : Γ(X, ⊤)} (h : IsUnit D) : IsRegularFn D :=
  fun _ _ e => (h.map _).mul_right_eq_zero.1 e

theorem isRegularFn_of_ne_zero [IsIntegral X] {D : Γ(X, ⊤)} (h : D ≠ 0) : IsRegularFn D := by
  intro V a e
  rcases eq_or_ne V ⊥ with rfl | hV
  · exact Subsingleton.elim _ _
  · obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).1 hV
    have : Nonempty V := ⟨⟨x, hx⟩⟩
    refine (mul_eq_zero.1 e).resolve_left fun h0 => h ?_
    exact map_injective_of_isIntegral X (homOfLE le_top) (h0.trans (map_zero _).symm)

theorem IsRegularFn.eq_zero_of_smul {D : Γ(X, ⊤)} (h : IsRegularFn D) [Mono (cartierDualToBidual F)]
    {V : X.Opens} {s : Γ(F, V)} (e : resG X (le_top : V ≤ ⊤) D • s = 0) : s = 0 := by
  refine QCoh.injective_app_of_mono (cartierDualToBidual F) V (Eq.trans ?_ (map_zero _).symm)
  refine dual_ext fun W hW l => h W _ ?_
  have := congrArg (fun t => dualApp l le_rfl (resM F hW t)) e
  simp only [resM_smul, map_smul, resG_resG, map_zero] at this
  exact this

theorem IsRegularFn.hom_eq_zero {D : Γ(X, ⊤)} (h : IsRegularFn D) [Mono (cartierDualToBidual F)]
    {φ : G ⟶ F} (e : D • φ = 0) : φ = 0 := by
  ext V s : 3
  exact h.eq_zero_of_smul congr(($e).app V s)

theorem isTorsionFree_of_mono_toBidual [IsIntegral X] [Mono (cartierDualToBidual F)] : IsTorsionFree F := by
  refine IsTorsionFree.of_mono (fun V hV l hl => dual_ext fun W h s => ?_) (cartierDualToBidual F)
  rcases eq_or_ne W ⊥ with rfl | hW'
  · exact Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).1 hW'
  have hW := genericPoint_mem hx
  obtain ⟨T, hT, i₁, i₂, e⟩ := (dual (dual F)).presheaf.germ_eq _ hW hW (resM _ h l) 0
    (by rw [Twist.germ_resM, hl, map_zero])
  have : Nonempty T := ⟨⟨_, hT⟩⟩
  refine map_injective_of_isIntegral X i₁ ?_
  have e' : resM _ i₁.le (resM _ h l) = 0 := e.trans (map_zero _)
  have := congrArg (fun m => dualApp m le_rfl (resM _ i₁.le s)) e'
  exact (dualApp_resM l h i₁.le s).symm.trans (this.trans (map_zero _).symm)

section Im

variable (ρ : O →+* End F) (σ : O →+* Γ(X, ⊤))

def eigenEval : F ⟶ dual (eigen (dualAct ρ) σ) := cartierDualToBidual F ≫ dualMap (eigenι (dualAct ρ) σ)

theorem dualApp_eigenEval {V W : X.Opens} (s : Γ(F, V)) (h : W ≤ V)
    (l : Γ(eigen (dualAct ρ) σ, W)) : dualApp ((eigenEval ρ σ).app V s) h l =
      dualApp ((eigenι (dualAct ρ) σ).app W l) le_rfl (resM F h s) := rfl

theorem eigenEval_eq : eigenEval ρ σ =
    eigenπ ρ σ ≫ cartierDualToBidual _ ≫ dualMap (dualQuotIso ρ σ).inv := by
  rw [toBidual_naturality_dualSheafTranspose_assoc, ← dualMap_comp, ← dualQuotIso_hom_ι, Iso.inv_hom_id_assoc,
    eigenEval]

def eigenIm : X.Modules := image (eigenEval ρ σ)

def eigenImπ : F ⟶ eigenIm ρ σ := factorThruImage _

def eigenImι : eigenIm ρ σ ⟶ dual (eigen (dualAct ρ) σ) := image.ι _

instance epi_eigenImπ : Epi (eigenImπ ρ σ) := inferInstanceAs (Epi (factorThruImage _))

instance mono_eigenImι : Mono (eigenImι ρ σ) := inferInstanceAs (Mono (image.ι _))

@[reassoc (attr := simp)] theorem eigenImπ_ι : eigenImπ ρ σ ≫ eigenImι ρ σ = eigenEval ρ σ :=
  image.fac _

instance mono_toBidual_eigenImage : Mono (cartierDualToBidual (eigenIm ρ σ)) :=
  mono_toBidual_of_mono (eigenImι ρ σ)

theorem isTorsionFree_eigenIm [IsIntegral X] : IsTorsionFree (eigenIm ρ σ) :=
  isTorsionFree_of_mono_toBidual

theorem eigenImπ_app_eq_zero_iff {V : X.Opens} {s : Γ(F, V)} : (eigenImπ ρ σ).app V s = 0 ↔
    ∀ (W : X.Opens) (h : W ≤ V) (l : Γ(dual F, W)), l ∈ (eigenSub (dualAct ρ) σ).sec W →
      dualApp l le_rfl (resM F h s) = 0 := by
  have e : (eigenImι ρ σ).app V ((eigenImπ ρ σ).app V s) = (eigenEval ρ σ).app V s :=
    congr(($(eigenImπ_ι ρ σ)).app V s)
  rw [← map_eq_zero_iff _ (QCoh.injective_app_of_mono (eigenImι ρ σ) V), e]
  exact ⟨fun H W h l hl => congrArg (dualApp · h ((eigenSub _ σ).mkSec l hl)) H,
    fun H => dual_ext fun W h l => H W h _ ((eigenSub _ σ).incl_app_mem l)⟩

theorem act_eigenImπ (a : O) : act ρ a ≫ eigenImπ ρ σ = σ a • eigenImπ ρ σ := by
  rw [← cancel_mono (eigenImι ρ σ), Category.assoc, Linear.smul_comp, eigenImπ_ι, eigenEval_eq,
    ← Category.assoc, act_eigenπ, Linear.smul_comp]

theorem isEquivariant_eigenImπ : IsEquivariant ρ (scalarAct (eigenIm ρ σ) σ) (eigenImπ ρ σ) :=
  fun a => act_eigenImπ ρ σ a

def quotToIm : eigenQuot ρ σ ⟶ eigenIm ρ σ := eigenDesc (eigenImπ ρ σ) (act_eigenImπ ρ σ)

@[reassoc (attr := simp)] theorem eigenπ_quotToIm : eigenπ ρ σ ≫ quotToIm ρ σ = eigenImπ ρ σ :=
  eigenπ_desc _ _ _ _

instance epi_quotToIm : Epi (quotToIm ρ σ) := epi_of_epi_fac (eigenπ_quotToIm ρ σ)

@[reassoc] theorem quotToIm_ι : quotToIm ρ σ ≫ eigenImι ρ σ =
    cartierDualToBidual _ ≫ dualMap (dualQuotIso ρ σ).inv := by
  rw [← cancel_epi (eigenπ ρ σ), eigenπ_quotToIm_assoc, eigenImπ_ι, eigenEval_eq]

variable {ρ σ}

theorem comp_eq_zero_of_comp_eigenImπ [Mono (cartierDualToBidual G)] {φ : F ⟶ G}
    (h : ∀ a, act ρ a ≫ φ = σ a • φ) {k : H ⟶ F} (hk : k ≫ eigenImπ ρ σ = 0) : k ≫ φ = 0 := by
  have h' (a : O) : dualMap φ ≫ act (dualAct ρ) a = σ a • dualMap φ := by
    rw [act_dualAct, ← dualMap_comp, h, dualMap_smul]
  rw [← cancel_mono (cartierDualToBidual G), Category.assoc, toBidual_naturality_dualSheafTranspose, ← eigenLift_ι _ _ _ h',
    dualMap_comp, zero_comp, ← Category.assoc (cartierDualToBidual F), ← eigenEval, ← eigenImπ_ι,
    Category.assoc, reassoc_of% hk, zero_comp]

def eigenImDesc [Mono (cartierDualToBidual G)] (φ : F ⟶ G) (h : ∀ a, act ρ a ≫ φ = σ a • φ) :
    eigenIm ρ σ ⟶ G :=
  Abelian.epiDesc (eigenImπ ρ σ) φ (comp_eq_zero_of_comp_eigenImπ h (kernel.condition _))

@[reassoc (attr := simp)] theorem eigenImπ_desc [Mono (cartierDualToBidual G)] (φ : F ⟶ G)
    (h : ∀ a, act ρ a ≫ φ = σ a • φ) : eigenImπ ρ σ ≫ eigenImDesc φ h = φ :=
  Abelian.comp_epiDesc _ _ _

variable {ρ' : O →+* End G} (σ)

def eigenImMap {φ : F ⟶ G} (h : IsEquivariant ρ ρ' φ) : eigenIm ρ σ ⟶ eigenIm ρ' σ :=
  eigenImDesc (φ ≫ eigenImπ ρ' σ) fun a => by
    rw [← Category.assoc, h a, Category.assoc, act_eigenImπ, Linear.comp_smul]

@[reassoc (attr := simp)] theorem eigenImπ_eigenImMap {φ : F ⟶ G} (h : IsEquivariant ρ ρ' φ) :
    eigenImπ ρ σ ≫ eigenImMap σ h = φ ≫ eigenImπ ρ' σ := eigenImπ_desc _ _

@[reassoc] theorem quotToIm_eigenImMap {φ : F ⟶ G} (h : IsEquivariant ρ ρ' φ) :
    quotToIm ρ σ ≫ eigenImMap σ h = eigenQuotMap σ h ≫ quotToIm ρ' σ := by
  rw [← cancel_epi (eigenπ ρ σ)]; simp

@[reassoc] theorem eigenImMap_ι {φ : F ⟶ G} (h : IsEquivariant ρ ρ' φ) :
    eigenImMap σ h ≫ eigenImι ρ' σ = eigenImι ρ σ ≫ dualMap (eigenMap σ h.dual) := by
  rw [← cancel_epi (eigenImπ ρ σ), eigenImπ_eigenImMap_assoc, eigenImπ_ι, eigenImπ_ι_assoc,
    eigenEval, eigenEval, toBidual_naturality_dualSheafTranspose_assoc, Category.assoc, ← dualMap_comp, ← dualMap_comp,
    eigenMap_ι]

instance epi_eigenImMap {φ : F ⟶ G} [Epi φ] (h : IsEquivariant ρ ρ' φ) : Epi (eigenImMap σ h) :=
  epi_of_epi_fac (eigenImπ_eigenImMap σ h)

@[simps] def eigenImIso {φ : F ≅ G} (h : IsEquivariant ρ ρ' φ.hom) :
    eigenIm ρ σ ≅ eigenIm ρ' σ where
  hom := eigenImMap σ h
  inv := eigenImMap σ (isEquivariant_inv h)
  hom_inv_id := by rw [← cancel_epi (eigenImπ _ _)]; simp
  inv_hom_id := by rw [← cancel_epi (eigenImπ _ _)]; simp

variable (ρ)

def eigenImConjIso {c : O →+* O} (hc : Function.Involutive c) :
    eigenIm (ρ.comp c) σ ≅ eigenIm ρ (σ.comp c) where
  hom := eigenImDesc (eigenImπ _ _) fun a => by
    have := act_eigenImπ ρ (σ.comp c) (c a)
    rwa [RingHom.comp_apply, hc] at this
  inv := eigenImDesc (eigenImπ _ _) fun a => by
    have := act_eigenImπ (ρ.comp c) σ (c a)
    rwa [act, RingHom.comp_apply, hc] at this
  hom_inv_id := by rw [← cancel_epi (eigenImπ _ _)]; simp
  inv_hom_id := by rw [← cancel_epi (eigenImπ _ _)]; simp

@[reassoc (attr := simp)] theorem eigenImπ_eigenImConjIso_hom {c : O →+* O}
    (hc : Function.Involutive c) : eigenImπ _ _ ≫ (eigenImConjIso ρ σ hc).hom = eigenImπ _ _ := by
  simp only [eigenImConjIso, eigenImπ_desc]

theorem toBidual_dualMap_eigenImage_inclusion : (cartierDualToBidual _ ≫ dualMap (eigenImι ρ σ)) ≫
    dualMap (eigenImπ ρ σ) = eigenι (dualAct ρ) σ := by
  rw [Category.assoc, ← dualMap_comp, eigenImπ_ι, eigenEval, dualMap_comp,
    ← toBidual_naturality_dualSheafTranspose_assoc, toBidual_dual_comp_dualMap, Category.comp_id]

def dualImIso : dual (eigenIm ρ σ) ≅ eigen (dualAct ρ) σ where
  hom := eigenLift (dualMap (eigenImπ ρ σ)) fun a => by
    rw [act_dualAct, ← dualMap_comp, act_eigenImπ, dualMap_smul]
  inv := cartierDualToBidual _ ≫ dualMap (eigenImι ρ σ)
  hom_inv_id := by
    rw [← cancel_mono (dualMap (eigenImπ ρ σ)), Category.assoc, toBidual_dualMap_eigenImage_inclusion,
      eigenLift_ι, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (eigenι _ _), Category.assoc, eigenLift_ι, toBidual_dualMap_eigenImage_inclusion,
      Category.id_comp]

@[reassoc (attr := simp)] theorem dualImIso_hom_ι :
    (dualImIso ρ σ).hom ≫ eigenι _ _ = dualMap (eigenImπ ρ σ) := rfl

theorem eigenImι_eq : eigenImι ρ σ = cartierDualToBidual _ ≫ dualMap (dualImIso ρ σ).inv := by
  rw [← cancel_epi (eigenImπ ρ σ), eigenImπ_ι, toBidual_naturality_dualSheafTranspose_assoc, ← dualMap_comp,
    ← dualImIso_hom_ι, Iso.inv_hom_id_assoc, eigenEval]

theorem isIso_eigenImι {r : ℕ} (h : IsVB (eigenIm ρ σ) r) : IsIso (eigenImι ρ σ) := by
  have := h.isIso_toBidual_of_local_frames
  rw [eigenImι_eq]
  exact inferInstanceAs (IsIso (_ ≫ (dualIso (dualImIso ρ σ).symm).hom))

theorem isVB_eigen_dualAct {r : ℕ} (h : IsVB (eigenIm ρ σ) r) : IsVB (eigen (dualAct ρ) σ) r :=
  h.dual.of_iso (dualImIso ρ σ)

theorem isIso_eigenImι_of_epi {r : ℕ} (h : IsVB F r) [Epi (dualMap (eigenι (dualAct ρ) σ))] :
    IsIso (eigenImι ρ σ) :=
  have := h.isIso_toBidual_of_local_frames
  have : Epi (eigenEval ρ σ) := epi_comp _ _
  have := epi_of_epi_fac (eigenImπ_ι ρ σ)
  isIso_of_mono_of_epi _

theorem isIso_quotToIm_iff : IsIso (quotToIm ρ σ) ↔ Mono (cartierDualToBidual (eigenQuot ρ σ)) := by
  refine ⟨fun _ => mono_toBidual_of_mono (quotToIm ρ σ), fun _ => ?_⟩
  have : Mono (cartierDualToBidual _ ≫ dualMap (dualQuotIso ρ σ).inv) := mono_comp _ _
  have := mono_of_mono_fac (quotToIm_ι ρ σ)
  exact isIso_of_mono_of_epi _

theorem isIso_quotToIm {r : ℕ} (h : IsVB (eigenQuot ρ σ) r) : IsIso (quotToIm ρ σ) :=
  (isIso_quotToIm_iff ρ σ).2 (mono_toBidual_of_isVectorBundle h)

theorem isIso_quotToIm_of_isIso [Mono (cartierDualToBidual F)] [IsIso (eigenι ρ σ ≫ eigenπ ρ σ)] :
    IsIso (quotToIm ρ σ) :=
  (isIso_quotToIm_iff ρ σ).2 (mono_toBidual_of_mono (inv (eigenι ρ σ ≫ eigenπ ρ σ) ≫ eigenι ρ σ))

theorem isIso_quotToIm_of_split {k κ : Type} [Field k] [Algebra k Γ(X, ⊤)] [Fintype κ]
    {τ : κ → (O →+* k)} (hτ : IsSplitBy τ) [Mono (cartierDualToBidual F)] (j : κ) :
    IsIso (quotToIm ρ (scal X (τ j))) := by
  classical
  have := hτ.isIso_eigenι_eigenπ ρ j
  exact isIso_quotToIm_of_isIso _ _

theorem isIso_eigenι_eigenImπ_of_split {k κ : Type} [Field k] [Algebra k Γ(X, ⊤)] [Fintype κ]
    {τ : κ → (O →+* k)} (hτ : IsSplitBy τ) [Mono (cartierDualToBidual F)] (j : κ) :
    IsIso (eigenι ρ (scal X (τ j)) ≫ eigenImπ ρ (scal X (τ j))) := by
  classical
  have := hτ.isIso_eigenι_eigenπ ρ j
  have := isIso_quotToIm_of_split ρ hτ j
  rw [← eigenπ_quotToIm, ← Category.assoc]
  infer_instance

variable {ρ σ}

theorem isIso_eigenπ_of_actsThrough (h : ActsThrough ρ σ) : IsIso (eigenπ ρ σ) :=
  ⟨eigenDesc (𝟙 F) fun a => by rw [Category.comp_id, h a, smulHom_eq_smul_id],
    eigenπ_desc _ _ _ _, by rw [← cancel_epi (eigenπ ρ σ)]; simp⟩

theorem isIso_eigenImπ_of_actsThrough [Mono (cartierDualToBidual F)] (h : ActsThrough ρ σ) :
    IsIso (eigenImπ ρ σ) :=
  ⟨eigenImDesc (𝟙 F) fun a => by rw [Category.comp_id, h a, smulHom_eq_smul_id],
    eigenImπ_desc _ _, by rw [← cancel_epi (eigenImπ ρ σ)]; simp⟩

theorem isZero_eigenIm_of_actsThrough {τ : O →+* Γ(X, ⊤)} (h : ActsThrough ρ τ) {a : O}
    (ha : IsRegularFn (τ a - σ a)) : IsZero (eigenIm ρ σ) := by
  refine IsZero.of_epi_eq_zero (eigenImπ ρ σ) (ha.hom_eq_zero ?_)
  rw [sub_smul, ← act_eigenImπ, h a, smulHom_comp]
  exact sub_self _

end Im

section Proj

variable (ρ : O →+* End F) (σ : O →+* Γ(X, ⊤))

structure IsEigenProj (ε : F ⟶ F) (D : Γ(X, ⊤)) : Prop where

  act_comp : ∀ a, act ρ a ≫ ε = σ a • ε

  exists_sum : ∃ (n : ℕ) (c : Fin n → Γ(X, ⊤)) (b : Fin n → O),
    ε = ∑ i, c i • act ρ (b i) ∧ D = ∑ i, c i * σ (b i)

variable {ρ σ}

theorem isEigenProj_of_tensor {R : Type} [CommRing R] (β : R →+* Γ(X, ⊤)) (χ : O →+* R)
    (t : R ⊗[ℤ] O →+* End F) (ht : ∀ c a, act t (c ⊗ₜ a) = β c • act ρ a) (v : R ⊗[ℤ] O →+ R)
    (hv : ∀ c a, v (c ⊗ₜ a) = c * χ a) {x : R ⊗[ℤ] O} (hx : ∀ a, (1 ⊗ₜ a) * x = χ a • x) :
    IsEigenProj ρ (β.comp χ) (act t x) (β (v x)) where
  act_comp a := by
    have e : x * (1 ⊗ₜ a) = (χ a ⊗ₜ 1) * x := by
      rw [mul_comm, hx, Algebra.smul_def]; rfl
    have := congrArg t e
    rw [map_mul, map_mul] at this
    change act t _ ≫ act t x = act t x ≫ act t _ at this
    rw [ht, ht, map_one, one_smul, Linear.comp_smul, act, act, act, map_one] at this
    exact this.trans (congrArg _ (Category.comp_id _))
  exists_sum := by
    obtain ⟨n, c, b, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
    refine ⟨n, fun i => β (c i), b, ?_, ?_⟩
    · exact (map_sum t _ _).trans (Finset.sum_congr rfl fun i _ => ht _ _)
    · simp [hv]

theorem exists_isEigenProj_of_tensor (ρ : O →+* End F) {R : Type} [CommRing R] (β : R →+* Γ(X, ⊤))
    (χ : O →+* R) (v : R ⊗[ℤ] O →+ R) (hv : ∀ c a, v (c ⊗ₜ a) = c * χ a) {x : R ⊗[ℤ] O}
    (hx : ∀ a, (1 ⊗ₜ a) * x = χ a • x) : ∃ ε, IsEigenProj ρ (β.comp χ) ε (β (v x)) :=
  letI : Algebra ℤ (End F) := Ring.toIntAlgebra _
  ⟨_, isEigenProj_of_tensor β χ (Algebra.TensorProduct.lift ((smulEnd F).comp β).toIntAlgHom
    ρ.toIntAlgHom fun _ a => (smulHom_comp (act ρ a) _).symm).toRingHom (fun _ _ => rfl) v hv hx⟩

theorem isEigenProj_idem {k κ : Type} [Field k] [Algebra k Γ(X, ⊤)] [DecidableEq κ]
    {τ : κ → (O →+* k)} (hτ : IsSplitBy τ) (j : κ) :
    IsEigenProj ρ (scal X (τ j)) (act (tensorAct k ρ) (hτ.idem j)) 1 := by
  have := isEigenProj_of_tensor (ρ := ρ) (algebraMap k Γ(X, ⊤)) (τ j) (tensorAct k ρ)
    (act_tensorAct_tmul ρ) ((Pi.evalAddMonoidHom _ j).comp (splitMap τ).toAddMonoidHom)
    (fun _ _ => rfl) (x := hτ.idem j) fun a => by
      rw [hτ.tmul_mul_idem, Algebra.smul_def]; rfl
  simpa using this

namespace IsEigenProj

variable {ε : F ⟶ F} {D : Γ(X, ⊤)} (h : IsEigenProj ρ σ ε D)
include h

theorem comp_eq_smul {φ : F ⟶ G} (hφ : ∀ a, act ρ a ≫ φ = σ a • φ) : ε ≫ φ = D • φ := by
  obtain ⟨n, c, b, rfl, rfl⟩ := h.exists_sum
  simp only [Preadditive.sum_comp, Linear.smul_comp, hφ, Finset.sum_smul, mul_smul]

theorem comp_eq_smul' {φ : G ⟶ F} (hφ : ∀ a, φ ≫ act ρ a = σ a • φ) : φ ≫ ε = D • φ := by
  obtain ⟨n, c, b, rfl, rfl⟩ := h.exists_sum
  simp only [Preadditive.comp_sum, Linear.comp_smul, hφ, Finset.sum_smul, mul_smul]

theorem isEquivariant : IsEquivariant ρ ρ ε := fun a => by
  obtain ⟨n, c, b, rfl, -⟩ := h.exists_sum
  have e (x : O) : act ρ a ≫ act ρ x = act ρ x ≫ act ρ a :=
    (map_mul ρ x a).symm.trans ((congrArg ρ (mul_comm x a)).trans (map_mul ρ a x))
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Linear.comp_smul, Linear.smul_comp, e]

theorem comp_act (a : O) : ε ≫ act ρ a = σ a • ε := (h.isEquivariant a).symm.trans (h.act_comp a)

theorem comp_self : ε ≫ ε = D • ε := h.comp_eq_smul h.act_comp

theorem dual : IsEigenProj (dualAct ρ) σ (dualMap ε) D where
  act_comp a := by rw [act_dualAct, ← dualMap_comp, h.comp_act, dualMap_smul]
  exists_sum := by
    obtain ⟨n, c, b, rfl, e⟩ := h.exists_sum
    refine ⟨n, c, b, (map_sum (AddMonoidHom.mk' (fun φ : F ⟶ F => dualMap φ) dualMap_add) _ _).trans
      (Finset.sum_congr rfl fun i _ => dualMap_smul _ _), e⟩

theorem pullback (f : Y ⟶ X) : IsEigenProj (pullAct ρ f) (f.appTop.hom.comp σ)
    ((Scheme.Modules.pullback f).map ε) (f.appTop D) where
  act_comp a := by rw [act_pullAct, ← Functor.map_comp, h.act_comp, pullback_map_smul]; rfl
  exists_sum := by
    obtain ⟨n, c, b, rfl, rfl⟩ := h.exists_sum
    refine ⟨n, fun i => f.appTop (c i), b, ?_, by simp⟩
    rw [Functor.map_sum]
    exact Finset.sum_congr rfl fun i _ => pullback_map_smul _ _ _

theorem of_iso {ρ' : O →+* End G} {φ : F ≅ G} (hφ : IsEquivariant ρ ρ' φ.hom) :
    IsEigenProj ρ' σ (φ.inv ≫ ε ≫ φ.hom) D where
  act_comp a := by
    rw [reassoc_of% isEquivariant_inv hφ a, reassoc_of% h.act_comp a, Linear.smul_comp,
      Linear.comp_smul]
  exists_sum := by
    obtain ⟨n, c, b, rfl, e⟩ := h.exists_sum
    refine ⟨n, c, b, ?_, e⟩
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Linear.comp_smul, Linear.smul_comp,
      hφ _, Iso.inv_hom_id_assoc]

theorem comp_eigenImπ_eq_zero (hD : IsRegularFn D) {k : G ⟶ F} (hk : k ≫ ε = 0) :
    k ≫ eigenImπ ρ σ = 0 :=
  hD.hom_eq_zero (by
    rw [← Linear.comp_smul, ← h.comp_eq_smul (act_eigenImπ ρ σ), reassoc_of% hk, zero_comp])

variable [Mono (cartierDualToBidual F)]

def imToSub : eigenIm ρ σ ⟶ eigen ρ σ :=
  eigenLift (eigenImDesc ε h.act_comp) fun a => by
    rw [← cancel_epi (eigenImπ ρ σ), eigenImπ_desc_assoc, Linear.comp_smul, eigenImπ_desc,
      h.comp_act]

@[reassoc (attr := simp)] theorem eigenImπ_imToSub_ι :
    eigenImπ ρ σ ≫ h.imToSub ≫ eigenι ρ σ = ε := eigenImπ_desc _ h.act_comp

theorem imToSub_ι_eigenImπ : h.imToSub ≫ eigenι ρ σ ≫ eigenImπ ρ σ = D • 𝟙 _ := by
  rw [← cancel_epi (eigenImπ ρ σ), eigenImπ_imToSub_ι_assoc, h.comp_eq_smul (act_eigenImπ ρ σ),
    Linear.comp_smul, Category.comp_id]

theorem ι_eigenImπ_imToSub : eigenι ρ σ ≫ eigenImπ ρ σ ≫ h.imToSub = D • 𝟙 _ := by
  rw [← cancel_mono (eigenι ρ σ), Category.assoc, Category.assoc, eigenImπ_imToSub_ι,
    h.comp_eq_smul' (eigenι_act ρ σ), Linear.smul_comp, Category.id_comp]

theorem quotToIm_imToSub_ι_eigenπ :
    quotToIm ρ σ ≫ h.imToSub ≫ eigenι ρ σ ≫ eigenπ ρ σ = D • 𝟙 _ := by
  rw [← cancel_epi (eigenπ ρ σ), eigenπ_quotToIm_assoc, eigenImπ_imToSub_ι_assoc,
    h.comp_eq_smul (act_eigenπ ρ σ), Linear.comp_smul, Category.comp_id]

variable (hD : IsRegularFn D)
include hD

theorem comp_eigenImπ_eq_zero_iff {k : G ⟶ F} : k ≫ eigenImπ ρ σ = 0 ↔ k ≫ ε = 0 :=
  ⟨comp_eq_zero_of_comp_eigenImπ h.act_comp, h.comp_eigenImπ_eq_zero hD⟩

theorem eigenImπ_app_eq_zero_iff {V : X.Opens} {s : Γ(F, V)} :
    (eigenImπ ρ σ).app V s = 0 ↔ ε.app V s = 0 := by
  refine ⟨fun e => ?_, fun e => hD.eq_zero_of_smul ?_⟩
  · refine congr(($(h.eigenImπ_imToSub_ι)).app V s).symm.trans ?_
    exact (congrArg ((h.imToSub ≫ eigenι ρ σ).app V) e).trans (map_zero _)
  · refine congr(($(h.comp_eq_smul (act_eigenImπ ρ σ))).app V s).symm.trans ?_
    exact (congrArg ((eigenImπ ρ σ).app V) e).trans (map_zero _)

theorem quotToIm_app_eq_zero_iff {V : X.Opens} {s : Γ(eigenQuot ρ σ, V)} :
    (quotToIm ρ σ).app V s = 0 ↔ resG X (le_top : V ≤ ⊤) D • s = 0 := by
  refine ⟨fun e => ?_, fun e => hD.eq_zero_of_smul ?_⟩
  · refine congr(($(h.quotToIm_imToSub_ι_eigenπ)).app V s).symm.trans ?_
    exact (congrArg ((h.imToSub ≫ eigenι ρ σ ≫ eigenπ ρ σ).app V) e).trans (map_zero _)
  · rw [← Scheme.Modules.Hom.app_smul, e, map_zero]

theorem mono_imToSub : Mono h.imToSub :=
  Preadditive.mono_of_cancel_zero _ fun g hg => hD.hom_eq_zero (by
    rw [← Category.comp_id g, ← Linear.comp_smul, ← h.imToSub_ι_eigenImπ, reassoc_of% hg, zero_comp])

theorem mono_ι_eigenImπ : Mono (eigenι ρ σ ≫ eigenImπ ρ σ) :=
  have := mono_toBidual_of_mono (eigenι ρ σ)
  Preadditive.mono_of_cancel_zero _ fun g hg => hD.hom_eq_zero (by
    rw [← Category.comp_id g, ← Linear.comp_smul, ← h.ι_eigenImπ_imToSub, reassoc_of% hg, zero_comp])

def imIsoImage : eigenIm ρ σ ≅ image ε :=
  have := h.mono_imToSub hD
  have := strongEpi_of_epi (eigenImπ ρ σ)
  image.isoStrongEpiMono (eigenImπ ρ σ) (h.imToSub ≫ eigenι ρ σ) h.eigenImπ_imToSub_ι

@[reassoc (attr := simp)] theorem imIsoImage_hom_ι :
    (h.imIsoImage hD).hom ≫ image.ι ε = h.imToSub ≫ eigenι ρ σ :=
  have := h.mono_imToSub hD
  have := strongEpi_of_epi (eigenImπ ρ σ)
  image.isoStrongEpiMono_hom_comp_ι _ _ h.eigenImπ_imToSub_ι

theorem isQuasicoherent_eigenIm [F.IsQuasicoherent] : (eigenIm ρ σ).IsQuasicoherent :=
  have := h.mono_imToSub hD
  QCoh.isQuasicoherent_of_epi_of_mono (eigenImπ ρ σ) (h.imToSub ≫ eigenι ρ σ)

theorem isFiniteQC_eigenIm [IsFiniteQC F] : IsFiniteQC (eigenIm ρ σ) :=
  have := h.isQuasicoherent_eigenIm hD
  .of_epi (eigenImπ ρ σ)

omit hD

variable (f : Y ⟶ X) (hf : IsRegularFn (f.appTop D))

def pullbackImHom : (Scheme.Modules.pullback f).obj (eigenIm ρ σ) ⟶
    eigenIm (pullAct ρ f) (f.appTop.hom.comp σ) :=
  Abelian.epiDesc ((Scheme.Modules.pullback f).map (eigenImπ ρ σ)) (eigenImπ _ _)
    ((h.pullback f).comp_eigenImπ_eq_zero hf (by
      rw [← h.eigenImπ_imToSub_ι, Functor.map_comp, kernel.condition_assoc, zero_comp]))

@[reassoc (attr := simp)] theorem map_eigenImπ_pullbackImHom :
    (Scheme.Modules.pullback f).map (eigenImπ ρ σ) ≫ h.pullbackImHom f hf = eigenImπ _ _ :=
  Abelian.comp_epiDesc _ _ _

instance epi_pullbackImHom : Epi (h.pullbackImHom f hf) :=
  epi_of_epi_fac (h.map_eigenImπ_pullbackImHom f hf)

variable [Mono (cartierDualToBidual ((Scheme.Modules.pullback f).obj F))]

theorem pullbackImHom_comp : h.pullbackImHom f hf ≫ (h.pullback f).imToSub ≫ eigenι _ _ ≫
    (Scheme.Modules.pullback f).map (eigenImπ ρ σ) = (f.appTop D : Γ(Y, ⊤)) • 𝟙 _ := by
  rw [← cancel_epi ((Scheme.Modules.pullback f).map (eigenImπ ρ σ)),
    map_eigenImπ_pullbackImHom_assoc, eigenImπ_imToSub_ι_assoc, ← Functor.map_comp,
    h.comp_eq_smul (act_eigenImπ ρ σ), pullback_map_smul, Linear.comp_smul, Category.comp_id]

theorem pullbackImHom_app_eq_zero_iff {V : Y.Opens}
    {s : Γ((Scheme.Modules.pullback f).obj (eigenIm ρ σ), V)} :
    (h.pullbackImHom f hf).app V s = 0 ↔ resG Y (le_top : V ≤ ⊤) (f.appTop D) • s = 0 := by
  refine ⟨fun e => ?_, fun e => hf.eq_zero_of_smul ?_⟩
  · refine congr(($(h.pullbackImHom_comp f hf)).app V s).symm.trans ?_
    exact (congrArg (((h.pullback f).imToSub ≫ eigenι _ _ ≫
      (Scheme.Modules.pullback f).map (eigenImπ ρ σ)).app V) e).trans (map_zero _)
  · rw [← Scheme.Modules.Hom.app_smul, e, map_zero]

theorem isIso_pullbackImHom {r : ℕ} (hr : IsVB (eigenIm ρ σ) r) : IsIso (h.pullbackImHom f hf) :=
  have := mono_toBidual_of_isVectorBundle (hr.pullback f)
  have : Mono (h.pullbackImHom f hf) := Preadditive.mono_of_cancel_zero _ fun g hg =>
    hf.hom_eq_zero (by rw [← Category.comp_id g, ← Linear.comp_smul, ← h.pullbackImHom_comp f hf,
      reassoc_of% hg, zero_comp])
  isIso_of_mono_of_epi _

end IsEigenProj

end Proj

section Examples₂

open Polynomial

variable (F G)

def twoAct : ℤ[X] →+* End (F ⊞ G) :=
  eval₂RingHom' (Int.castRingHom _) (2 • (biprod.snd ≫ biprod.inr : F ⊞ G ⟶ F ⊞ G))
    fun n => Int.cast_commute n _

variable (X) in

def zeroChar : ℤ[X] →+* Γ(X, ⊤) := (Int.castRingHom _).comp constantCoeff

theorem act_twoAct_X : act (twoAct F G) Polynomial.X = 2 • (biprod.snd ≫ biprod.inr) :=
  eval₂_X (S := End (F ⊞ G)) _ _

variable {F G} in

theorem act_comp_of_X {ρ : ℤ[X] →+* End F} {φ : F ⟶ G} (h : act ρ Polynomial.X ≫ φ = 0)
    (a : ℤ[X]) : act ρ a ≫ φ = zeroChar X a • φ := by
  have e : act ρ a = act ρ a.divX ≫ act ρ Polynomial.X + smulHom F (zeroChar X a) := by
    conv_lhs => rw [← X_mul_divX_add a, act, map_add, map_mul]
    exact congrArg _ congr($(RingHom.ext_int (ρ.comp C) (scalarAct F (Int.castRingHom _)))
      (a.coeff 0))
  rw [e, Preadditive.add_comp, Category.assoc, h, Limits.comp_zero, zero_add, smulHom_comp]
  rfl

theorem isEigenProj_twoAct :
    IsEigenProj (twoAct F G) (zeroChar X) (2 • (biprod.fst ≫ biprod.inl)) 2 where
  act_comp := act_comp_of_X (by simp [act_twoAct_X])
  exists_sum := ⟨2, ![2, -1], ![1, Polynomial.X], by
    have e : act (twoAct F G) 1 = 𝟙 _ := map_one (twoAct F G)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, act_twoAct_X, e,
      two_smul, neg_smul, one_smul, ← biprod.total]
    abel, by simp [zeroChar]⟩

def eigenImTwoIso [Mono (cartierDualToBidual F)] (h : IsRegularFn (2 : Γ(X, ⊤))) :
    eigenIm (twoAct F G) (zeroChar X) ≅ F where
  hom := eigenImDesc biprod.fst (act_comp_of_X (by simp [act_twoAct_X]))
  inv := biprod.inl ≫ eigenImπ _ _
  hom_inv_id := by
    have := (isEigenProj_twoAct F G).comp_eigenImπ_eq_zero h (k := biprod.inr) (by simp)
    rw [← cancel_epi (eigenImπ _ _), eigenImπ_desc_assoc, Category.comp_id]
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [this]
  inv_hom_id := by simp

theorem actsThrough_pull_twoAct (f : Y ⟶ X) (hY : (2 : Γ(Y, ⊤)) = 0) :
    ActsThrough (pullAct (twoAct F G) f) (f.appTop.hom.comp (zeroChar X)) := fun a => by
  have := act_comp_of_X (ρ := pullAct (twoAct F G) f) (φ := 𝟙 _) (by
    rw [act_pullAct, act_twoAct_X, Functor.map_nsmul, Category.comp_id,
      ← Nat.cast_smul_eq_nsmul Γ(Y, ⊤), Nat.cast_ofNat, hY, zero_smul]) a
  rw [Category.comp_id] at this
  rw [this, smulHom_eq_smul_id]
  simp [zeroChar]

variable {F G} in

theorem not_isIso_quotToIm_twoAct {r s : ℕ} (hF : IsVB F r) (hG : IsVB G (s + 1))
    (h : IsRegularFn (2 : Γ(X, ⊤))) (f : Y ⟶ X) [Nonempty Y] (hY : (2 : Γ(Y, ⊤)) = 0) :
    ¬IsIso (quotToIm (twoAct F G) (zeroChar X)) := fun _ => by
  have := mono_toBidual_of_isVectorBundle hF
  have := isIso_eigenπ_of_actsThrough (actsThrough_pull_twoAct F G f hY)
  have h₁ := ((hF.of_iso (asIso (quotToIm _ _) ≪≫ eigenImTwoIso F G h).symm).pullback f).of_iso
    (asIso (eigenπ _ _) ≪≫ pullbackQuotIso _ _ f).symm
  have := h₁.rank_unique ((hF.biprod hG).pullback f)
  omega

example : let L := structureModule (Spec (.of ℤ))
    IsVB (eigenIm (twoAct L L) (zeroChar _)) 1 ∧ ¬IsIso (quotToIm (twoAct L L) (zeroChar _)) := by
  intro L
  have hL : IsVB L 1 := (isFrame_one ⊤).isVB
  have := mono_toBidual_of_isVectorBundle hL
  have h : IsRegularFn (2 : Γ(Spec (.of ℤ), ⊤)) := isRegularFn_of_ne_zero fun e => by
    have := congrArg (Scheme.ΓSpecIso (.of ℤ)).hom.hom e
    rw [map_ofNat, map_zero] at this
    exact absurd (show (2 : ℤ) = 0 from this) (by decide)
  refine ⟨hL.of_iso (eigenImTwoIso L L h).symm, not_isIso_quotToIm_twoAct hL hL h
    (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 2)))) ?_⟩
  exact (map_ofNat (Scheme.ΓSpecIso (.of (ZMod 2))).inv.hom 2).symm.trans (map_zero _)

end Examples₂

end GlobalTheory.LieVB
