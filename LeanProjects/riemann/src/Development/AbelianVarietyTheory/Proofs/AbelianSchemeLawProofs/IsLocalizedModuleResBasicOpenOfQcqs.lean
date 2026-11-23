import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijectiveToPushforwardComp

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
namespace GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

namespace SecOn

open GlobalTheory.LB

variable {M : LB X} {V W : X.Opens}

variable (M) in

def resBasicOpen (a : Γ(X, V)) : SecOn M V →ₗ[Γ(X, V)] SecOn M (X.basicOpen a) :=
  QCoh.resBasicOpen (toMod M) a

@[simp] theorem resBasicOpen_apply (a : Γ(X, V)) (s : SecOn M V) :
    resBasicOpen M a s = restrict M (X.basicOpen_le a) s := rfl

theorem smul_basicOpen_def (a b : Γ(X, V)) (s : SecOn M (X.basicOpen a)) :
    b • s = rs X (X.basicOpen_le a) b • s := rfl

theorem isLocalizedModule_resBasicOpen_of_qcqs (hM : M.IsLB) (hV : IsCompact (V : Set X))
    (hV' : IsQuasiSeparated (V : Set X)) (a : Γ(X, V)) :
    IsLocalizedModule.Away a (resBasicOpen M a) :=
  haveI := isQuasicoherent_toMod hM
  QCoh.Qcqs.isLocalizedModule_resBasicOpen_of_qcqs (toMod M) hV hV' a

theorem isLocalizedModule_resBasicOpen (hM : M.IsLB) (hV : IsAffineOpen V) (a : Γ(X, V)) :
    IsLocalizedModule.Away a (resBasicOpen M a) :=
  isLocalizedModule_resBasicOpen_of_qcqs hM hV.isCompact hV.isQuasiSeparated a

theorem exists_pow_smul_eq_zero (hM : M.IsLB) (hV : IsCompact (V : Set X)) (a : Γ(X, V))
    (h : W ≤ V) (hW : W = X.basicOpen a) (t : SecOn M V) (ht : restrict M h t = 0) :
    ∃ n : ℕ, a ^ n • t = 0 :=
  haveI := isQuasicoherent_toMod hM
  QCoh.Qcqs.exists_pow_smul_eq_zero_of_isCompact (toMod M) hV a h hW t ht

theorem exists_pow_smul_eq_restrict (hM : M.IsLB) (hV : IsCompact (V : Set X))
    (hV' : IsQuasiSeparated (V : Set X)) (a : Γ(X, V)) (h : W ≤ V) (hW : W = X.basicOpen a)
    (s : SecOn M W) : ∃ (n : ℕ) (t : SecOn M V), rs X h a ^ n • s = restrict M h t :=
  haveI := isQuasicoherent_toMod hM
  QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs (toMod M) hV hV' a h hW s

theorem isLocalizedModule_of_ringHom (hM : M.IsLB) (hV : IsCompact (V : Set X))
    (hV' : IsQuasiSeparated (V : Set X)) {A : Type*} [CommRing A] (φ : A →+* Γ(X, V)) (a : A)
    (h : W ≤ V) (hW : W = X.basicOpen (φ a)) [Module A (SecOn M V)] [Module A (SecOn M W)]
    (hsV : ∀ (r : A) (s : SecOn M V), r • s = φ r • s)
    (hsW : ∀ (r : A) (s : SecOn M W), r • s = rs X h (φ r) • s)
    (l : SecOn M V →ₗ[A] SecOn M W) (hl : ∀ s, l s = restrict M h s) :
    IsLocalizedModule.Away a l :=
  haveI := isQuasicoherent_toMod hM
  QCoh.Qcqs.isLocalizedModule_of_ringHom_of_qcqs (toMod M) hV hV' φ a h hW hsV hsW l hl

theorem isBaseChange_restrict (hM : M.IsLB) (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V)
    [Algebra Γ(X, V) Γ(X, W)] [Module Γ(X, V) (SecOn M W)]
    [IsScalarTower Γ(X, V) Γ(X, W) (SecOn M W)]
    (halg : ∀ r, algebraMap Γ(X, V) Γ(X, W) r = rs X h r)
    (l : SecOn M V →ₗ[Γ(X, V)] SecOn M W) (hl : ∀ s, l s = restrict M h s) :
    IsBaseChange Γ(X, W) l :=
  haveI := isQuasicoherent_toMod hM
  QCoh.isBaseChange_of_eq_res (toMod M) hV hW h halg l hl

theorem invertible (hM : M.IsLB) (hV : IsAffineOpen V) : Module.Invertible Γ(X, V) (SecOn M V) :=
  invertible_sections hM hV

theorem finite (hM : M.IsLB) (hV : IsAffineOpen V) : Module.Finite Γ(X, V) (SecOn M V) :=
  haveI := invertible hM hV
  inferInstance

theorem projective (hM : M.IsLB) (hV : IsAffineOpen V) : Module.Projective Γ(X, V) (SecOn M V) :=
  haveI := invertible hM hV
  inferInstance

theorem finitePresentation (hM : M.IsLB) (hV : IsAffineOpen V) :
    Module.FinitePresentation Γ(X, V) (SecOn M V) :=
  haveI := invertible hM hV
  Module.finitePresentation_of_projective _ _

theorem flat (hM : M.IsLB) (hV : IsAffineOpen V) : Module.Flat Γ(X, V) (SecOn M V) :=
  haveI := invertible hM hV
  inferInstance

theorem isBaseChange_pullLE (hM : M.IsLB) (π : X' ⟶ X) {V' : X'.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (e : V' ≤ π ⁻¹ᵁ V) [Algebra Γ(X, V) Γ(X', V')]
    [Module Γ(X, V) (SecOn (M.pull π) V')]
    [IsScalarTower Γ(X, V) Γ(X', V') (SecOn (M.pull π) V')]
    (halg : ∀ r, algebraMap Γ(X, V) Γ(X', V') r = (π.appLE V V' e).hom r)
    (l : SecOn M V →ₗ[Γ(X, V)] SecOn (M.pull π) V') (hl : ∀ s, l s = pullLE M π V V' e s) :
    IsBaseChange Γ(X', V') l := by
  haveI := isQuasicoherent_toMod hM
  letI : Module Γ(X, V) Γ((Scheme.Modules.pullback π).obj (toMod M), V') :=
    Module.compHom _ (algebraMap Γ(X, V) Γ(X', V'))
  haveI : IsScalarTower Γ(X, V) Γ(X', V') Γ((Scheme.Modules.pullback π).obj (toMod M), V') :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have h := QCoh.isBaseChange_of_eq_pullbackSections π (toMod M) hV' hV e halg
    { toFun := QCoh.pullbackSections π (toMod M) e
      map_add' s t := by
        letI := QCoh.appLEModule π ((Scheme.Modules.pullback π).obj (toMod M)) e
        exact (QCoh.pullbackSections π (toMod M) e).map_add s t
      map_smul' r s := by
        rw [QCoh.pullbackSections_smul]
        exact congrArg (· • QCoh.pullbackSections π (toMod M) e s) (halg r).symm } fun _ ↦ rfl
  refine IsBaseChange.of_equiv (h.equiv ≪≫ₗ appLinearEquiv (pullbackIso hM π) V') fun s => ?_
  rw [LinearEquiv.trans_apply, IsBaseChange.equiv_tmul, one_smul, appLinearEquiv_apply, hl]
  refine (app_map (pullbackHom M π) e _).trans ?_
  exact congrArg (restrict (M.pull π) e) congr(($(unit_comp_pullbackHom M π)).app V s)

end SecOn

theorem cst_eq_appLE (f : X ⟶ Spec (CommRingCat.of R)) (V : X.Opens) :
    CommRingCat.ofHom (cst f V) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V le_top := rfl

theorem flat_cst (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] {V : X.Opens} (hV : IsAffineOpen V) :
    (cst f V).Flat :=
  show ((f.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Flat from
  RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv))
    (f.flat_appLE (isAffineOpen_top _) hV le_top)

section Pullback

variable {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R')} {π : X' ⟶ X}
  {g : R →+* R'}

theorem isAffineOpen_preimage_of_isPullback
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) {V : X.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (π ⁻¹ᵁ V) :=
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  hV.preimage π

theorem isPushout_cst (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) {V : X.Opens}
    (hV : IsAffineOpen V) {V' : X'.Opens} (e : V' = π ⁻¹ᵁ V) :
    IsPushout (CommRingCat.ofHom g) (CommRingCat.ofHom (cst f V))
      (CommRingCat.ofHom (cst f' V')) (π.appLE V V' e.le) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := V') le_top
    le_top (by simp [e])).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  refine po.flip.of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [cst_eq_appLE]
  · simp [cst_eq_appLE]
  · simp

end Pullback

namespace SecOnR

variable (f : X ⟶ Spec (CommRingCat.of R)) {M : LB X} {V W : X.Opens}

theorem isLocalizedModule_restrict (hM : M.IsLB) (hV : IsCompact (V : Set X))
    (hV' : IsQuasiSeparated (V : Set X)) (r : R) (h : W ≤ V) (hW : W = X.basicOpen (cst f V r)) :
    IsLocalizedModule.Away r (restrict f M h) :=
  letI : Module R (SecOn M V) := inferInstanceAs (Module R (SecOnR f M V))
  letI : Module R (SecOn M W) := inferInstanceAs (Module R (SecOnR f M W))
  SecOn.isLocalizedModule_of_ringHom hM hV hV' (cst f V) r h hW (fun _ _ => rfl)
    (fun a s => congrArg (· • s) (rs_cst f h a).symm) (restrict f M h) fun _ => rfl

theorem invertible (hM : M.IsLB) (hV : IsAffineOpen V) :
    Module.Invertible Γ(X, V) (SecOnR f M V) := SecOn.invertible hM hV

theorem flat_of_flat_cst (hM : M.IsLB) (hV : IsAffineOpen V) (hf : (cst f V).Flat) :
    Module.Flat R (SecOnR f M V) :=
  letI := cstAlgebra f V
  haveI : Module.Flat R Γ(X, V) := hf
  haveI : Module.Flat Γ(X, V) (SecOnR f M V) := SecOn.flat hM hV
  Module.Flat.trans R Γ(X, V) _

theorem flat [Flat f] (hM : M.IsLB) (hV : IsAffineOpen V) : Module.Flat R (SecOnR f M V) :=
  flat_of_flat_cst f hM hV (flat_cst f hV)

section BaseChange

variable {f} [Algebra R R'] {f' : X' ⟶ Spec (CommRingCat.of R')} {π : X' ⟶ X}

theorem isBaseChange_pull (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (hV : IsAffineOpen V)
    {V' : X'.Opens} (e : V' = π ⁻¹ᵁ V) [Module R (SecOnR f' (M.pull π) V')]
    [IsScalarTower R R' (SecOnR f' (M.pull π) V')]
    (l : SecOnR f M V →ₗ[R] SecOnR f' (M.pull π) V') (hl : ∀ s, l s = pull M H.w V V' e.le s) :
    IsBaseChange R' l := by
  letI := cstAlgebra f V
  letI := cstAlgebra f' V'
  letI : Algebra Γ(X, V) Γ(X', V') := (π.appLE V V' e.le).hom.toAlgebra
  letI : Algebra R Γ(X', V') := ((cst f' V').comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' Γ(X', V') := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R Γ(X, V) Γ(X', V') :=
    .of_algebraMap_eq fun r => (appLE_cst H.w e.le r).symm
  haveI : Algebra.IsPushout R R' Γ(X, V) Γ(X', V') :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_cst H hV e)
  letI : Module Γ(X, V) (SecOn (M.pull π) V') := Module.compHom _ (π.appLE V V' e.le).hom
  haveI : IsScalarTower Γ(X, V) Γ(X', V') (SecOn (M.pull π) V') :=
    .of_algebraMap_smul fun _ _ => rfl
  have h := SecOn.isBaseChange_pullLE hM π hV (e ▸ isAffineOpen_preimage_of_isPullback H hV) e.le
    (fun _ => rfl)
    { toFun := SecOn.pullLE M π V V' e.le
      map_add' := map_add _
      map_smul' := (SecOn.pullLE M π V V' e.le).map_smulₛₗ } fun _ => rfl
  let E : Γ(X', V') ⊗[Γ(X, V)] SecOnR f M V ≃ₗ[Γ(X', V')] SecOnR f' (M.pull π) V' := h.equiv
  have hE (s : SecOnR f M V) : E (1 ⊗ₜ s) = pull M H.w V V' e.le s :=
    (h.equiv_tmul 1 s).trans (one_smul _ _)
  refine IsBaseChange.of_equiv
    ((Algebra.IsPushout.cancelBaseChange R R' Γ(X, V) Γ(X', V') (SecOnR f M V)).symm ≪≫ₗ
      E.restrictScalars R') fun s => ?_
  simp [hl, hE]

variable (M) in

def baseChangeHom (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (V : X.Opens) (V' : X'.Opens) (e : V' ≤ π ⁻¹ᵁ V) :
    R' ⊗[R] SecOnR f M V →ₗ[R'] SecOnR f' (M.pull π) V' :=
  letI : Module R (SecOnR f' (M.pull π) V') := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' (SecOnR f' (M.pull π) V') := .of_algebraMap_smul fun _ _ => rfl
  LinearMap.liftBaseChange R'
    { toFun := pull M w V V' e
      map_add' := map_add _
      map_smul' := (pull M w V V' e).map_smulₛₗ }

@[simp] theorem baseChangeHom_tmul
    (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) {V' : X'.Opens}
    (e : V' ≤ π ⁻¹ᵁ V) (c : R') (s : SecOnR f M V) :
    baseChangeHom M w V V' e (c ⊗ₜ s) = c • pull M w V V' e s := rfl

theorem baseChangeHom_restrict
    (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) {V' W' : X'.Opens}
    (h : W ≤ V) (h' : W' ≤ V') (e : V' ≤ π ⁻¹ᵁ V) (e' : W' ≤ π ⁻¹ᵁ W)
    (x : R' ⊗[R] SecOnR f M V) :
    baseChangeHom M w W W' e' ((restrict f M h).baseChange R' x) =
      restrict f' _ h' (baseChangeHom M w V V' e x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c s =>
    rw [LinearMap.baseChange_tmul, baseChangeHom_tmul, baseChangeHom_tmul, map_smul,
      pull_restrict w h h' e e']

theorem baseChangeHom_bijective (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (hV : IsAffineOpen V)
    {V' : X'.Opens} (e : V' = π ⁻¹ᵁ V) :
    Function.Bijective (baseChangeHom M H.w V V' e.le) := by
  letI : Module R (SecOnR f' (M.pull π) V') := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' (SecOnR f' (M.pull π) V') := .of_algebraMap_smul fun _ _ => rfl
  have h := isBaseChange_pull hM H hV e
    { toFun := pull M H.w V V' e.le
      map_add' := map_add _
      map_smul' := (pull M H.w V V' e.le).map_smulₛₗ } fun _ => rfl
  have E : h.equiv.toLinearMap = baseChangeHom M H.w V V' e.le :=
    TensorProduct.AlgebraTensorModule.ext fun c s => h.equiv_tmul c s
  exact E ▸ h.equiv.bijective

def baseChangeEquiv (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (hV : IsAffineOpen V)
    {V' : X'.Opens} (e : V' = π ⁻¹ᵁ V) :
    R' ⊗[R] SecOnR f M V ≃ₗ[R'] SecOnR f' (M.pull π) V' :=
  LinearEquiv.ofBijective _ (baseChangeHom_bijective hM H hV e)

@[simp] theorem baseChangeEquiv_tmul (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (hV : IsAffineOpen V)
    {V' : X'.Opens} (e : V' = π ⁻¹ᵁ V) (c : R') (s : SecOnR f M V) :
    baseChangeEquiv hM H hV e (c ⊗ₜ s) = c • pull M H.w V V' e.le s := rfl

end BaseChange

end SecOnR

section Cech

variable {κ : Type} {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R')}
  {π : X' ⟶ X} (M : LB X) (D : κ → X.Opens)

variable {M D} in

theorem flat_cechLB_X [LinearOrder κ] [Finite κ] (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    (hM : M.IsLB) (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) (p : ℕ) :
    Module.Flat R ((cechLB f M D).X p) :=
  GlobalTheory.Cube.flat_term (secCube f M D) (p + 1) fun s hs =>
    SecOnR.flat f hM (hD s (Finset.card_pos.1 (by omega)))

section Alg

variable [Algebra R R']

def secCubeBaseChange (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) :
    GlobalTheory.Cube.baseChange R' (secCube f M D) ⟶ secCube f' (M.pull π) fun i => π ⁻¹ᵁ D i :=
  GlobalTheory.Cube.homMk (fun s => SecOnR.baseChangeHom M w _ _ (preimage_biInf D π s).ge)
    fun {s t} h x => SecOnR.baseChangeHom_restrict w (iInf_le_iInf_of_subset D h)
      (iInf_le_iInf_of_subset (fun i => π ⁻¹ᵁ D i) h) (preimage_biInf D π s).ge
      (preimage_biInf D π t).ge x

theorem secCubeBaseChange_app_tmul
    (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (s : Finset κ) (c : R')
    (x : (secCube f M D).obj s) :
    ((secCubeBaseChange M D w).app s).hom (c ⊗ₜ[R] x) = c • secCubePull M D w s x := rfl

variable {M} in

theorem secCubeBaseChange_app_bijective (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) {s : Finset κ}
    (hs : IsAffineOpen (⨅ i ∈ s, D i)) :
    Function.Bijective ((secCubeBaseChange M D H.w).app s).hom :=
  SecOnR.baseChangeHom_bijective hM H hs (preimage_biInf D π s).symm

def secTermBaseChange (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (p : ℕ) :
    R' ⊗[R] GlobalTheory.Cube.Term (secCube f M D) p →ₗ[R']
      GlobalTheory.Cube.Term (secCube f' (M.pull π) fun i => π ⁻¹ᵁ D i) p :=
  GlobalTheory.Cube.termMap (secCubeBaseChange M D w) p ∘ₗ GlobalTheory.Cube.termBaseChange R' (secCube f M D) p

theorem secTermBaseChange_tmul (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (p : ℕ) (c : R') (x : GlobalTheory.Cube.Term (secCube f M D) p) (s : {s : Finset κ // s.card = p}) :
    secTermBaseChange M D w p (c ⊗ₜ[R] x) s = c • secCubePull M D w s.1 (x s) := rfl

theorem d_secTermBaseChange [LinearOrder κ]
    (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (p : ℕ)
    (x : R' ⊗[R] GlobalTheory.Cube.Term (secCube f M D) p) :
    GlobalTheory.Cube.d _ p (secTermBaseChange M D w p x) =
      secTermBaseChange M D w (p + 1) ((GlobalTheory.Cube.d (secCube f M D) p).baseChange R' x) :=
  (GlobalTheory.Cube.termMap_d (secCubeBaseChange M D w) p _).symm.trans
    (congrArg (GlobalTheory.Cube.termMap (secCubeBaseChange M D w) (p + 1))
      (GlobalTheory.Cube.d_termBaseChange R' (secCube f M D) p x))

variable {M D} in

theorem secTermBaseChange_bijective [Finite κ] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (p : ℕ)
    (hD : ∀ s : Finset κ, s.card = p → IsAffineOpen (⨅ i ∈ s, D i)) :
    Function.Bijective (secTermBaseChange M D H.w p) :=
  (Function.Bijective.piMap fun s : {s : Finset κ // s.card = p} =>
    secCubeBaseChange_app_bijective D hM H (hD s.1 s.2)).comp
    (GlobalTheory.Cube.termBaseChange_bijective R' (secCube f M D) p)

end Alg

variable {g : R →+* R'}

def secCubeExtendScalars (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) :
    secCube f M D ⋙ ModuleCat.extendScalars g ⟶ secCube f' (M.pull π) fun i => π ⁻¹ᵁ D i :=
  letI := g.toAlgebra
  secCubeBaseChange M D w

def cechLBBaseChange [LinearOrder κ] (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) :
    ((ModuleCat.extendScalars g).mapHomologicalComplex _).obj (cechLB f M D) ⟶
      cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i :=
  cechComparison (ModuleCat.extendScalars g) (secCube f M D) ≫
    cechComplexMap (secCubeExtendScalars M D w)

open ChangeOfRings in

theorem cechLBBaseChange_f_tmul [LinearOrder κ] (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g))
    (p : ℕ) (c : R') (x : (cechLB f M D).X p) (s : {s : Finset κ // s.card = p + 1}) :
    ((cechLBBaseChange M D w).f p).hom (c ⊗ₜ[R,g] x) s = c • secCubePull M D w s.1 (x s) := rfl

variable {M D}

theorem isIso_cechLBBaseChange [LinearOrder κ] [Finite κ] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) :
    IsIso (cechLBBaseChange M D H.w) :=
  letI := g.toAlgebra
  haveI : IsIso (cechComplexMap (secCubeExtendScalars M D H.w)) :=
    isIso_cechComplexMap _ fun s hs => secCubeBaseChange_app_bijective D hM H (hD s hs)
  inferInstanceAs (IsIso (cechComparison (ModuleCat.extendScalars g) (secCube f M D) ≫
    cechComplexMap (secCubeExtendScalars M D H.w)))

def cechLBBaseChangeIso [LinearOrder κ] [Finite κ] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) :
    ((ModuleCat.extendScalars g).mapHomologicalComplex _).obj (cechLB f M D) ≅
      cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i :=
  haveI := isIso_cechLBBaseChange hM H hD
  asIso (cechLBBaseChange M D H.w)

@[simp] theorem cechLBBaseChangeIso_hom [LinearOrder κ] [Finite κ] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) :
    (cechLBBaseChangeIso hM H hD).hom = cechLBBaseChange M D H.w := rfl

theorem isAffineOpen_biInf_preimage (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {s : Finset κ} (hs : IsAffineOpen (⨅ i ∈ s, D i)) : IsAffineOpen (⨅ i ∈ s, π ⁻¹ᵁ D i) :=
  preimage_biInf D π s ▸ isAffineOpen_preimage_of_isPullback H hs

end Cech

theorem sections_over_affine_open {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) :
    (∀ V : X.Opens, IsCompact (V : Set X) → IsQuasiSeparated (V : Set X) → ∀ a : Γ(X, V),
      IsLocalizedModule.Away a (SecOn.resBasicOpen M a)) ∧
    (∀ V : X.Opens, IsAffineOpen V → ∀ a : Γ(X, V),
      IsLocalizedModule.Away a (SecOn.resBasicOpen M a)) ∧
    (∀ V : X.Opens, IsAffineOpen V → Module.Invertible Γ(X, V) (SecOn M V) ∧
      Module.FinitePresentation Γ(X, V) (SecOn M V) ∧ Module.Projective Γ(X, V) (SecOn M V)) ∧
    (∀ (R : Type) [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)), Flat f →
      ∀ V : X.Opens, IsAffineOpen V → Module.Flat R (SecOnR f M V)) ∧
    (∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (π : X' ⟶ X)
      (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R'))
      (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (V : X.Opens),
      IsAffineOpen V → Function.Bijective (SecOnR.baseChangeHom M H.w V (π ⁻¹ᵁ V) le_rfl)) ∧
    (∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
      (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R'))
      (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
      (κ : Type) [LinearOrder κ] [Finite κ] (D : κ → X.Opens),
      (∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) →
        IsIso (cechLBBaseChange M D H.w)) :=
  ⟨fun _ => SecOn.isLocalizedModule_resBasicOpen_of_qcqs hM,
    fun _ => SecOn.isLocalizedModule_resBasicOpen hM,
    fun _ hV => ⟨SecOn.invertible hM hV, SecOn.finitePresentation hM hV, SecOn.projective hM hV⟩,
    fun _ _ f _ _ hV => SecOnR.flat f hM hV,
    fun _ _ _ _ _ _ _ _ _ H _ hV => SecOnR.baseChangeHom_bijective hM H hV rfl,
    fun _ _ _ _ _ _ _ _ _ H _ _ _ _ hD => isIso_cechLBBaseChange hM H hD⟩

end GlobalTheory.AbLaw
