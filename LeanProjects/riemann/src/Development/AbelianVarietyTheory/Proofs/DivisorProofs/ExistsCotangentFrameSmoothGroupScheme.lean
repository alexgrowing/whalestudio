import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.VB GlobalTheory.Conormal

namespace GlobalTheory.ConormalFrame

theorem sub_isLocalizedModule {X : Scheme.{0}} {F : X.Modules} [F.IsQuasicoherent] (N : Sub F)
    {U : X.Opens} (hU : IsAffineOpen U)
    (h : ∀ (f : Γ(X, U)) (t : Γ(F, U)),
      GlobalTheory.Twist.resM F (X.basicOpen_le f) t ∈ N.sec _ → ∃ n : ℕ, f ^ n • t ∈ N.sec U)
    (f : Γ(X, U)) : IsLocalizedModule.Away f (GlobalTheory.QCoh.resBasicOpen N.toMod f) := by
  refine (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff _ f).2 ⟨fun s => ?_, fun t ht => ?_⟩
  · obtain ⟨n, t, e⟩ := GlobalTheory.QCoh.exists_pow_smul_eq_res F hU f (X.basicOpen_le f) rfl
      (N.incl.app _ s)
    obtain ⟨m, hm⟩ := h f t (by
      change F.presheaf.map _ t ∈ _
      rw [← e]
      exact (N.sec _).smul_mem _ (N.incl_app_mem s))
    refine ⟨m + n, N.mkSec _ hm, N.incl_app_injective _ ?_⟩
    rw [Scheme.Modules.Hom.app_smul, GlobalTheory.QCoh.app_res, Sub.incl_app_mkSec, Scheme.Modules.map_smul,
      ← e, pow_add, mul_smul, map_pow]
  · obtain ⟨n, e⟩ := GlobalTheory.QCoh.exists_pow_smul_eq_zero F hU f (X.basicOpen_le f) rfl
      (N.incl.app _ t) (by rw [← GlobalTheory.QCoh.app_res, ht, map_zero])
    exact ⟨n, N.incl_app_injective _ (by rw [Scheme.Modules.Hom.app_smul, e, map_zero])⟩

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}

include he in

theorem preimage_eq (c : IsChart π e U W) : e ⁻¹ᵁ W = U :=
  le_antisymm ((le_preimage_iff he).1 (e.preimage_mono c.le_base)) c.le

include he in

theorem isQuasicoherent_restrict_ideal (c : IsChart π e U W) :
    ((ideal e).restrict c.affine.fromSpec).IsQuasicoherent := by
  have := (isVB_structureModule X).isQuasicoherent
  refine (GlobalTheory.QCoh.isQuasicoherent_restrict_fromSpec_iff _ c.affine).2
    (sub_isLocalizedModule _ c.affine fun f (t : Γ(X, W)) ht => ?_)
  have hcpt : IsCompact ((e ⁻¹ᵁ W : S.Opens) : Set S) := by
    rw [preimage_eq he c]; exact c.affine_base.isCompact
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact S
    (U := e ⁻¹ᵁ W) hcpt (e.appLE W _ le_rfl t) (e.appLE W _ le_rfl f) (by
      have hle : S.basicOpen (e.appLE W _ le_rfl f) ≤ e ⁻¹ᵁ X.basicOpen f := by
        rw [Scheme.Hom.appLE_eq_app, e.preimage_basicOpen]
      have := congrArg (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG S hle)
        (show e.appLE _ _ le_rfl (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X (X.basicOpen_le f) t) = 0 from ht)
      rw [GlobalTheory.DualPull.resG_appLE, GlobalTheory.DualPull.appLE_resG, map_zero] at this
      exact (GlobalTheory.DualPull.resG_appLE e _ _ _).trans this)
  refine ⟨n, ?_⟩
  change e.appLE W _ le_rfl (f ^ n * t) = 0
  rw [map_mul, map_pow, hn]

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}

include he in

theorem isQuasicoherent_conormal : (conormal e).IsQuasicoherent := by
  refine GlobalTheory.QCoh.isQuasicoherent_of_forall_exists_affine _ fun x => ?_
  obtain ⟨U, W, hx, -, c⟩ := exists_isChart he (x := x) (V := ⊤) trivial
  have := isQuasicoherent_restrict_ideal he c
  refine ⟨U, c.affine_base, hx,
    (GlobalTheory.QCoh.isQuasicoherent_restrict_fromSpec_iff _ c.affine_base).mp ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec Γ(S, U)).ringCatSheaf).prop_of_iso
    ((GlobalTheory.QCoh.restrictPullbackIso
      (IsAffineOpen.SpecMap_appLE_fromSpec e c.affine c.affine_base c.le)).app (ideal e))
    (GlobalTheory.QCoh.isQuasicoherent_pullback_Spec (e.appLE W U c.le) ((ideal e).restrict c.affine.fromSpec))

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

open GlobalTheory.QCoh

set_option backward.isDefEq.respectTransparency false in

theorem isBaseChange_pullbackSections {X Y : Scheme.{0}} (f : X ⟶ Y) (G : Y.Modules)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    [(G.restrict hV.fromSpec).IsQuasicoherent] (e : U ≤ f ⁻¹ᵁ V) :
    letI := appLEAlgebra f e
    letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
    haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
    IsBaseChange Γ(X, U) (pullbackSections f G e) := by
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  obtain ⟨a, ha⟩ := exists_equiv_pullback_Spec (f.appLE V U e) (G.restrict hV.fromSpec)
  have w := IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e
  let κ : Γ((Scheme.Modules.pullback (Spec.map (f.appLE V U e))).obj (G.restrict hV.fromSpec), ⊤)
      ≃ₗ[Γ(X, U)] Γ(((Scheme.Modules.pullback f).obj G).restrict hU.fromSpec, ⊤) :=
    (moduleSpecΓFunctor.mapIso ((restrictPullbackIso w).app G)).toLinearEquiv
  refine IsBaseChange.of_equiv
    ((sectionsEquivFromSpec G hV).baseChange Γ(Y, V) Γ(X, U) _ _ ≪≫ₗ a ≪≫ₗ κ ≪≫ₗ
      (sectionsEquivFromSpec _ hU).symm) fun s ↦ ?_
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_eq, LinearEquiv.baseChange_tmul, ha, sectionsEquivFromSpec_apply,
    sectionsEquivFromSpec_apply, res_pullbackSections]
  refine Eq.trans ?_ (restrictPullbackIso_hom_app_pullbackSections w G (V' := ⊤) (U' := ⊤)
    (fromSpec_image_le hV ⊤) le_rfl _ s)
  exact congr(κ $(res_self _ le_rfl _)).symm

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}

theorem ofAugCot_bijective (c : IsChart π e U W) : Function.Bijective (c.ofAugCot he) := by
  letI := c.algebra
  letI := GlobalTheory.QCoh.appLEAlgebra e c.le
  letI := GlobalTheory.QCoh.appLEModule e ((Scheme.Modules.pullback e).obj (ideal e)) c.le
  haveI := GlobalTheory.QCoh.appLE_isScalarTower e ((Scheme.Modules.pullback e).obj (ideal e)) c.le
  haveI := AugCot.isScalarTower_of_algebraMap_eq (c.aug he) fun _ => rfl
  haveI := isQuasicoherent_restrict_ideal he c
  have hb := isBaseChange_pullbackSections e (ideal e) c.affine_base c.affine c.le
  let g : Γ(ideal e, W) →ₗ[Γ(X, W)] AugCot (c.aug he) := (RingHom.ker (c.aug he)).toCotangent ∘ₗ
    (GlobalTheory.QCoh.appLinear (idealSub e).incl W).codRestrict (RingHom.ker (c.aug he)) fun s =>
      (c.aug_eq_zero_iff he).2 ((idealSub e).incl_app_mem s)
  have key (x : RingHom.ker (c.aug he)) : c.ofAugCot he ((RingHom.ker (c.aug he)).toCotangent x) =
      cls c.le x ((c.aug_eq_zero_iff he).1 x.2) := d_eq_cls he _ _ _
  refine Function.bijective_iff_has_inverse.2 ⟨hb.lift g, fun x => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := (RingHom.ker (c.aug he)).toCotangent_surjective x
    rw [key]
    exact hb.lift_eq g _
  · refine hb.inductionOn y (fun y => c.ofAugCot he (hb.lift g y) = y)
      (by rw [map_zero, map_zero]; rfl) (fun s => ?_) (fun r y hy => ?_) fun y z hy hz => ?_
    · rw [hb.lift_eq]
      exact key _
    · rw [map_smul, map_smul, hy]
      rfl
    · rw [map_add, map_add, hy, hz]
      rfl

include he in

theorem exists_isFrame [Smooth π] (x : S) :
    ∃ (U : S.Opens) (n : ℕ) (s : Fin n → Γ(conormal e, U)), x ∈ U ∧ IsFrame s := by
  have := isQuasicoherent_conormal he
  obtain ⟨U, W, hx, -, c⟩ := exists_isChart he (x := x) (V := ⊤) trivial
  letI := c.algebra
  have : Algebra.Smooth Γ(S, U) Γ(X, W) := Smooth.smooth_appLE π c.affine_base c.affine c.le_base
  let E := LinearEquiv.ofBijective (c.ofAugCot he) (ofAugCot_bijective he c)
  have := Module.Finite.equiv E
  have := Module.Projective.of_equiv E
  exact Summand.exists_frame_of_projective c.affine_base ⟨x, hx⟩

end GlobalTheory.ConormalFrame

theorem GlobalTheory.ConormalFrame.exists_isFrame_omega : ∀ (O : Type) [CommRing O] (A : Over (Sp O))
    [GrpObj A] [Smooth A.hom] (x : Sp O), ∃ (U : (Sp O).Opens) (n : ℕ)
    (s : Fin n → Γ(GlobalTheory.LieVB.omega A, U)), x ∈ U ∧ GlobalTheory.VB.IsFrame s :=
  fun _ _ A _ _ x => GlobalTheory.ConormalFrame.exists_isFrame (GlobalTheory.LieVB.sec_hom η[A]) x
