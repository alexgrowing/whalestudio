import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDualOfAffinePairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple

set_option autoImplicit false

noncomputable section

open Module TensorProduct GlobalTheory.DeRham

namespace GlobalTheory.PrincipalPolPairing

section Algebra

variable {R R' : Type} {M M' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M]
  [Module R M] [AddCommGroup M'] [Module R' M'] {f : M →ₛₗ[algebraMap R R'] M'}

theorem exists_corr (hf : Function.Bijective (liftSemi f)) (h : Dual R M) :
    ∃ h' : Dual R' M', ∀ c, h' (f c) = algebraMap R R' (h c) := by
  let e := LinearEquiv.ofBijective _ hf
  let l : M →ₛₗ[algebraMap R R'] R' :=
    { toFun c := algebraMap R R' (h c), map_add' := by simp, map_smul' := by simp }
  refine ⟨liftSemi l ∘ₗ e.symm.toLinearMap, fun c ↦ ?_⟩
  have : f c = e (1 ⊗ₜ c) := (one_smul R' (f c)).symm
  rw [this, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, liftSemi_tmul, one_smul]
  rfl

theorem ext_bc (hf : Function.Bijective (liftSemi f)) {N : Type*} [AddCommGroup N] [Module R' N]
    {u v : M' →ₗ[R'] N} (h : ∀ c, u (f c) = v (f c)) : u = v := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hf.2 c
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

theorem ext_corr [Module.Finite R M] [Module.Projective R M] (hf : Function.Bijective (liftSemi f))
    {N : Type*} [AddCommGroup N] [Module R' N] {u v : Dual R' M' →ₗ[R'] N}
    (h : ∀ (y : Dual R M) (y' : Dual R' M'), (∀ c, y' (f c) = algebraMap R R' (y c)) → u y' = v y') :
    u = v := by
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  choose l hl using fun i : Fin n ↦ exists_corr hf (LinearMap.proj i ∘ₗ s)
  refine LinearMap.ext fun y' ↦ ?_
  have e : y' = ∑ i, y' (f (p (Pi.single i 1))) • l i := by
    refine ext_bc hf fun c ↦ ?_
    have hc : c = ∑ i, s c i • p (Pi.single i 1) := by
      conv_lhs => rw [← LinearMap.id_apply (R := R) c, ← hps, LinearMap.comp_apply, pi_eq_sum_univ' (s c)]
      simp only [map_sum, map_smul]
    conv_lhs => rw [hc]
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hl,
      LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul, mul_comm]
    simp
  rw [e]
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h _ _ (hl i)]

theorem subsingleton_coker [Module.Finite R M] [Module.Projective R M]
    (hf : Function.Bijective (liftSemi f)) (θ : Dual R M →ₗ[R] M) (φ' : Dual R' M' →ₗ[R'] Dual R' (Dual R' M'))
    (hφ : Function.Surjective φ')
    (h : ∀ (x y : Dual R M) (x' y' : Dual R' M'), (∀ c, x' (f c) = algebraMap R R' (x c)) →
      (∀ c, y' (f c) = algebraMap R R' (y c)) → φ' x' y' = algebraMap R R' (y (θ x))) :
    Subsingleton (R' ⊗[R] (M ⧸ LinearMap.range θ)) := by
  let e := LinearEquiv.ofBijective _ hf
  haveI : Module.Finite R' M' := Module.Finite.equiv e
  haveI : Module.Projective R' M' := Module.Projective.of_equiv e
  let π : M' →ₗ[R'] R' ⊗[R] (M ⧸ LinearMap.range θ) :=
    (LinearMap.range θ).mkQ.baseChange R' ∘ₗ e.symm.toLinearMap
  have hπ : Function.Surjective π :=
    (LinearMap.baseChange_surjective R' (Submodule.mkQ_surjective _)).comp e.symm.surjective
  let θ' : Dual R' M' →ₗ[R'] M' := (Module.evalEquiv R' M').symm.toLinearMap ∘ₗ φ'
  have hθ' : Function.Surjective θ' := (Module.evalEquiv R' M').symm.surjective.comp hφ
  have k : π ∘ₗ θ' = 0 := by
    refine ext_corr hf fun x x' hx ↦ ?_
    have e₁ : θ' x' = f (θ x) := by
      apply (Module.evalEquiv R' M').injective
      refine ((Module.evalEquiv R' M').apply_symm_apply _).trans (ext_corr hf fun y y' hy ↦ ?_)
      rw [h x y x' y' hx hy, ← hy]
      rfl
    have e₂ : f (θ x) = e (1 ⊗ₜ θ x) := (one_smul R' (f _)).symm
    rw [LinearMap.comp_apply, e₁, e₂]
    simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, LinearMap.baseChange_tmul,
      LinearMap.zero_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self θ x), tmul_zero]
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := (hπ.comp hθ') a
  obtain ⟨b, rfl⟩ := (hπ.comp hθ') b
  exact (LinearMap.congr_fun k a).trans (LinearMap.congr_fun k b).symm

theorem subsingleton_of_fibres {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (h : ∀ p : PrimeSpectrum R, Subsingleton (AlgebraicClosure p.asIdeal.ResidueField ⊗[R] Q)) :
    Subsingleton Q := by
  rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  have := h p
  have e := AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField p.asIdeal.ResidueField
    (AlgebraicClosure p.asIdeal.ResidueField) Q
  have h₁ := e.toEquiv.subsingleton
  have h₂ : Nontrivial (AlgebraicClosure p.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField]
    (p.asIdeal.ResidueField ⊗[R] Q)) :=
    Module.FaithfullyFlat.rTensor_nontrivial _ _ _
  exact not_subsingleton _ h₁

theorem isPerfPair_of_fibres {M : Type 1} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (φ : Dual R M →ₗ[R] Dual R M →ₗ[R] R)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω], ∃ (M' : Type 1) (_ : AddCommGroup M')
      (_ : Module Ω M') (f : M →ₛₗ[algebraMap R Ω] M') (φ' : Dual Ω M' →ₗ[Ω] Dual Ω M' →ₗ[Ω] Ω),
      Function.Bijective (liftSemi f) ∧ φ'.IsPerfPair ∧
      ∀ (x : Dual R M) (x' : Dual Ω M') (y : Dual R M) (y' : Dual Ω M'), (∀ c, x' (f c) = algebraMap R Ω (x c)) →
        (∀ c, y' (f c) = algebraMap R Ω (y c)) → φ' x' y' = algebraMap R Ω (φ x y)) :
    φ.IsPerfPair := by
  let E := Module.evalEquiv R M
  have key (θ : Dual R M →ₗ[R] M)
      (hθ : (∀ x y, y (θ x) = φ x y) ∨ ∀ x y, y (θ x) = φ y x) : Function.Surjective θ := by
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    refine subsingleton_of_fibres (R := R) fun p ↦ ?_
    obtain ⟨M', _, _, f, φ', hf, hp, k⟩ := h (AlgebraicClosure p.asIdeal.ResidueField)
    rcases hθ with hθ | hθ
    · exact subsingleton_coker hf θ φ' hp.bijective_left.2 fun x y x' y' hx hy ↦ by
        rw [hθ, k x x' y y' hx hy]
    · exact subsingleton_coker hf θ φ'.flip hp.bijective_right.2 fun x y x' y' hx hy ↦ by
        rw [hθ, LinearMap.flip_apply, k y y' x x' hy hx]
  have ev (z : Dual R (Dual R M)) (y : Dual R M) : y (E.symm z) = z y :=
    LinearMap.congr_fun (E.apply_symm_apply z) y
  have s₁ := key (E.symm.toLinearMap ∘ₗ φ) (Or.inl fun x y ↦ ev _ _)
  have s₂ := key (E.symm.toLinearMap ∘ₗ φ.flip) (Or.inr fun x y ↦ ev _ _)
  refine LinearMap.IsPerfPair.of_bijective _ ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun z ↦ ?_⟩
  · refine LinearMap.ext fun c ↦ ?_
    obtain ⟨y, rfl⟩ := s₂ c
    refine (ev _ _).trans ?_
    rw [LinearMap.flip_apply, hx]
    rfl
  · obtain ⟨x, hx⟩ := s₁ (E.symm z)
    exact ⟨x, E.symm.injective hx⟩

theorem exists_inverse [Module.Finite R M] [Module.Projective R M] (φ : Dual R M →ₗ[R] Dual R M →ₗ[R] R)
    (hφ : φ.IsPerfPair) :
    ∃ b : M →ₗ[R] M →ₗ[R] R, b.IsPerfPair ∧ ∀ s y, φ (b s) y = y s := by
  let Φ := LinearEquiv.ofBijective φ hφ.bijective_left
  let B : M ≃ₗ[R] Dual R M := (Module.evalEquiv R M).trans Φ.symm
  exact ⟨B.toLinearMap, LinearMap.IsPerfPair.of_bijective _ B.bijective,
    fun s y ↦ LinearMap.congr_fun (Φ.apply_symm_apply _) y⟩

theorem inverse_bc [Module.Finite R M] [Module.Projective R M] (hf : Function.Bijective (liftSemi f))
    {φ : Dual R M →ₗ[R] Dual R M →ₗ[R] R} {φ' : Dual R' M' →ₗ[R'] Dual R' M' →ₗ[R'] R'}
    (hφ' : φ'.IsPerfPair)
    (k : ∀ (x : Dual R M) (x' : Dual R' M') (y : Dual R M) (y' : Dual R' M'),
      (∀ c, x' (f c) = algebraMap R R' (x c)) → (∀ c, y' (f c) = algebraMap R R' (y c)) →
        φ' x' y' = algebraMap R R' (φ x y))
    {b : M →ₗ[R] M →ₗ[R] R} {b' : M' →ₗ[R'] M' →ₗ[R'] R'} (hb : ∀ s y, φ (b s) y = y s)
    (hb' : ∀ s y, φ' (b' s) y = y s) (s t : M) : b' (f s) (f t) = algebraMap R R' (b s t) := by
  obtain ⟨x', hx⟩ := exists_corr hf (b s)
  rw [← hx]
  congr 1
  refine hφ'.bijective_left.1 (ext_corr hf fun y y' hy ↦ ?_)
  rw [hb', k _ _ _ _ hx hy, hb, hy]

end Algebra

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.CatCoh GlobalTheory.Cris
open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase GlobalTheory.DeRhamSheaf
open Limits (pullback)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Affine

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem isotropic (H : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : LB (A ⊗ A).left} (hP : P.IsLB) {φ : HdR A →ₗ[R] HdR A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) A A P φ) : ∀ x ∈ Fil A, ∀ y ∈ Fil A, φ x y = 0 := by
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨iso, -⟩ := H.2.2.2.2 R _ _ (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg) P hP ψ hψ
  intro x hx y hy
  have := iso _ (push_mem_Fil (inl A A) hx) _ (push_mem_Fil (inr A A) hy)
  rwa [e, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_id, push_one, LinearMap.zero_apply, map_zero, LinearMap.zero_apply, sub_zero] at this

theorem corr_bc (H : AbelianDeRham.Free) {R' : Type} [CommRing R'] [Algebra R R'] {A' : Over (Sp R')} [GrpObj A']
    (hA' : IsAbelianScheme A') (hg' : SmoothOfRelativeDimension g A'.hom) {π : A'.left ⟶ A.left}
    (h : IsGrpPullback A' A (spMap (algebraMap R R')) π) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    {P' : LB (A' ⊗ A').left} (hP' : P'.IsLB) (e : cls P' hP' = CechPic.pull (sqMap h.1.w) (cls P hP))
    {φ : HdR A →ₗ[R] HdR A →ₗ[R] R} (hφ : IsCorrForm (dp0 R) (𝟙 _) A A P φ)
    {φ' : HdR A' →ₗ[R'] HdR A' →ₗ[R'] R'} (hφ' : IsCorrForm (dp0 R') (𝟙 _) A' A' P' φ') :
    ∀ x x' y y', (bcMor h).Corr x x' → (bcMor h).Corr y y' → φ' x' y' = algebraMap R R' (φ x y) := by
  obtain ⟨χ, hχ, k⟩ := hφ.pull hP (bcMor h) (bcMor h) (h := sqMap h.1.w) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _) hP' ((cls_eq_iff (pull_isLB hP _) hP').1 ((cls_pull hP _ _).trans e.symm))
  obtain rfl := hχ.unique (cupSquare_of_free H (AbelianSchemeGerms.isAbelianScheme_tensor A' A' hA' hA') (smooth_prod hg' hg'))
    hP' hφ'
  exact k

theorem perfect (H : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : LB (A ⊗ A).left} (hP : P.IsLB) (hc : IsPrincipalPol A (cls P hP)) {φ : HdR A →ₗ[R] HdR A →ₗ[R] R}
    (hφ : IsCorrForm (dp0 R) (𝟙 _) A A P φ) : φ.IsPerfPair := by
  obtain ⟨_, _, -⟩ := Free.prim H.1 hA hg
  refine isPerfPair_of_fibres φ fun Ω _ _ _ ↦ ?_
  obtain ⟨L, hL, -, hK, hcL⟩ := hc.2.2 Ω (spMap (algebraMap R Ω))
  have h := isGrpPullback_pullback A (spMap (algebraMap R Ω))
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hA h
  have hg' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 hg
  haveI := hA'.comm
  obtain ⟨ψ, hψ⟩ := PureLift.exists_isPolForm H.1 hA' hg' hL
  have hΛ : (abelian₂ _ L).IsLB := LB.isLB_linComb hL _ _
  refine ⟨_, _, _, (bcMor h).pull, ψ, (H.2.2.1 R A g hA hg Ω _ _ h).1,
    (H.2.2.2.2 Ω _ g hA' hg' L hL ψ hψ).2 hK, corr_bc H.1 hA' hg' h hP hΛ ?_ hφ (isCorrForm_lam hψ)⟩
  refine (cls_cube_two hL _ _ hΛ).trans (hcL.symm.trans ?_)
  congr 2

theorem exists_pairing (H : AbelianDeRham) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    {P : LB (A ⊗ A).left} (hP : P.IsLB) (hc : IsPrincipalPol A (cls P hP)) :
    ∃ (φ : HdR A →ₗ[R] HdR A →ₗ[R] R) (b : primDR A →ₗ[R] primDR A →ₗ[R] R),
      IsCorrForm (dp0 R) (𝟙 _) A A P φ ∧ φ.IsPerfPair ∧ b.IsPerfPair ∧ (∀ s y, φ (b s) y = y s) ∧
      ∀ s ∈ PrimitiveSubmodule A, ∀ t ∈ PrimitiveSubmodule A, b s t = 0 := by
  obtain ⟨φ, hφ⟩ := exists_isCorrForm
    (cupSquare_of_free H.1 (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg)) hP
    ((triv_ev_iff hP _ _).2 hc.1) ((triv_ev_iff hP _ _).2 hc.2.1)
  obtain ⟨_, _, hrk⟩ := Free.prim H.1 hA hg
  obtain ⟨-, ⟨N, hN⟩, _, _, hF⟩ := H.2.1 R _ _ hA hg
  have hp := perfect H hA hg hP hc hφ
  obtain ⟨b, hb, k⟩ := exists_inverse φ hp
  refine ⟨φ, b, hφ, hp, hb, k, fun s hs t ht ↦ ?_⟩
  have := PolExistsRing.mem_of_annihilates_dual φ (PrimitiveSubmodule A) N hN _ hrk hF (isotropic H hA hg hP hφ) (b s)
    fun y hy ↦ (k s y).trans ((Submodule.mem_dualAnnihilator _).1 hy s hs)
  exact (Submodule.mem_dualAnnihilator _).1 this t ht

end Affine

theorem exists_iso_dual (hD : AbelianDeRham) (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hc : ∃ c, IsPrincipalPol A c)
    (H : T.Modules) (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))
    (he : HodgeSeqSheaf.IsDRTriv A H e) (F : T.Modules) (i : F ⟶ H)
    (hi : ∀ (V : T.Opens) (hV : IsAffineOpen V) (x : Γ(F, V)), e V hV (i.app V x) ∈ PrimitiveSubmodule (onAff A hV)) :
    ∃ β : H ⟶ VB.dual H, IsIso β ∧ i ≫ β ≫ VB.dualMap i = 0 := by
  obtain ⟨c, hc⟩ := hc
  have hπ (V : T.Opens) (hV : IsAffineOpen V) :
      IsGrpPullback (onAff A hV) A hV.fromSpec (pullback.fst A.hom hV.fromSpec) := isGrpPullback_pullback A _
  choose P hP eP using fun (V : T.Opens) (hV : IsAffineOpen V) ↦ cls_surj (CechPic.pull (sqMap (hπ V hV).1.w) c)
  choose φ b hφ pφ pb k iso using fun (V : T.Opens) (hV : IsAffineOpen V) ↦
    exists_pairing hD (DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV) (DeRhamSheaf.VB.smooth_onAff A hg hV)
      (hP V hV) (eP V hV ▸ PPAS.isPrincipalPol_pull (hπ V hV) hc)
  obtain ⟨β, h₁, h₂, -⟩ := AffinePairingGlue.exists_iso_dual_of_affine_pairing T H (2 * g)
    (DeRhamSheaf.VB.isVB_of_isDeRhamSheaf hD T A g hA hg H ⟨e, he⟩)
    (fun V hV ↦ (b V hV).compl₁₂ (e V hV).toLinearMap (e V hV).toLinearMap)
    (fun V V' hV hV' h s t ↦ by
      letI := resAlg h
      obtain ⟨π, hπ', eπ⟩ := DeRhamSheaf.VB.exists_transition A hV hV' h
      have hAV := DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV
      have hgV := DeRhamSheaf.VB.smooth_onAff A hg hV
      obtain ⟨_, _, -⟩ := Free.prim hD.1 hAV hgV
      simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
      rw [he V V' hV hV' h π hπ' eπ, he V V' hV hV' h π hπ' eπ]
      refine inverse_bc (hD.2.2.1 _ _ g hAV hgV _ _ π hπ').1 (pφ V' hV') (corr_bc hD.1
        (DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV') (DeRhamSheaf.VB.smooth_onAff A hg hV') hπ' (hP V hV)
        (hP V' hV') ?_ (hφ V hV) (hφ V' hV')) (k V hV) (k V' hV') _ _
      rw [eP, eP, ← CechPic.pull_comp]
      congr 2
      apply pullback.hom_ext
      · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, eπ]
      · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, eπ])
    (fun V hV ↦ by
      have := pb V hV
      exact LinearMap.IsPerfPair.congr (b V hV) (e V hV) (e V hV) _ (by ext; simp))
    F i fun V hV x y ↦ iso V hV _ (hi V hV x) _ (hi V hV y)
  exact ⟨β, h₁, h₂⟩

theorem main : GlobalTheory.CovTop.HypothesesX → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.PoincareDeRhamDuality →
    ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c) →
    ∀ (H : T.Modules) (e : ∀ (V : T.Opens) (hV : IsAffineOpen V),
        Γ(H, V) ≃ₗ[Γ(T, V)] GlobalTheory.DeRham.primDR (GlobalTheory.DeRhamSheaf.onAff A hV)),
      GlobalTheory.HodgeSeqSheaf.IsDRTriv A H e →
      ∀ (F : T.Modules) (i : F ⟶ H), (∀ (V : T.Opens) (hV : IsAffineOpen V) (x : Γ(F, V)),
          e V hV (i.app V x) ∈ GlobalTheory.DeRham.PrimitiveSubmodule (GlobalTheory.DeRhamSheaf.onAff A hV)) →
      ∃ β : H ⟶ GlobalTheory.VB.dual H, IsIso β ∧ i ≫ β ≫ GlobalTheory.VB.dualMap i = 0 :=
  fun _ hP _ T A _ g hA hg hc H e he F i hi ↦ exists_iso_dual hP.p5 T A g hA hg hc H e he F i hi

end GlobalTheory.PrincipalPolPairing
