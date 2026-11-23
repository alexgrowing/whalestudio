import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PairVEqZeroOfMemLieSpan
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsFiniteQCHomModOfExact
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC pullbackSections freeModule sectionsHom freeBasis)
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DualPull
open GlobalTheory.LocM (modN modNMap π_modNMap nsmul_id_modN)

namespace GlobalTheory.HTSheaf

section Subsheaves

variable {X : Scheme.{0}} {F G P : X.Modules} {U V : X.Opens}

instance isQuasicoherent_ker (φ : F ⟶ G) [F.IsQuasicoherent] [G.IsQuasicoherent] : (Sub.ker φ).toMod.IsQuasicoherent :=
  QCoh.isQuasicoherent_of_exact_app (Sub.ker φ).incl φ (fun U _ => (Sub.ker φ).incl_app_injective U)
    fun _ _ _ => (Sub.ker φ).mem_sec_iff

def imSub (φ : G ⟶ F) : Sub F := Sub.ker (cokernel.π φ)

instance isQuasicoherent_imSub (φ : G ⟶ F) [F.IsQuasicoherent] [G.IsQuasicoherent] : (imSub φ).toMod.IsQuasicoherent :=
  isQuasicoherent_ker _

theorem app_mem_imSub (φ : G ⟶ F) (s : Γ(G, V)) : φ.app V s ∈ (imSub φ).sec V :=
  congr(($(cokernel.condition φ)).app V s)

theorem mem_imSub_iff (φ : G ⟶ F) [F.IsQuasicoherent] [G.IsQuasicoherent] (hU : IsAffineOpen U) {s : Γ(F, U)} :
    s ∈ (imSub φ).sec U ↔ ∃ t, φ.app U t = s := QCoh.exact_cokernel_π_app φ hU s

def toIm (φ : G ⟶ F) : G ⟶ (imSub φ).toMod := (imSub φ).lift φ fun _ => app_mem_imSub φ

@[reassoc (attr := simp)] theorem toIm_incl (φ : G ⟶ F) : toIm φ ≫ (imSub φ).incl = φ := rfl

instance epi_toIm (φ : G ⟶ F) [F.IsQuasicoherent] [G.IsQuasicoherent] : Epi (toIm φ) :=
  (QCoh.epi_iff_forall_affine _).2 fun U hU s =>
    have ⟨t, ht⟩ := (mem_imSub_iff φ hU).1 ((imSub φ).incl_app_mem s)
    ⟨t, (imSub φ).incl_app_injective U ht⟩

def preSub (φ : F ⟶ G) (N : Sub G) : Sub F := Sub.ker (φ ≫ cokernel.π N.incl)

theorem mem_preSub_iff (φ : F ⟶ G) (N : Sub G) {s : Γ(F, V)} : s ∈ (preSub φ N).sec V ↔ φ.app V s ∈ N.sec V :=
  N.cokernel_π_app_eq_zero_iff

instance isQuasicoherent_preSub (φ : F ⟶ G) (N : Sub G) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [N.toMod.IsQuasicoherent] : (preSub φ N).toMod.IsQuasicoherent := isQuasicoherent_ker _

def spanSub {ι : Type} (u : ι → Γ(F, ⊤)) : Sub F := imSub (sectionsHom u)

instance isQuasicoherent_spanSub {ι : Type} [Finite ι] (u : ι → Γ(F, ⊤)) [F.IsQuasicoherent] :
    (spanSub u).toMod.IsQuasicoherent := isQuasicoherent_imSub _

theorem sectionsHom_app_sum {ι : Type} [Fintype ι] (u : ι → Γ(F, ⊤)) (a : ι → Γ(X, V)) :
    (sectionsHom u).app V (∑ i, a i • resM _ le_top (freeBasis X i)) = ∑ i, a i • resM F le_top (u i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Scheme.Modules.Hom.app_smul, app_resM, QCoh.sectionsHom_app_freeBasis]

theorem mem_spanSub_iff {ι : Type} [Fintype ι] (u : ι → Γ(F, ⊤)) [F.IsQuasicoherent] (hU : IsAffineOpen U)
    {s : Γ(F, U)} : s ∈ (spanSub u).sec U ↔ ∃ a : ι → Γ(X, U), ∑ i, a i • resM F le_top (u i) = s := by
  refine (mem_imSub_iff _ hU).trans ⟨fun ⟨t, ht⟩ => ?_, fun ⟨a, ha⟩ => ⟨_, (sectionsHom_app_sum u a).trans ha⟩⟩
  obtain ⟨a, rfl⟩ := QCoh.exists_sum_smul_freeBasis U t
  exact ⟨a, (sectionsHom_app_sum u a).symm.trans ht⟩

theorem res_mem_spanSub {ι : Type} (u : ι → Γ(F, ⊤)) (i : ι) (V : X.Opens) : resM F le_top (u i) ∈ (spanSub u).sec V :=
  (spanSub u).res_mem le_top (QCoh.sectionsHom_app_freeBasis u i ▸ app_mem_imSub _ _)

theorem π_app_eq_zero_iff [F.IsQuasicoherent] (hU : IsAffineOpen U) (N : ℕ) (s : Γ(F, U)) :
    (cokernel.π (N • 𝟙 F)).app U s = 0 ↔ ∃ r, N • r = s := by
  refine (QCoh.exact_cokernel_π_app _ hU s).trans (exists_congr fun r => ?_)
  rw [show (N • 𝟙 F).app U r = N • r from by
    induction N with
    | zero => rw [zero_smul, zero_smul]; rfl
    | succ n ih => rw [succ_nsmul, succ_nsmul, ← ih]; rfl]

theorem nsmul_sec_modN (N : ℕ) (s : Γ(modN F N, V)) : N • s = 0 := by
  have h (n : ℕ) : (n • 𝟙 (modN F N)).app V s = n • s := by
    induction n with
    | zero => rw [zero_smul, zero_smul]; rfl
    | succ n ih => rw [succ_nsmul, succ_nsmul, ← ih]; rfl
  rw [← h, nsmul_id_modN]
  rfl

end Subsheaves

section Minors

variable {X : Scheme.{0}} {F : X.Modules} (N : Sub F) (r : ℕ)

def minors (U : X.Opens) : Set Γ(X, U) :=
  {d | ∃ (l : Fin r → Γ(dual F, U)) (m : Fin r → Γ(N.toMod, U)),
    d = (Matrix.of fun i k => dualApp (l i) le_rfl (N.incl.app U (m k))).det}

theorem resG_minor {U V : X.Opens} (h : V ≤ U) (l : Fin r → Γ(dual F, U)) (m : Fin r → Γ(N.toMod, U)) :
    resG X h (Matrix.of fun i k => dualApp (l i) le_rfl (N.incl.app U (m k))).det =
      (Matrix.of fun i k => dualApp (resM _ h (l i)) le_rfl (N.incl.app V (resM _ h (m k)))).det := by
  rw [RingHom.map_det]
  congr 1
  ext i k
  rw [Matrix.of_apply, app_resM, dualApp_res]
  exact (dualApp_resM (l i) le_rfl h _).symm

theorem minors_subset [(dual F).IsQuasicoherent] [N.toMod.IsQuasicoherent] {U V : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(X, U)) (h : V ≤ U) (hV : V = X.basicOpen f) : minors N r V ⊆ Ideal.span (resG X h '' minors N r U) := by
  rintro _ ⟨l, m, rfl⟩
  choose a l' hl using fun i => QCoh.exists_pow_smul_eq_res (dual F) hU f h hV (l i)
  choose b m' hm using fun k => QCoh.exists_pow_smul_eq_res N.toMod hU f h hV (m k)
  have hu : IsUnit (resG X h f) := by
    subst hV
    exact X.toRingedSpace.isUnit_res_basicOpen f
  have e := resG_minor N r h l' m'
  have e₂ : (Matrix.of fun i k => dualApp (resM _ h (l' i)) le_rfl (N.incl.app _ (resM _ h (m' k)))) =
      Matrix.diagonal (fun i => resG X h f ^ a i) * (Matrix.of fun i k => dualApp (l i) le_rfl (N.incl.app _ (m k))) *
        Matrix.diagonal fun k => resG X h f ^ b k := by
    ext i k
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, Matrix.of_apply,
      show resM _ h (l' i) = _ from (hl i).symm, show resM _ h (m' k) = _ from (hm k).symm,
      Scheme.Modules.Hom.app_smul, map_smul, dualApp_smul, resG_self, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_comm]
  rw [e₂, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal] at e
  have h₁ : IsUnit (∏ i, resG X h f ^ a i) := IsUnit.prod_univ_iff.2 fun i => hu.pow _
  have h₂ : IsUnit (∏ i, resG X h f ^ b i) := IsUnit.prod_univ_iff.2 fun i => hu.pow _
  rw [SetLike.mem_coe, ← Ideal.unit_mul_mem_iff_mem _ h₁, ← Ideal.mul_unit_mem_iff_mem _ h₂, ← e]
  exact Ideal.subset_span ⟨_, ⟨l', m', rfl⟩, rfl⟩

def minorIdeal [(dual F).IsQuasicoherent] [N.toMod.IsQuasicoherent] : X.IdealSheafData where
  ideal U := Ideal.span (minors N r U.1)
  map_ideal_basicOpen U f := by
    rw [Ideal.map_span]
    refine le_antisymm (Ideal.span_mono ?_) (Ideal.span_le.2 (minors_subset N r U.2 f _ rfl))
    rintro _ ⟨_, ⟨l, m, rfl⟩, rfl⟩
    exact ⟨_, _, resG_minor N r (X.basicOpen_le f) l m⟩

end Minors

section Eps

variable {R O ι : Type} [CommRing R] [CommRing O] (σ : ι → O →+* R)

open EigenSplit

def ann (χ : O →+* R) : Submodule R (R ⊗[ℤ] O) where
  carrier := {x | ∀ a, (1 ⊗ₜ a) * x = χ a • x}
  add_mem' hx hy a := by rw [mul_add, hx, hy, smul_add]
  zero_mem' a := by rw [mul_zero, smul_zero]
  smul_mem' c x hx a := by rw [mul_smul_comm, hx, smul_comm]

variable {σ}

theorem splitMap_eq_zero_of_mem_ann [IsDomain R] {i k : ι} (h : σ k ≠ σ i) {x : R ⊗[ℤ] O} (hx : x ∈ ann (σ i)) :
    splitMap σ x k = 0 := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h
  have := congrArg (splitMap σ · k) (hx a)
  simp only [map_mul, map_smul, Pi.mul_apply, EigenSplit.splitMap_tmul, one_mul, Pi.smul_apply, smul_eq_mul] at this
  exact (mul_eq_zero.1 ((sub_mul _ _ _).trans (sub_eq_zero.2 this))).resolve_left (sub_ne_zero.2 ha)

theorem exists_ann_eq_span [IsDomain R] [IsPrincipalIdealRing R] [Finite ι] (hσ : Function.Injective σ)
    (h : Function.Injective (splitMap σ)) (i : ι) :
    ∃ ε, ann (σ i) = Submodule.span R {ε} ∧ splitMap σ ε i ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  let q : R ⊗[ℤ] O →ₗ[R] R := LinearMap.proj i ∘ₗ (splitMap σ).toLinearMap
  have hq : ∀ x ∈ ann (σ i), q x = 0 → x = 0 := fun x hx h0 => h (by
    rw [map_zero]
    exact funext fun k => if e : k = i then e ▸ h0 else splitMap_eq_zero_of_mem_ann (hσ.ne e) hx)
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal ((ann (σ i)).map q)).principal
  obtain ⟨ε, hε, rfl⟩ : d ∈ (ann (σ i)).map q := hd ▸ Submodule.mem_span_singleton_self d
  have key : ann (σ i) = Submodule.span R {ε} := by
    refine le_antisymm (fun x hx => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hε)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hd ▸ Submodule.mem_map_of_mem hx)
    exact Submodule.mem_span_singleton.2 ⟨c, sub_eq_zero.1 (hq _ (sub_mem (Submodule.smul_mem _ _ hε) hx)
      (by rw [map_sub, map_smul, hc, sub_self]))⟩
  refine ⟨ε, key, fun h0 => ?_⟩
  choose a ha using fun k : {k // k ≠ i} => DFunLike.ne_iff.1 (hσ.ne k.2)
  let x : R ⊗[ℤ] O := ∏ k : {k // k ≠ i}, (1 ⊗ₜ a k - σ k.1 (a k) ⊗ₜ 1)
  have hx (k : ι) : splitMap σ x k = ∏ k' : {k // k ≠ i}, (σ k (a k') - σ k'.1 (a k')) := by simp [x]
  have hm : x ∈ ann (σ i) := fun b => h (funext fun k => by
    simp only [map_mul, map_smul, Pi.mul_apply, EigenSplit.splitMap_tmul, one_mul, Pi.smul_apply, smul_eq_mul]
    by_cases e : k = i
    · rw [e]
    · rw [hx, Finset.prod_eq_zero (Finset.mem_univ (⟨k, e⟩ : {k // k ≠ i})) (sub_self _), mul_zero, mul_zero])
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (key ▸ hm)
  have := hx i
  rw [← hc, map_smul, Pi.smul_apply, h0, smul_zero] at this
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 this.symm
  exact ha k (sub_eq_zero.1 hk).symm

theorem map_eq_smul_idem [IsDomain R] [DecidableEq ι] (hσ : Function.Injective σ) {i : ι} {x : R ⊗[ℤ] O}
    (hx : x ∈ ann (σ i)) {R' : Type} [CommRing R'] (f : R →+* R') (h : IsSplitting fun k => f.comp (σ k)) :
    Algebra.TensorProduct.map f.toIntAlgHom (AlgHom.id ℤ O) x = f (splitMap σ x i) • idem h i := by
  have e (y : R ⊗[ℤ] O) (k : ι) : splitMap (fun k => f.comp (σ k))
      (Algebra.TensorProduct.map f.toIntAlgHom (AlgHom.id ℤ O) y) k = f (splitMap σ y k) := by
    induction y with
    | zero => simp
    | add y z hy hz => simp only [map_add, Pi.add_apply, hy, hz]
    | tmul r a => simp
  refine h.1 (funext fun k => ?_)
  rw [e, map_smul, splitMap_idem, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k = i
  · rw [hk, Pi.single_eq_same, mul_one]
  · rw [Pi.single_eq_of_ne hk, mul_zero, splitMap_eq_zero_of_mem_ann (hσ.ne hk) hx, map_zero]

variable {X : Scheme.{0}} {F : X.Modules}

def tensAct (β : R →+* Γ(X, ⊤)) (ρ : O →+* End F) : R ⊗[ℤ] O →+* End F :=
  letI : Algebra ℤ (End F) := Ring.toIntAlgebra _
  (Algebra.TensorProduct.lift ((smulEnd F).comp β).toIntAlgHom ρ.toIntAlgHom
    fun _ a => (smulHom_comp (act ρ a) _).symm).toRingHom

end Eps

section Pull

variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G'] [GrpObj G'']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {g : S'' ⟶ S'} {ψ : G''.left ⟶ G'.left}
  (h : IsGrpPullback G' G f φ) {V V' : S.Opens} {T T' : S'.Opens}

def pb (e : T ≤ f ⁻¹ᵁ V) : Γ(omega G, V) →+ Γ(omega G', T) :=
  letI := QCoh.appLEModule f ((Scheme.Modules.pullback f).obj (omega G)) e
  ((omegaBase h).app T).hom.comp (pullbackSections f (omega G) e).toAddMonoidHom

theorem pb_apply (e : T ≤ f ⁻¹ᵁ V) (s : Γ(omega G, V)) :
    pb h e s = (omegaBase h).app T (pullbackSections f (omega G) e s) := rfl

theorem pb_smul (e : T ≤ f ⁻¹ᵁ V) (a : Γ(S, V)) (s : Γ(omega G, V)) : pb h e (a • s) = f.appLE V T e a • pb h e s := by
  rw [pb_apply, QCoh.pullbackSections_smul, Scheme.Modules.Hom.app_smul, pb_apply]

theorem pb_resM (e : T ≤ f ⁻¹ᵁ V') (k : V' ≤ V) (s : Γ(omega G, V)) :
    pb h e (resM _ k s) = pb h (e.trans (f.preimage_mono k)) s :=
  congrArg ((omegaBase h).app T) (QCoh.pullbackSections_res f (omega G) e k s)

theorem resM_pb (e : T ≤ f ⁻¹ᵁ V) (k : T' ≤ T) (s : Γ(omega G, V)) : resM _ k (pb h e s) = pb h (k.trans e) s :=
  (app_resM (omegaBase h) k _).symm.trans (congrArg ((omegaBase h).app T') (QCoh.res_pullbackSections f (omega G) e k s))

variable [QuasiSeparated G.hom]

theorem pb_pb (h' : IsGrpPullback G'' G' g ψ) {k : S'' ⟶ S} {χ : G''.left ⟶ G.left} (h'' : IsGrpPullback G'' G k χ)
    (hk : g ≫ f = k) (hχ : ψ ≫ φ = χ) {W : S''.Opens} (e : T ≤ f ⁻¹ᵁ V) (e' : W ≤ g ⁻¹ᵁ T) (e'' : W ≤ k ⁻¹ᵁ V)
    (s : Γ(omega G, V)) : pb h' e' (pb h e s) = pb h'' e'' s := by
  subst hk hχ
  have H (x : W) := Conormal.exists_isChart (sec_hom (MonObj.one (X := G))) (V := V) (x := (g ≫ f) x.1) (e'' x.2)
  choose U B hx hU c using H
  refine Twist.sec_ext_of_cover (fun x : W => W ⊓ (g ≫ f) ⁻¹ᵁ U x) (fun _ => inf_le_left)
    (fun x hxW => Opens.mem_iSup.2 ⟨⟨x, hxW⟩, hxW, hx _⟩) fun x => ?_
  obtain ⟨a, ha⟩ := (c x).d_surjective (sec_hom (MonObj.one (X := G))) (resM _ (hU x) s)
  have k₁ : T ⊓ f ⁻¹ᵁ U x ≤ f ⁻¹ᵁ U x := inf_le_right
  have k₂ : W ⊓ (g ≫ f) ⁻¹ᵁ U x ≤ g ⁻¹ᵁ (T ⊓ f ⁻¹ᵁ U x) := inf_le_inf e' le_rfl
  have k₃ := Conormal.le_of_sq (unitSec_comp h) (c x).le k₁
  have k₄ := Conormal.le_of_sq (unitSec_comp h') k₃ k₂
  calc _ = pb h' k₂ (pb h k₁ (resM _ (hU x) s)) := by
        rw [resM_pb, pb_resM, ← resM_pb h e inf_le_left, pb_resM]
    _ = pb h'' inf_le_right (resM _ (hU x) s) := by
        rw [← show dUnit G (c x).le a = resM (omega G) (hU x) s from ha, pb_apply h, omegaBase_dUnit h _ _ k₃ le_rfl, pb_apply, omegaBase_dUnit h' _ _ k₄ le_rfl, pb_apply,
          omegaBase_dUnit h'' _ _ (W' := ψ ⁻¹ᵁ φ ⁻¹ᵁ B x) k₄ le_rfl]
        exact congrArg _ (Conormal.appLE_appLE rfl _ _ _ a)
    _ = _ := by rw [resM_pb, pb_resM]

theorem span_range_pb (hT : IsAffineOpen T) (hV : IsAffineOpen V) (e : T ≤ f ⁻¹ᵁ V) :
    Submodule.span Γ(S', T) (Set.range (pb h e)) = ⊤ := by
  letI := QCoh.appLEAlgebra f e
  letI := QCoh.appLEModule f ((Scheme.Modules.pullback f).obj (omega G)) e
  haveI := QCoh.appLE_isScalarTower f ((Scheme.Modules.pullback f).obj (omega G)) e
  refine eq_top_iff.2 fun s _ => ?_
  obtain ⟨t, rfl⟩ : ∃ t, (omegaBase h).app T t = s :=
    ⟨(inv (omegaBase h)).app T s, by rw [QCoh.app_app, IsIso.inv_hom_id]; rfl⟩
  induction t using (QCoh.isBaseChange_pullbackSections f (omega G) hT hV e).inductionOn with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
  | smul a t ht => rw [Scheme.Modules.Hom.app_smul]; exact Submodule.smul_mem _ _ (ht trivial)
  | add t t' ht ht' => rw [map_add]; exact add_mem (ht trivial) (ht' trivial)

omit [QuasiSeparated G.hom]

def pushOm : omega G ⟶ (Scheme.Modules.pushforward f).obj (omega G') :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv (omega G) (omega G') (omegaBase h)

theorem pushOm_app (s : Γ(omega G, V)) : (pushOm h).app V s = pb h (le_refl (f ⁻¹ᵁ V)) s :=
  congrArg ((omegaBase h).app (f ⁻¹ᵁ V)) (resM_self (F := (Scheme.Modules.pullback f).obj (omega G)) _ _).symm

def pushMod (N : ℕ) : modN (omega G) N ⟶ (Scheme.Modules.pushforward f).obj (modN (omega G') N) :=
  cokernel.desc _ (pushOm h ≫ (Scheme.Modules.pushforward f).map (cokernel.π _)) (by
    rw [Preadditive.nsmul_comp, Category.id_comp, ← Preadditive.comp_nsmul, ← Functor.map_nsmul,
      ← Category.comp_id (cokernel.π _), ← Preadditive.comp_nsmul, nsmul_id_modN, comp_zero, Functor.map_zero, comp_zero])

def pbMod (N : ℕ) (e : T ≤ f ⁻¹ᵁ V) : Γ(modN (omega G) N, V) →+ Γ(modN (omega G') N, T) :=
  (resM (modN (omega G') N) e).comp ((pushMod h N).app V).hom

theorem pbMod_π (N : ℕ) (e : T ≤ f ⁻¹ᵁ V) (s : Γ(omega G, V)) :
    pbMod h N e ((cokernel.π (N • 𝟙 (omega G))).app V s) = (cokernel.π (N • 𝟙 (omega G'))).app T (pb h e s) := by
  have e₁ : (pushMod h N).app V ((cokernel.π (N • 𝟙 (omega G))).app V s) =
      (cokernel.π (N • 𝟙 (omega G'))).app _ (pb h (le_refl (f ⁻¹ᵁ V)) s) := by
    rw [QCoh.app_app, pushMod, cokernel.π_desc, ← pushOm_app]
    rfl
  exact (congrArg (resM (modN (omega G') N) e) e₁).trans ((app_resM _ e _).symm.trans (congrArg _ (resM_pb h _ e s)))

theorem pbMod_resM (N : ℕ) (e : T ≤ f ⁻¹ᵁ V') (k : V' ≤ V) (u : Γ(modN (omega G) N, V)) :
    pbMod h N e (resM _ k u) = pbMod h N (e.trans (f.preimage_mono k)) u :=
  (congrArg (resM (modN (omega G') N) e) (app_resM (pushMod h N) k u)).trans
    (resM_resM (F := modN (omega G') N) (f.preimage_mono k) e _)

theorem resM_pbMod (N : ℕ) (e : T ≤ f ⁻¹ᵁ V) (k : T' ≤ T) (u : Γ(modN (omega G) N, V)) :
    resM _ k (pbMod h N e u) = pbMod h N (k.trans e) u := resM_resM e k _

theorem pbMod_omegaMap (a : G ⟶ G) (a' : G' ⟶ G') [IsMonHom a] [IsMonHom a'] (w : a'.left ≫ φ = φ ≫ a.left) (N : ℕ)
    (e : T ≤ f ⁻¹ᵁ V) (u : Γ(modN (omega G) N, V)) :
    pbMod h N e ((modNMap (omegaMap a) N).app V u) = (modNMap (omegaMap a') N).app T (pbMod h N e u) := by
  have key : modNMap (omegaMap a) N ≫ pushMod h N =
      pushMod h N ≫ (Scheme.Modules.pushforward f).map (modNMap (omegaMap a') N) := by
    have k₀ : omegaMap a ≫ pushOm h = pushOm h ≫ (Scheme.Modules.pushforward f).map (omegaMap a') := by
      rw [pushOm, ← Adjunction.homEquiv_naturality_left, omegaBase_naturality h h a a' w,
        Adjunction.homEquiv_naturality_right]
    rw [← cancel_epi (cokernel.π _), LocM.π_modNMap_assoc, pushMod, cokernel.π_desc, cokernel.π_desc_assoc, Category.assoc,
      ← Functor.map_comp, π_modNMap, reassoc_of% k₀, Functor.map_comp]
  exact (congrArg (resM (modN (omega G') N) e) congr(($key).app V u)).trans (app_resM (modNMap (omegaMap a') N) e _).symm

end Pull

example {X : Scheme.{0}} (F : X.Modules) (V : X.Opens) (s : Γ(F, V)) : s ∈ (imSub (𝟙 F)).sec V := app_mem_imSub (𝟙 F) s

example : (1 : ℤ) ⊗ₜ[ℤ] ((1, 0) : ℤ × ℤ) ∈ ann (RingHom.fst ℤ ℤ) := fun a => by
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← TensorProduct.tmul_smul]
  cases a
  simp

end GlobalTheory.HTSheaf
