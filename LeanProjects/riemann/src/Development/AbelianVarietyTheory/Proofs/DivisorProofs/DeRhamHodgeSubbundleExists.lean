import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.ConjSeq.ConjSub

open GlobalTheory.Published.AbelianDeRham (bcMor)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul)

theorem exists_sub_of_affine {X : Scheme.{0}} {F : X.Modules}
    (N : ∀ V : X.Opens, IsAffineOpen V → Submodule Γ(X, V) Γ(F, V))
    (hres : ∀ (V W : X.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V) (s : Γ(F, V)),
      s ∈ N V hV → resM F h s ∈ N W hW)
    (hloc : ∀ (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V)) (s : Γ(F, V)),
      resM F (X.basicOpen_le f) s ∈ N _ (hV.basicOpen f) → ∃ n : ℕ, f ^ n • s ∈ N V hV) :
    ∃ C : GlobalTheory.VB.Sub F, ∀ (V : X.Opens) (hV : IsAffineOpen V) (s : Γ(F, V)),
      s ∈ C.sec V ↔ s ∈ N V hV := by
  let S : ∀ U : X.Opens, Submodule Γ(X, U) Γ(F, U) := fun U =>
    { carrier := {s | ∀ (V : X.Opens) (hV : IsAffineOpen V) (h : V ≤ U), resM F h s ∈ N V hV}
      add_mem' := fun hs ht V hV h => by rw [map_add]; exact add_mem (hs V hV h) (ht V hV h)
      zero_mem' := fun V hV h => by rw [map_zero]; exact zero_mem _
      smul_mem' := fun a s hs V hV h => by
        rw [resM_smul]; exact Submodule.smul_mem _ _ (hs V hV h) }
  have hS : ∀ (U : X.Opens) (s : Γ(F, U)), s ∈ S U ↔
      ∀ (V : X.Opens) (hV : IsAffineOpen V) (h : V ≤ U), resM F h s ∈ N V hV := fun _ _ => Iff.rfl
  refine ⟨⟨S, fun {U W} h s hs => (hS _ _).2 fun V hV h' => ?_, fun {U s} H =>
    (hS _ _).2 fun V hV h => ?_⟩, fun V hV s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · rw [resM_resM]
    exact (hS _ _).1 hs V hV _
  · let G : Set Γ(X, V) := {f | ∃ n : ℕ, f ^ n • resM F h s ∈ N V hV}
    have hG : Ideal.span G = ⊤ := by
      rw [← hV.self_le_iSup_basicOpen_iff]
      intro x hx
      obtain ⟨W, hW, hxW, hs⟩ := H x (h hx)
      obtain ⟨f, hf, hxf⟩ := hV.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hx
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hloc V hV f _ ?_⟩, hxf⟩
      have := (hS _ _).1 hs _ (hV.basicOpen f) hf
      rwa [resM_resM, ← resM_resM h (X.basicOpen_le f)] at this
    exact Submodule.mem_of_span_eq_top_of_smul_pow_mem _ G hG _ fun r => r.2
  · have := (hS _ _).1 hs V hV le_rfl
    rwa [resM_self] at this
  · exact (hS _ _).2 fun W hW h => hres V W hV hW h s hs

theorem exists_pow_smul_mem_span {R R' : Type} {M M' : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (r : R)
    [IsLocalization.Away r R'] (f : M →ₛₗ[algebraMap R R'] M')
    (hf : Function.Bijective (liftSemi f)) {σ : R →+* R} {σ' : R' →+* R'} (Φ : M →ₛₗ[σ] M)
    (Φ' : M' →ₛₗ[σ'] M') (hΦ : ∀ m, f (Φ m) = Φ' (f m)) (x : M)
    (hx : f x ∈ Submodule.span R' (Set.range Φ')) :
    ∃ n : ℕ, r ^ n • x ∈ Submodule.span R (Set.range Φ) := by
  letI : Module R M' := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' M' :=
    ⟨fun a b m => by
      show (a • b) • m = algebraMap R R' a • b • m
      rw [Algebra.smul_def, mul_smul]⟩
  let l : M →ₗ[R] M' :=
    { toFun := f
      map_add' := map_add _
      map_smul' := fun a m => f.map_smulₛₗ a m }
  have hl : IsBaseChange R' l :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hf) fun m => by
      exact (liftSemi_tmul _ 1 m).trans (one_smul _ _)
  haveI : IsLocalizedModule (Submonoid.powers r) l :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r) R' l).2 hl
  let N := Submodule.span R (Set.range Φ)
  have hle : Submodule.span R' (Set.range Φ') ≤ N.localized' R' (Submonoid.powers r) l := by
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hf.2 y
    induction z with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
    | tmul c m =>
      rw [liftSemi_tmul, map_smulₛₗ, ← hΦ]
      refine Submodule.smul_mem _ _ ⟨Φ m, Submodule.subset_span ⟨m, rfl⟩, 1, ?_⟩
      exact IsLocalizedModule.mk'_one _ _ _
  obtain ⟨m, hm, s, hs⟩ := hle hx
  have h1 : l m = l (s • x) := by
    rw [IsLocalizedModule.mk'_eq_iff] at hs
    rw [hs, Submonoid.smul_def, Submonoid.smul_def, map_smul]
    rfl
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers r) h1
  obtain ⟨n, hn⟩ := (c * s).2
  refine ⟨n, ?_⟩
  have : r ^ n • x = c • m := by
    rw [hc, smul_smul, Submonoid.smul_def, ← hn]
  rw [this]
  exact N.smul_mem _ hm

theorem pull_frobDR (p : ℕ) [Fact p.Prime] {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hR : (p : R) = 0) (hR' : (p : R') = 0) {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')}
    [GrpObj A'] {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A (spMap (algebraMap R R')) φ)
    (x : primDR A) :
    (bcMor hφ).pull (frobDR p R hR A x) = frobDR p R' hR' A' ((bcMor hφ).pull x) := by
  have k := (frobMor p R hR A (cast_left p R hR A)).comp (bcMor hφ)
  refine (GrpMor.pull_pull _ _ k (fun _ => rfl) rfl x).trans
    (GrpMor.pull_pull _ _ k (fun r => ?_) ?_ x).symm
  · rw [RingHom.comp_apply, frobR_apply, frobR_apply, map_pow]
  · exact GlobalTheory.VB.frob_naturality p _ φ _

theorem exists_conjSub : GlobalTheory.CovTop.Hypotheses2 → ∀ (p : ℕ) [Fact p.Prime] {T : Scheme.{0}}
    [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)),
    IsDRIso A H e →
    ∃ C : GlobalTheory.VB.Sub H, ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ C.sec V ↔ e V hV s ∈ GlobalTheory.ConjSeq.conjDR p Γ(T, V)
        (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V) (onAff A hV) := by
  intro P p _ T _ A _ g hA hg H e he
  have hp (V : T.Opens) : (p : Γ(T, V)) = 0 :=
    GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V
  refine exists_sub_of_affine
    (fun V hV => (conjDR p Γ(T, V) (hp V) (onAff A hV)).comap (e V hV).toLinearMap)
    (fun V W hV hW h s hs => ?_) fun V hV f s hs => ?_
  · letI := resAlg h
    obtain ⟨φ, hφ, hφ'⟩ := VB.exists_transition A hV hW h
    change e W hW _ ∈ conjDR p _ _ _
    rw [he V W hV hW h φ hφ hφ']
    have hle : conjDR p Γ(T, V) (hp V) (onAff A hV) ≤
        (conjDR p Γ(T, W) (hp W) (onAff A hW)).comap (bcMor hφ).pull := by
      rw [conjDR, Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      change (bcMor hφ).pull _ ∈ conjDR p _ _ _
      rw [pull_frobDR p (hp V) (hp W) hφ]
      exact Submodule.subset_span ⟨_, rfl⟩
    exact hle hs
  · have hD := hV.basicOpen f
    letI := resAlg (T.basicOpen_le f)
    obtain ⟨φ, hφ, hφ'⟩ := VB.exists_transition A hV hD (T.basicOpen_le f)
    have hbc : (bcMor hφ).IsBC :=
      (P.p5.2.2.1 _ (onAff A hV) g (VB.isAbelianScheme_onAff A hA hV) (VB.smooth_onAff A hg hV) _
        (onAff A hD) φ hφ).1
    change e _ hD _ ∈ conjDR p _ _ _ at hs
    rw [he V _ hV hD (T.basicOpen_le f) φ hφ hφ'] at hs
    haveI := hV.isLocalization_basicOpen f
    obtain ⟨n, hn⟩ := exists_pow_smul_mem_span f (bcMor hφ).pull hbc _ _
      (pull_frobDR p (hp V) (hp _) hφ) _ hs
    refine ⟨n, ?_⟩
    change e V hV _ ∈ conjDR p _ _ _
    rw [map_smul]
    exact hn

end GlobalTheory.ConjSeq.ConjSub
