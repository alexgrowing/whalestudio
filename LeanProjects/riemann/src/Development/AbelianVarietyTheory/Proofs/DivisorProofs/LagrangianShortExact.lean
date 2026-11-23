import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace Limits
open GlobalTheory.LB (resG_self)
open GlobalTheory.Twist (resM resM_self)
open GlobalTheory.QCoh (appLinear appLinear_apply appLinear_comp)

namespace GlobalTheory.VB.Lagr

theorem alg {R M P : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup P]
    [Module R P] {g : ℕ} (bM : Module.Basis (Fin (2 * g)) R M) (bP : Module.Basis (Fin g) R P)
    (j : P →ₗ[R] M) (hj : Function.Injective j) (N : Submodule R M)
    (hN : IsCompl (LinearMap.range j) N) (B : M →ₗ[R] Module.Dual R M)
    (hB : Function.Bijective B) (hiso : ∀ s s', B (j s) (j s') = 0)
    (φ : M →ₗ[R] Module.Dual R P) (hφ : ∀ t s, φ t s = B t (j s)) :
    Function.Surjective φ ∧ ∀ t, φ t = 0 → t ∈ LinearMap.range j := by
  classical
  let e₀ : P ≃ₗ[R] LinearMap.range j := LinearEquiv.ofInjective j hj
  let p : M →ₗ[R] P := e₀.symm.toLinearMap ∘ₗ Submodule.projectionOnto _ N hN
  have hpj (s : P) : p (j s) = s := by
    have : j s = ((e₀ s : LinearMap.range j) : M) := rfl
    show e₀.symm (Submodule.projectionOnto _ N hN (j s)) = s
    rw [this, Submodule.projectionOnto_apply_left, LinearEquiv.symm_apply_apply]
  have hpN (n : M) (hn : n ∈ N) : p n = 0 := by
    show e₀.symm (Submodule.projectionOnto _ N hN n) = 0
    rw [(Submodule.projectionOnto_apply_eq_zero_iff hN).2 hn, map_zero]
  have hφj (s : P) : φ (j s) = 0 := LinearMap.ext fun s' => (hφ _ _).trans (hiso s s')
  have hsurj : Function.Surjective φ := fun l => by
    obtain ⟨t, ht⟩ := hB.2 (l ∘ₗ p)
    exact ⟨t, LinearMap.ext fun s => by rw [hφ, ht, LinearMap.comp_apply, hpj]⟩
  have hsurjN (l : Module.Dual R P) : ∃ n ∈ N, φ n = l := by
    obtain ⟨t, rfl⟩ := hsurj l
    obtain ⟨k, hk, n, hn, rfl⟩ := Submodule.mem_sup.1
      (hN.codisjoint.eq_top ▸ Submodule.mem_top : t ∈ LinearMap.range j ⊔ N)
    obtain ⟨s, rfl⟩ := hk
    exact ⟨n, hn, by rw [map_add, hφj, zero_add]⟩
  let Θ : M →ₗ[R] P × Module.Dual R P := LinearMap.prod p φ
  have hΘ : Function.Surjective Θ := by
    rintro ⟨s, l⟩
    obtain ⟨n, hn, rfl⟩ := hsurjN l
    refine ⟨j s + n, ?_⟩
    show (p (j s + n), φ (j s + n)) = (s, φ n)
    rw [map_add, map_add, hpj, hpN n hn, hφj, add_zero, zero_add]
  let bQ := bP.prod bP.dualBasis
  let e : (P × Module.Dual R P) ≃ₗ[R] M :=
    bQ.equiv bM (finSumFinEquiv.trans (finCongr (two_mul g).symm))
  haveI : Module.Finite R M := Module.Finite.of_basis bM
  have hinj : Function.Injective Θ := by
    have := OrzechProperty.injective_of_surjective_endomorphism (e.toLinearMap ∘ₗ Θ)
      (e.surjective.comp hΘ)
    exact fun a b hab => this (by simp [hab])
  refine ⟨hsurj, fun t ht => ⟨p t, ?_⟩⟩
  have : Θ (t - j (p t)) = 0 := by
    show (p (t - j (p t)), φ (t - j (p t))) = (0, 0)
    rw [map_sub, map_sub, hpj, sub_self, ht, hφj, sub_self]
  exact (sub_eq_zero.1 (hinj (this.trans (map_zero Θ).symm))).symm

end GlobalTheory.VB.Lagr

namespace GlobalTheory.VB.Lagr

variable {X : Scheme.{0}}

def evU (F : X.Modules) (U : X.Opens) : Γ(dual F, U) →ₗ[Γ(X, U)] Module.Dual Γ(X, U) Γ(F, U) where
  toFun l := dualApp l le_rfl
  map_add' l l' := dualApp_add l l' le_rfl
  map_smul' a l := by
    rw [dualApp_smul, resG_self]
    rfl

@[simp] theorem evU_apply (F : X.Modules) (U : X.Opens) (l : Γ(dual F, U)) (s : Γ(F, U)) :
    evU F U l s = dualApp l le_rfl s := rfl

theorem evU_bijective {F : X.Modules} {U : X.Opens} {r : ℕ} {e : Fin r → Γ(F, U)} (he : IsFrame e) :
    Function.Bijective (evU F U) := by
  refine ⟨fun l l' hll' => he.dual_ext le_rfl fun i => ?_, fun lf => ?_⟩
  · exact LinearMap.congr_fun hll' _
  · refine ⟨(he.dual.basis le_rfl).equivFun.symm fun i => lf (resM F le_rfl (e i)), ?_⟩
    refine (he.basis le_rfl).ext fun i => ?_
    rw [IsFrame.basis_apply, evU_apply, ← he.dual_basis_repr le_rfl, ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply]

end GlobalTheory.VB.Lagr

namespace GlobalTheory.VB

open Lagr

theorem lagrangian_shortExact : ∀ (T : Scheme.{0}) (g : ℕ) (F H : T.Modules), GlobalTheory.VB.IsVB F g →
    GlobalTheory.VB.IsVB H (2 * g) →
    ∀ (i : F ⟶ H) (β : H ⟶ GlobalTheory.VB.dual H), IsIso β →
    (∀ (V : T.Opens), IsAffineOpen V → Function.Injective (GlobalTheory.QCoh.appLinear i V) ∧
      ∃ N : Submodule Γ(T, V) Γ(H, V), IsCompl (LinearMap.range (GlobalTheory.QCoh.appLinear i V)) N) →
    ∀ w : i ≫ β ≫ GlobalTheory.VB.dualMap i = 0, (ShortComplex.mk i (β ≫ GlobalTheory.VB.dualMap i) w).ShortExact := by
  intro T g F H hF hH i β hβ hloc w

  have key (V : T.Opens) (x : T) (hx : x ∈ V) : ∃ U : T.Opens, U ≤ V ∧ x ∈ U ∧
      Function.Surjective ((β ≫ dualMap i).app U) ∧
      ∀ t : Γ(H, U), (β ≫ dualMap i).app U t = 0 → ∃ u, i.app U u = t := by
    obtain ⟨U₁, eH, -, hx₁, hle₁, heH⟩ := hH.exists_affine hx
    obtain ⟨U, eF, hU, hxU, hle, heF⟩ := hF.exists_affine hx₁
    have heH' := heH.res hle
    obtain ⟨hinj, N, hN⟩ := hloc U hU
    have hβU : Function.Bijective (β.app U) := ConcreteCategory.bijective_of_isIso (β.app U)
    let B := evU H U ∘ₗ appLinear β U
    have hB : Function.Bijective B := (evU_bijective heH').comp hβU
    have hiso (s s' : Γ(F, U)) : B (appLinear i U s) (appLinear i U s') = 0 := by
      have hw := congrArg (fun f => appLinear f U s) w
      simp only [appLinear_comp, LinearMap.comp_apply, GlobalTheory.QCoh.appLinear_zero,
        LinearMap.zero_apply] at hw
      have := congrArg (fun l => dualApp l le_rfl s') hw
      simp only [appLinear_apply, dualApp_dualMap, dualApp_zero, LinearMap.zero_apply] at this
      exact this
    let φ := evU F U ∘ₗ appLinear (β ≫ dualMap i) U
    have hφ (t : Γ(H, U)) (s : Γ(F, U)) : φ t s = B t (appLinear i U s) := rfl
    obtain ⟨hsurj, hker⟩ := alg (heH'.basis le_rfl) (heF.basis le_rfl) (appLinear i U) hinj N hN
      B hB hiso φ hφ
    have hevF := evU_bijective heF
    refine ⟨U, hle.trans hle₁, hxU, fun l => ?_, fun t ht => ?_⟩
    · obtain ⟨t, ht⟩ := hsurj (evU F U l)
      exact ⟨t, hevF.1 ht⟩
    · obtain ⟨u, hu⟩ := hker t (by
        show evU F U ((β ≫ dualMap i).app U t) = 0
        rw [ht, map_zero])
      exact ⟨u, hu⟩
  refine ShortComplex.ShortExact.mk' (DualExact.exact_of_locally _ fun V x hx => ?_)
    (QCoh.mono_of_locally_app_injective i fun V x hx => ?_)
    (QCoh.epi_of_locally_app_surjective _ fun V x hx => ?_)
  · obtain ⟨U, hU, hxU, -, hex⟩ := key V x hx
    exact ⟨U, hU, hxU, hex⟩
  · obtain ⟨U, hU, hxU, hle⟩ := QCoh.exists_affine_mem_le x hx
    exact ⟨U, hxU, hle, (hloc U hU).1⟩
  · obtain ⟨U, hU, hxU, hs, -⟩ := key V x hx
    exact ⟨U, hxU, hU, hs⟩

end GlobalTheory.VB
