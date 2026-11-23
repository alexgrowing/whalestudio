import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardSystemAffineSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobsonIdealFaithfulModuleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompleteModuleNoetherianRealizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSectionsStatement
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RestrictIso

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.LocTors

theorem chartIn_map {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) {N M : Type} [AddCommGroup N]
    [Module Γ(X, V) N] [AddCommGroup M] [Module Γ(X, V) M] (g : N →ₗ[Γ(X, V)] M)
    {T : Submodule Γ(X, V) N} {T' : Submodule Γ(X, V) M} (hT : T.map g ≤ T') {x : N}
    (hx : ChartIn φ V T x) : ChartIn φ V T' (g x) := by
  intro U hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  obtain ⟨y, hy⟩ := hx U hU h
  let g' : T →ₗ[Γ(X, V)] T' := (g.comp T.subtype).codRestrict T' (fun t => hT ⟨t, t.2, rfl⟩)
  refine ⟨g'.rTensor Γ(Z, U) y, ?_⟩
  have hc : T'.subtype.comp g' = g.comp T.subtype := rfl
  change (T'.subtype.rTensor Γ(Z, U)) (g'.rTensor Γ(Z, U) y) = g x ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U))
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hc, LinearMap.rTensor_comp,
    LinearMap.comp_apply, hy, LinearMap.rTensor_tmul]

theorem eq_zero_of_mem_pow {B R M : Type} [CommRing B] [CommRing R] [IsNoetherianRing R]
    [Algebra B R] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    [Module.Finite R M] (I : Ideal B) (hjac : I.map (algebraMap B R) ≤ Ideal.jacobson ⊥) (m : M)
    (hm : ∀ n, m ∈ (I ^ (n + 1) • ⊤ : Submodule B M)) : m = 0 := by
  set IR : Ideal R := I.map (algebraMap B R)
  have key : ∀ n, m ∈ (IR ^ n • ⊤ : Submodule R M) := by
    intro n
    have h1 : (I ^ (n + 1) • ⊤ : Submodule B M) ≤ (IR ^ (n + 1) • ⊤ : Submodule R M).restrictScalars B := by
      rw [Submodule.smul_le]
      intro a ha u _
      rw [Submodule.restrictScalars_mem, algebraMap_smul R a u |>.symm]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      have h2 : algebraMap B R a ∈ (I ^ (n + 1)).map (algebraMap B R) := Ideal.mem_map_of_mem _ ha
      rwa [Ideal.map_pow] at h2
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) (h1 (hm n))
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) IR hjac
  have : m ∈ (⨅ n : ℕ, IR ^ n • (⊤ : Submodule R M)) := Submodule.mem_iInf _ |>.2 key
  rw [hK] at this
  exact (Submodule.mem_bot R).1 this

theorem adjKer_pow_smul_mem_secs {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] (J : X.IdealSheafData)
    {Z : Scheme.{0}} [Z.Over (Spec (.of A))] (ψ : Z ⟶ J.subscheme) (hψ : IsProper ψ)
    (hover : (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)))
    (W : J.subscheme.Opens) (hW : IsIso (ψ ∣_ W)) {E : X.Modules} (hE : IsCoherent E)
    {S : ℕ → Subobject E} (hS : ClosedSys I E S) (hK : ∀ e, Killed J (S e))
    (B : Subobject ((Scheme.Modules.pullback (ψ ≫ J.subschemeι)).obj E))
    (hB : ∀ e, B ⊔ powSub I _ (e + 1) = pullSys I (ψ ≫ J.subschemeι) E S e)
    (V : X.affineOpens) (f : Γ(X, V)) (hf : J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W)
    (x : Γ(E, V)) (hx : x ∈ secs (adjKer (ψ ≫ J.subschemeι) B) V) :
    ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V := by
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  haveI : Module.Finite Γ(X, V) Γ(E, V) := hE.2 V V.2
  haveI : E.IsQuasicoherent := hE.1
  set IB : Ideal Γ(X, V) := Ideal.map (toFunctions (A := A) (V : X.Opens)) I with hIB
  have hpow : ∀ n, Ideal.map (toFunctions (A := A) (V : X.Opens)) (I ^ n) = IB ^ n :=
    fun n => Ideal.map_pow _ _ _
  let T : ℕ → Submodule Γ(X, V) Γ(E, V) := fun n => secsSub (S n) V
  have hpowsecs : ∀ n, secs (powSub I E n) V =
      ((IB ^ n • ⊤ : Submodule Γ(X, V) Γ(E, V)) : Set Γ(E, V)) := by
    intro n
    rw [GlobalTheory.T.ideal_power_subobject_sections I E hE.1 n V V.2, hpow]
  have h1 : ∀ n, IB ^ (n + 1) • (⊤ : Submodule Γ(X, V) Γ(E, V)) ≤ T n := by
    intro n y hy
    have hy' : y ∈ secs (powSub I E (n + 1)) V := by rw [hpowsecs]; exact hy
    exact (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 (hS.pow_le n) V hy'
  have h2 : ∀ n, T n = T (n + 1) ⊔ IB ^ (n + 1) • (⊤ : Submodule Γ(X, V) Γ(E, V)) := by
    intro n
    have hq : (powSub I E (n + 1) : X.Modules).IsQuasicoherent := (closedSys_pow I E).qcoh n
    obtain ⟨_, hsum⟩ := GlobalTheory.T.quasicoherent_sup_sections hE.1 (S (n + 1)) (powSub I E (n + 1)) (hS.qcoh (n + 1)) hq
    ext y
    change y ∈ secs (S n) V ↔ _
    rw [hS.succ n, hsum V V.2, Submodule.mem_sup]
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      refine ⟨s, hs, t, ?_, rfl⟩
      have ht' : t ∈ ((IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) Γ(E, V)) : Set Γ(E, V)) := by
        rw [← hpowsecs]; exact ht
      exact ht'
    · rintro ⟨s, hs, t, ht, rfl⟩
      refine ⟨s, hs, t, ?_, rfl⟩
      rw [hpowsecs]
      exact ht
  obtain ⟨R, firstRealIndex, secondRealIndex, iR3, M, familyMassRatio, familyMassSecondLine, iM3, iM4, iM5, μ, hjac, hspan, hiff⟩ :=
    GlobalTheory.T.complete_module_noetherian_realization IB T h1 h2
  have hJ : ∀ a ∈ J.ideal ⟨(V : X.Opens), V.2⟩, ∀ m : M, a • m = 0 := by
    intro a ha m
    have hm : m ∈ Submodule.span R (Set.range μ) := hspan ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun m _ => a • m = 0) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨e, rfl⟩
      apply eq_zero_of_mem_pow IB hjac
      intro n
      rw [← map_smul]
      exact (hiff n (a • e)).1 (hK n V a ha e)
    · exact smul_zero a
    · intro u v _ _ hu hv
      rw [smul_add, hu, hv, add_zero]
    · intro r u _ hu
      rw [smul_comm a r u, hu, smul_zero]
  have hIso : IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) :=
    GroundTheory.Arith.SchemeCoh.isIso_morphismRestrict_of_le ψ hf
  have hch := GlobalTheory.T.pushforward_system_affine_sections I (ψ ≫ J.subschemeι) hover hE hS B hB (V : X.Opens) V.2 x hx
  have hch' : ∀ n, ChartIn (ψ ≫ J.subschemeι) (V : X.Opens)
      (IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) (μ x) := by
    intro n
    refine chartIn_map _ _ μ ?_ (hch n)
    rintro _ ⟨e, he, rfl⟩
    exact (hiff n e).1 he
  obtain ⟨k, hk⟩ := GlobalTheory.T.jacobson_ideal_faithful_module J ψ hψ (V : X.Opens) V.2 IB hjac hJ f hIso (μ x) hch'
  refine ⟨k, fun n => ?_⟩
  have hμ : μ (f ^ k • x) ∈ (IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) := by
    rw [map_smul, hk]
    exact Submodule.zero_mem _
  exact (hiff n _).2 hμ

end GlobalTheory.CompanionTheory.GE.LocTors
