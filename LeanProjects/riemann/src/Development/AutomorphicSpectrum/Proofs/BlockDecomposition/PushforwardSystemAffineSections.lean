import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Chart

attribute [local instance] algebraOfOver

variable {X Z : Scheme.{0}}

theorem idealPowι_comp_pullback_map_cokernel_eq_zero {A : Type} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X)
    (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (E : X.Modules) (D : Subobject E) (m : ℕ)
    (hD : powSub I E m ≤ D) :
    idealPowι I ((Scheme.Modules.pullback φ).obj E) m ≫
      (Scheme.Modules.pullback φ).map (cokernel.π D.arrow) = 0 := by
  apply (cancel_epi (Abelian.factorThruImage
    (idealSumMap ((Scheme.Modules.pullback φ).obj E) (I ^ m)))).1
  rw [comp_zero, ← Category.assoc, Abelian.image.fac]
  apply biproduct.hom_ext'
  intro k
  rw [comp_zero, idealSumMap, biproduct.ι_desc_assoc, smulHom_comp, ← appTop_algebraMap φ hφ,
    ← pullback_map_smulHom_appTop, ← Functor.map_comp, ← smulHom_comp]
  obtain ⟨L, hL⟩ := exists_smulHom_eq_comp_idealSumMap E (I ^ m) (idealGen_mem (I ^ m) k)
  have hι : idealPowι I E m ≫ cokernel.π D.arrow = 0 := by
    have h := Subobject.ofMkLE_arrow (f := idealPowι I E m) (X := D) hD
    rw [← h, Category.assoc, cokernel.condition, comp_zero]
  rw [hL, ← Abelian.image.fac (idealSumMap E (I ^ m)), Category.assoc, Category.assoc, hι,
    comp_zero, comp_zero, Functor.map_zero]

theorem chartIn_of_pullback_app_eq_zero (φ : Z ⟶ X) {E : X.Modules} [E.IsQuasicoherent]
    (D : Subobject E) [(D : X.Modules).IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V)
    (x : Γ(E, V))
    (hx : ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ φ ⁻¹ᵁ V,
      ((Scheme.Modules.pullback φ).map (cokernel.π D.arrow)).app U
        (GlobalTheory.QCoh.pullbackSections φ E h x) = 0) :
    ChartIn φ V (secsSub D V) x := by
  intro U hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  have hx' := hx U hU h
  rw [GlobalTheory.QCoh.pullback_map_app_pullbackSections] at hx'
  letI := GlobalTheory.QCoh.appLEModule φ ((Scheme.Modules.pullback φ).obj (cokernel D.arrow)) h
  haveI := GlobalTheory.QCoh.appLE_isScalarTower φ ((Scheme.Modules.pullback φ).obj (cokernel D.arrow)) h
  have hbc := GlobalTheory.QCoh.isBaseChange_pullbackSections φ (cokernel D.arrow) hU hV h
  let πl : Γ(E, V) →ₗ[Γ(X, V)] Γ(cokernel D.arrow, V) :=
    { toFun := (cokernel.π D.arrow).app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  have hsurj : Function.Surjective πl := surjective_cokernel_π_app D.arrow hV
  have hex : Function.Exact (secsSub D V).subtype πl := by
    intro m
    have hm : m ∈ Set.range (secsSub D V).subtype ↔ m ∈ Set.range (D.arrow.app V) := by
      rw [Submodule.coe_subtype, Subtype.range_coe_subtype]
      rfl
    rw [hm, mem_range_app_iff D.arrow hV m]
    rfl
  have hex' := rTensor_exact Γ(Z, U) hex hsurj
  refine (hex' _).1 ?_
  rw [LinearMap.rTensor_tmul]
  have h1 : (1 : Γ(Z, U)) ⊗ₜ[Γ(X, V)] πl x = 0 := by
    apply hbc.equiv.injective
    rw [hbc.equiv_tmul, one_smul, map_zero]
    exact hx'
  rw [← TensorProduct.comm_tmul, h1, map_zero]

theorem chartIn_adjKer : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X),
    φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E →
    ∀ {S : ℕ → Subobject E}, ClosedSys I E S →
    ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)),
    (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∀ (V : X.Opens), IsAffineOpen V →
    ∀ x ∈ secs (adjKer φ B) V, ∀ n, ChartIn φ V (secsSub (S n) V) x := by
  intro A _ _ I X Z _ _ _ φ hφ E hE S hS B hB V hV x hx n
  have : E.IsQuasicoherent := hE.1
  have : ((S n : Subobject E) : X.Modules).IsQuasicoherent := hS.qcoh n
  apply chartIn_of_pullback_app_eq_zero φ (S n) V hV x
  intro U hU h
  obtain ⟨y, rfl⟩ := hx
  set g := (Scheme.Modules.pullback φ).map (cokernel.π (S n).arrow) with hg
  have hK : pullSys I φ E S n ≤ kernelSubobject g := by
    refine sup_le (image_le_kernel _ _ ?_) (le_kernelSubobject _ _ ?_)
    · rw [hg, ← Functor.map_comp, cokernel.condition, Functor.map_zero]
    · rw [powSub, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
        idealPowι_comp_pullback_map_cokernel_eq_zero I φ hφ E (S n) (n + 1) (hS.pow_le n),
        comp_zero]
  have hBle : B ≤ kernelSubobject g := by
    rw [← hB n] at hK
    exact le_sup_left.trans hK
  have hBg : B.arrow ≫ g = 0 := by
    rw [← Subobject.ofLE_arrow hBle, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
  have h0 : (adjMap φ B).app V ((adjKer φ B).arrow.app V y) = 0 := by
    have hk : (adjKer φ B).arrow ≫ adjMap φ B = 0 := kernelSubobject_arrow_comp _
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hk]
    rfl
  have h1 : (cokernel.π B.arrow).app (φ ⁻¹ᵁ V)
      (((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app E).app V
        ((adjKer φ B).arrow.app V y)) = 0 := by
    rw [adjMap, Adjunction.homEquiv_unit] at h0
    exact h0
  have hfac : g = cokernel.π B.arrow ≫ cokernel.desc B.arrow g hBg := (cokernel.π_desc _ _ _).symm
  have h2 : (cokernel.π B.arrow).app U
      (GlobalTheory.QCoh.pullbackSections φ E h ((adjKer φ B).arrow.app V y)) = 0 := by
    rw [GlobalTheory.QCoh.pullbackSections_apply]
    erw [GlobalTheory.QCoh.hom_app_res (cokernel.π B.arrow) h]
    rw [h1, map_zero]
  rw [hfac, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, h2, map_zero]

end GlobalTheory.CompanionTheory.GE.Chart
