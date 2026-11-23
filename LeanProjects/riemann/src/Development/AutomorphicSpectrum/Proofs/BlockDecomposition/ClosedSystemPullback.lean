import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh TensorProduct

namespace GlobalTheory.CompanionTheory.GE

attribute [local instance] algebraOfOver

variable {X Z : Scheme.{0}}

theorem pushforward_map_smulHom_appTop (φ : Z ⟶ X) (H : Z.Modules) (r : Γ(X, ⊤)) :
    (Scheme.Modules.pushforward φ).map (GroundTheory.Arith.SchemeCoh.smulHom H (φ.appTop r)) =
      GroundTheory.Arith.SchemeCoh.smulHom ((Scheme.Modules.pushforward φ).obj H) r := by
  ext U x
  rw [GroundTheory.Arith.SchemeCoh.smulHom_app_apply, GlobalTheory.QCoh.pushforward_smul]
  refine (GroundTheory.Arith.SchemeCoh.smulHom_app_apply H (φ.appTop r) (φ ⁻¹ᵁ U) x).trans ?_
  congr 1
  unfold GroundTheory.Arith.SchemeCoh.restrictTop
  have h := φ.naturality (homOfLE (le_top : U ≤ ⊤)).op
  have h2 := congrArg (fun g => CommRingCat.Hom.hom g r) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2.symm

theorem pullback_map_smulHom_appTop (φ : Z ⟶ X) (E : X.Modules) (a : Γ(X, ⊤)) :
    (Scheme.Modules.pullback φ).map (GroundTheory.Arith.SchemeCoh.smulHom E a) =
      GroundTheory.Arith.SchemeCoh.smulHom _ (φ.appTop a) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, pushforward_map_smulHom_appTop]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.naturality _).symm.trans
    (GroundTheory.Arith.SchemeCoh.smulHom_comp _ _)

theorem pullback_map_comp_eq_zero_iff (φ : Z ⟶ X) {D E : X.Modules} {Q : Z.Modules} (f : D ⟶ E)
    (q : (Scheme.Modules.pullback φ).obj E ⟶ Q) :
    (Scheme.Modules.pullback φ).map f ≫ q = 0 ↔
      f ≫ (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E Q q = 0 := by
  rw [← Adjunction.homEquiv_naturality_left]
  constructor
  · intro h
    rw [h, Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]
  · intro h
    apply ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv D Q).injective
    rw [h, Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

theorem appTop_algebraMap [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X)
    (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (a : A) :
    φ.appTop (algebraMap A Γ(X, ⊤) a) = algebraMap A Γ(Z, ⊤) a := by
  unfold GroundTheory.Arith.SchemeCoh.algebraOfOver GroundTheory.Arith.SchemeCoh.overAlgebra
  simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  rw [← hφ, Scheme.Hom.comp_appTop]
  rfl

theorem exists_smulHom_eq_comp_idealSumMap [X.Over (Spec (.of A))] (F : X.Modules) (J : Ideal A) {a : A}
    (ha : a ∈ J) : ∃ L : F ⟶ (⨁ fun _ : Fin (idealGenNum J) => F),
      GroundTheory.Arith.SchemeCoh.smulHom F (algebraMap A Γ(X, ⊤) a) = L ≫ idealSumMap F J := by
  rw [← GroundTheory.Arith.SchemeCoh.span_idealGen J] at ha
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 ha
  refine ⟨biproduct.lift fun k => GroundTheory.Arith.SchemeCoh.smulHom F (algebraMap A Γ(X, ⊤) (c k)), ?_⟩
  rw [GroundTheory.Arith.SchemeCoh.idealSumMap, biproduct.lift_desc, ← hc, map_sum,
    GroundTheory.Arith.SchemeCoh.smulHom_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, map_mul, GroundTheory.Arith.SchemeCoh.smulHom_comp_smulHom]

theorem arrow_comp_cokernel_eq_zero {C : X.Modules} {D T : Subobject C} (h : D ≤ T) :
    D.arrow ≫ cokernel.π T.arrow = 0 := by
  rw [← Subobject.ofLE_arrow h, Category.assoc, cokernel.condition, Limits.comp_zero]

theorem pullback_idealPowι_comp_eq_zero [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X)
    (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (E : X.Modules) (n : ℕ)
    {T : Subobject ((Scheme.Modules.pullback φ).obj E)}
    (hT : powSub I ((Scheme.Modules.pullback φ).obj E) n ≤ T) :
    (Scheme.Modules.pullback φ).map (idealPowι I E n) ≫ cokernel.π T.arrow = 0 := by
  have h0 : kernel.ι (cokernel.π (GroundTheory.Arith.SchemeCoh.idealSumMap
      ((Scheme.Modules.pullback φ).obj E) (I ^ n))) ≫ cokernel.π T.arrow = 0 := by
    change GroundTheory.Arith.SchemeCoh.idealPowι I ((Scheme.Modules.pullback φ).obj E) n ≫
      cokernel.π T.arrow = 0
    have e := Subobject.underlyingIso_arrow
      (GroundTheory.Arith.SchemeCoh.idealPowι I ((Scheme.Modules.pullback φ).obj E) n)
    have e2 : (Subobject.mk (GroundTheory.Arith.SchemeCoh.idealPowι I ((Scheme.Modules.pullback φ).obj E)
        n)).arrow ≫ cokernel.π T.arrow = 0 := arrow_comp_cokernel_eq_zero hT
    rw [← e, Category.assoc, e2, Limits.comp_zero]
  have hz : GroundTheory.Arith.SchemeCoh.idealSumMap ((Scheme.Modules.pullback φ).obj E) (I ^ n) ≫
      cokernel.π T.arrow = 0 := by
    rw [← kernel.lift_ι (cokernel.π (GroundTheory.Arith.SchemeCoh.idealSumMap _ (I ^ n)))
      (GroundTheory.Arith.SchemeCoh.idealSumMap _ (I ^ n)) (cokernel.condition _), Category.assoc, h0,
      Limits.comp_zero]
  have key : GroundTheory.Arith.SchemeCoh.idealSumMap E (I ^ n) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E _ (cokernel.π T.arrow) = 0 := by
    rw [GroundTheory.Arith.SchemeCoh.idealSumMap]
    apply biproduct.hom_ext'
    intro k
    rw [biproduct.ι_desc_assoc, Limits.comp_zero, ← Adjunction.homEquiv_naturality_left,
      pullback_map_smulHom_appTop, appTop_algebraMap φ hφ]
    obtain ⟨L, hL⟩ := exists_smulHom_eq_comp_idealSumMap ((Scheme.Modules.pullback φ).obj E) (I ^ n)
      (GroundTheory.Arith.SchemeCoh.idealGen_mem (I ^ n) k)
    rw [hL, Category.assoc, hz, Limits.comp_zero, Adjunction.homEquiv_unit, Functor.map_zero,
      Limits.comp_zero]
  rw [pullback_map_comp_eq_zero_iff]
  rw [show GroundTheory.Arith.SchemeCoh.idealPowι I E n =
      kernel.ι (cokernel.π (GroundTheory.Arith.SchemeCoh.idealSumMap E (I ^ n))) from rfl,
    ← cokernel.π_desc (GroundTheory.Arith.SchemeCoh.idealSumMap E (I ^ n)) _ key, kernel.condition_assoc,
    Limits.zero_comp]

private theorem isQuasicoherent_imageSubobject_of_isQuasicoherent {W : Scheme.{0}} {M N : W.Modules} (f : M ⟶ N)
    (T : Subobject N) (hT : T = imageSubobject f) :
    SheafOfModules.IsQuasicoherent M ∧ SheafOfModules.IsQuasicoherent N →
      SheafOfModules.IsQuasicoherent (Subobject.underlying.obj T) := by
  subst hT
  have e := (imageSubobjectIso f).symm
  intro h
  exact @GlobalTheory.QCoh.isQuasicoherent_of_iso _ _ _ e (@GlobalTheory.QCoh.isQuasicoherent_image _ _ _ f h.1 h.2)

theorem closedSys_pullSys {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))]
    [IsLocallyNoetherian X] (φ : Z ⟶ X) (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)))
    {E : X.Modules} (hE : IsCoherent E) {S : ℕ → Subobject E} (hS : ClosedSys I E S) :
    ClosedSys I ((Scheme.Modules.pullback φ).obj E) (pullSys I φ E S) := by
  have hle : ∀ e, S (e + 1) ≤ S e := fun e => by
    rw [hS.succ e]
    exact le_sup_left
  unfold GlobalTheory.CompanionTheory.GE.pullSys
  refine ⟨fun e => ?_, fun e => le_sup_right, fun e => ?_⟩
  · have hpb : SheafOfModules.IsQuasicoherent ((Scheme.Modules.pullback φ).obj E) :=
      @GlobalTheory.QCoh.isQuasicoherent_pullback _ _ φ E hE.1
    exact (GlobalTheory.CompanionTheory.GE.supsecs hpb _ _
      (isQuasicoherent_imageSubobject_of_isQuasicoherent ((Scheme.Modules.pullback φ).map (S e).arrow) _ rfl
        ⟨@GlobalTheory.QCoh.isQuasicoherent_pullback _ _ φ _ (hS.qcoh e), hpb⟩)
      ((@closedSys_pow A _ _ I _ _ ((Scheme.Modules.pullback φ).obj E) hpb).qcoh e)).1
  · apply le_antisymm
    · refine sup_le ?_ le_sup_right
      generalize hT : (imageSubobject ((Scheme.Modules.pullback φ).map (S (e + 1)).arrow) ⊔
          powSub I ((Scheme.Modules.pullback φ).obj E) (e + 1 + 1)) ⊔
          powSub I ((Scheme.Modules.pullback φ).obj E) (e + 1) = T
      have hT1 : imageSubobject ((Scheme.Modules.pullback φ).map (S (e + 1)).arrow) ≤ T := by
        rw [← hT]
        exact le_sup_left.trans le_sup_left
      have hT2 : powSub I ((Scheme.Modules.pullback φ).obj E) (e + 1) ≤ T := by
        rw [← hT]
        exact le_sup_right
      have hK : S e ≤ kernelSubobject ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E _
          (cokernel.π T.arrow)) := by
        rw [hS.succ e]
        refine sup_le (le_kernelSubobject _ _ ?_) (le_kernelSubobject _ _ ?_)
        · refine (pullback_map_comp_eq_zero_iff φ _ _).1 ?_
          have e1 := imageSubobject_arrow_comp ((Scheme.Modules.pullback φ).map (S (e + 1)).arrow)
          refine (congrArg (· ≫ cokernel.π T.arrow) e1).symm.trans ?_
          rw [Category.assoc, arrow_comp_cokernel_eq_zero hT1, Limits.comp_zero]
        · have e2 := (pullback_map_comp_eq_zero_iff φ _ _).1
            (pullback_idealPowι_comp_eq_zero I φ hφ E (e + 1) hT2)
          have e3 := Subobject.underlyingIso_hom_comp_eq_mk
            (GroundTheory.Arith.SchemeCoh.idealPowι I E (e + 1))
          exact (congrArg (· ≫ _) e3.symm).trans
            ((Category.assoc _ _ _).trans (by rw [e2]; exact Limits.comp_zero))
      have hz : (S e).arrow ≫ (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E _
          (cokernel.π T.arrow) = 0 := by
        rw [← Subobject.ofLE_arrow hK, Category.assoc, kernelSubobject_arrow_comp, Limits.comp_zero]
      exact imageSubobject_le _ (Abelian.monoLift _ _ ((pullback_map_comp_eq_zero_iff φ _ _).2 hz))
        (Abelian.monoLift_comp _ _ _)
    · have him : imageSubobject ((Scheme.Modules.pullback φ).map (S (e + 1)).arrow) ≤
          imageSubobject ((Scheme.Modules.pullback φ).map (S e).arrow) := by
        rw [← Subobject.ofLE_arrow (hle e), Functor.map_comp]
        exact imageSubobject_comp_le _ _
      exact sup_le (sup_le (him.trans le_sup_left)
        ((powSub_succ_le I _ (e + 1)).trans le_sup_right)) le_sup_right

end GlobalTheory.CompanionTheory.GE
