import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesSheaf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {F : X.Modules} {V V' : X.Opens} (hle : V' ≤ V)

lemma algV_res (a : A) : resO hle (algV X V a) = algV X V' a := by
  have := Scheme.Hom.appLE_map (X ↘ Spec (.of A)) (U := ⊤) (le_top : V ≤ _) (homOfLE hle).op
  exact congrArg (fun f : Γ(Spec (.of A), ⊤) ⟶ Γ(X, V') => f.hom ((Scheme.ΓSpecIso (.of A)).inv a))
    this

variable (I) in

abbrev resS : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) →+* Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V') :=
  resO (Scheme.Hom.preimage_mono _ hle)

lemma resS_reesInr (r : reesAlgebra I) : resS I hle (reesInr I V r) = reesInr I V' r := by
  have := Scheme.Hom.appLE_map (reesSnd I X) (U := ⊤) (le_top : reesPr I X ⁻¹ᵁ V ≤ _)
    (homOfLE (Scheme.Hom.preimage_mono _ hle)).op
  exact congrArg (fun f : Γ(Spec (.of (reesAlgebra I)), ⊤) ⟶ Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V') =>
    f.hom ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv r)) this

lemma resS_prApp (c : Γ(X, V)) :
    resS I hle ((reesPr I X).app V c) = (reesPr I X).app V' (resO hle c) := by
  have := (reesPr I X).naturality (homOfLE hle).op
  exact (congrArg (fun f : Γ(X, V) ⟶ Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V') => f.hom c) this).symm

lemma reesRingHom_res (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)) :
    reesRingHom hV' (resS I hle s) = (reesRingHom hV s).map (resO hle) := by
  have h := (isPushout_rees (I := I) hV).hom_ext
    (k := CommRingCat.ofHom ((reesRingHom hV').comp (resS I hle)))
    (l := CommRingCat.ofHom ((Polynomial.mapRingHom (resO hle)).comp (reesRingHom hV)))
    (by
      refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      change reesRingHom hV' (resS I hle ((reesPr I X).app V c)) =
        (reesRingHom hV ((reesPr I X).app V c)).map (resO hle)
      rw [resS_prApp, reesRingHom_inl, reesRingHom_inl, Polynomial.map_C])
    (by
      refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
      change reesRingHom hV' (resS I hle (reesInr I V r)) =
        (reesRingHom hV (reesInr I V r)).map (resO hle)
      rw [resS_reesInr, reesRingHom_inr, reesRingHom_inr, Polynomial.map_map]
      congr 1
      exact RingHom.ext fun a => (algV_res hle a).symm)
  exact congrArg (fun f : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) ⟶
    CommRingCat.of (Polynomial Γ(X, V')) => f.hom s) h

variable (F) in

def resFA : Γ(F, V) →ₗ[A] Γ(F, V') where
  toFun := resF F hle
  map_add' := map_add _
  map_smul' a m := by
    change resF F hle (algV X V a • m) = algV X V' a • resF F hle m
    rw [resF_smul, algV_res]

lemma resFA_apply (m : Γ(F, V)) : resFA (A := A) F hle m = resF F hle m := rfl

lemma app_resF {M N : X.Modules} (φ : M ⟶ N) {U U' : X.Opens} (h : U' ≤ U) (y : Γ(M, U)) :
    φ.app U' (resF M h y) = resF N h (φ.app U y) := by
  have := φ.mapPresheaf.naturality (homOfLE h).op
  exact congrArg (fun f => f.hom y) this

variable (hF : IsCoherent F) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')

lemma theta₁_res_coeff
    (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) (n : ℕ) :
    (theta₁ hF hV' (resF _ (Scheme.Hom.preimage_mono _ hle) y)).coeff n =
      resF F hle ((theta₁ hF hV y).coeff n) := by
  have hy : y ∈ Submodule.span Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)
      (Set.range (unitPr I F V)) := by
    rw [(isBaseChangeAt_reesPr (I := I) hF hV).span_range]
    trivial
  induction hy using Submodule.span_induction generalizing n with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    have hres : resF _ (Scheme.Hom.preimage_mono _ hle) (unitPr I F V m) =
        unitPr I F V' (resF F hle m) :=
      (Etale.pullbackUnitApp_res (reesPr I X) F (homOfLE hle) m).symm
    rw [hres, theta₁_unitPr, theta₁_unitPr, PolynomialModule.coeff_single,
      PolynomialModule.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs
    · rfl
    · exact (map_zero _).symm
  | zero => simp
  | add z z' _ _ hz hz' =>
    simp only [map_add, PolynomialModule.coeff_add, Finsupp.add_apply, hz, hz']
  | smul s z _ hz =>
    rw [Scheme.Modules.map_smul, theta₁_smul, theta₁_smul, reesRingHom_res hle hV hV',
      PolynomialModule.smul_apply, PolynomialModule.smul_apply, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Polynomial.coeff_map, hz, resF_smul]

theorem reesSectionsEquiv_res (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    (reesSectionsEquiv I hF hV' (resF _ (Scheme.Hom.preimage_mono _ hle) x) :
      PolynomialModule A Γ(F, V')) =
      PolynomialModule.map A (resFA F hle) (reesSectionsEquiv I hF hV x : PolynomialModule A Γ(F, V)) := by
  obtain ⟨y, rfl⟩ := surjective_reesSheafπ_app hF (hV.preimage (reesPr I X)) x
  rw [← app_resF, reesSectionsEquiv_apply, reesSectionsEquiv_apply, reesSectionsMap_π,
    reesSectionsMap_π]
  apply PolynomialModule.coeff_injective
  ext n
  exact theta₁_res_coeff hle hF hV hV' y n

end

section Base

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Scheme.{u}) [X.Over (Spec (.of A))]

instance [LocallyOfFiniteType (X ↘ Spec (.of A))] :
    LocallyOfFiniteType (reesScheme I X ↘ Spec (.of (reesAlgebra I))) := by
  change LocallyOfFiniteType (pullback.snd (X ↘ Spec (.of A)) (reesStructure I))
  infer_instance

variable {I X}

attribute [local instance] algebraOfOver in

lemma reesInr_eq_resO_algebraMap (V : X.Opens) (r : reesAlgebra I) :
    reesInr I V r = resO (le_top : reesPr I X ⁻¹ᵁ V ≤ ⊤)
      (algebraMap (reesAlgebra I) Γ(reesScheme I X, ⊤) r) :=
  rfl

end Base

end GroundTheory.Arith.SchemeCoh
