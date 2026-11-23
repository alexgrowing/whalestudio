import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesSheafBase
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {F : X.Modules} {V : X.Opens}

variable (I F V) in

abbrev unitPr : Γ(F, V) →+ Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) :=
  Etale.pullbackUnitApp (reesPr I X) F V

variable (I F V) in

abbrev unitB : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →+
    Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V)) :=
  Etale.pullbackUnitApp (reesPolyMap I X) ((Scheme.Modules.pullback (reesPr I X)).obj F)
    (reesPr I X ⁻¹ᵁ V)

variable (hF : IsCoherent F) (hV : IsAffineOpen V)

include hF hV in
lemma isBaseChangeAt_reesPr : IsBaseChangeAt (reesPr I X) F V := by
  have := hF.1
  exact isBaseChangeAt_of_isAffineOpen _ F hV (hV.preimage _)

include hF hV in
lemma isBaseChangeAt_reesPolyMap :
    IsBaseChangeAt (reesPolyMap I X) ((Scheme.Modules.pullback (reesPr I X)).obj F)
      (reesPr I X ⁻¹ᵁ V) := by
  have := (isCoherent_pullback_reesPr (I := I) hF).1
  exact isBaseChangeAt_of_isAffineOpen _ _ (hV.preimage _) ((hV.preimage _).preimage _)

lemma single_zero_smul_compat (a : Γ(X, V)) (m : Γ(F, V)) :
    PolynomialModule.single Γ(X, V) 0 (a • m) =
      reesRingHom (I := I) hV ((reesPr I X).app V a) • PolynomialModule.single Γ(X, V) 0 m := by
  rw [reesRingHom_inl, ← Polynomial.monomial_zero_left, PolynomialModule.monomial_smul_single,
    zero_add]

include hF in
lemma exists_theta₁ : ∃ θ : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →+
    PolynomialModule Γ(X, V) Γ(F, V),
    (∀ m, θ (unitPr I F V m) = PolynomialModule.single Γ(X, V) 0 m) ∧
    (∀ (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)) y, θ (s • y) = reesRingHom (I := I) hV s • θ y) := by
  let _ : Module Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) (PolynomialModule Γ(X, V) Γ(F, V)) :=
    Module.compHom _ (reesRingHom (I := I) hV)
  obtain ⟨θ, hθ, -⟩ := isBaseChangeAt_reesPr (I := I) hF hV _
    (PolynomialModule.lsingle Γ(X, V) 0 : Γ(F, V) →ₗ[Γ(X, V)] _).toAddMonoidHom
    (fun a m => single_zero_smul_compat hV a m)
  exact ⟨θ.toAddMonoidHom, hθ, fun s y => θ.map_smul s y⟩

def theta₁ : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →+
    PolynomialModule Γ(X, V) Γ(F, V) :=
  (exists_theta₁ hF hV).choose

lemma theta₁_unitPr (m : Γ(F, V)) :
    theta₁ hF hV (unitPr I F V m) = PolynomialModule.single Γ(X, V) 0 m :=
  (exists_theta₁ hF hV).choose_spec.1 m

lemma theta₁_smul (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V))
    (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    theta₁ hF hV (s • y) = reesRingHom (I := I) hV s • theta₁ hF hV y :=
  (exists_theta₁ hF hV).choose_spec.2 s y

include hF in
lemma exists_theta : ∃ θ : Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V)) →+
    PolynomialModule Γ(X, V) Γ(F, V),
    (∀ y, θ (unitB I F V y) = theta₁ hF hV y) ∧
    (∀ (s : polyRing I V) x, θ (s • x) = polyRingHom (I := I) hV s • θ x) := by
  let _ : Module (polyRing I V) (PolynomialModule Γ(X, V) Γ(F, V)) :=
    Module.compHom _ (polyRingHom (I := I) hV)
  obtain ⟨θ, hθ, -⟩ := isBaseChangeAt_reesPolyMap (I := I) hF hV _ (theta₁ hF hV)
    (fun s y => theta₁_smul hF hV s y)
  exact ⟨θ.toAddMonoidHom, hθ, fun s x => θ.map_smul s x⟩

def thetaMap : Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V)) →+
    PolynomialModule Γ(X, V) Γ(F, V) :=
  (exists_theta hF hV).choose

lemma thetaMap_unitB (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    thetaMap hF hV (unitB I F V y) = theta₁ hF hV y :=
  (exists_theta hF hV).choose_spec.1 y

lemma polyRingInv_polyRingHom (s : polyRing I V) :
    polyRingInv (I := I) (V := V) (polyRingHom hV s) = s :=
  (polyRingEquiv hV).symm_apply_apply s

lemma thetaMap_smul (s : polyRing I V) (x : Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V))) :
    thetaMap hF hV (s • x) = polyRingHom (I := I) hV s • thetaMap hF hV x :=
  (exists_theta hF hV).choose_spec.2 s x

variable (I F V) in

abbrev polySec := Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V))

variable (I F V) in

def lambdaMap : PolynomialModule Γ(X, V) Γ(F, V) →+ polySec I F V where
  toFun q := q.coeff.sum fun n m =>
    (polyRingInv (I := I) (V := V) (Polynomial.X ^ n)) • unitB I F V (unitPr I F V m)
  map_zero' := by simp
  map_add' q q' := by
    simp only [PolynomialModule.coeff_add]
    rw [Finsupp.sum_add_index']
    · intro n
      simp
    · intro n m m'
      rw [map_add, map_add, smul_add]

lemma lambdaMap_single (n : ℕ) (m : Γ(F, V)) :
    lambdaMap I F V (PolynomialModule.single Γ(X, V) n m) =
      (polyRingInv (I := I) (V := V) (Polynomial.X ^ n)) • unitB I F V (unitPr I F V m) := by
  simp [lambdaMap, Finsupp.sum_single_index]

lemma unitB_unitPr_smul (c : Γ(X, V)) (m : Γ(F, V)) :
    unitB I F V (unitPr I F V (c • m)) = polyInl I V c • unitB I F V (unitPr I F V m) := by
  rw [unitPr, pullbackUnitApp_smul_at, unitB, pullbackUnitApp_smul_at]
  rfl

lemma lambdaMap_smul (p : Polynomial Γ(X, V)) (q : PolynomialModule Γ(X, V) Γ(F, V)) :
    lambdaMap I F V (p • q) = polyRingInv (I := I) (V := V) p • lambdaMap I F V q := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' => rw [add_smul, map_add, hp, hp', map_add, add_smul]
  | monomial i c =>
    induction q using PolynomialModule.induction_linear with
    | zero => simp
    | add q q' h h' => rw [smul_add, map_add, h, h', map_add, smul_add]
    | single j m =>
      rw [PolynomialModule.monomial_smul_single, lambdaMap_single, lambdaMap_single,
        unitB_unitPr_smul, smul_smul, smul_smul, polyRingInv, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X_pow,
        Polynomial.eval₂_X_pow, Polynomial.eval₂_monomial, pow_add]
      congr 1
      ring

include hF hV in
lemma lambdaMap_theta₁ (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    lambdaMap I F V (theta₁ hF hV y) = unitB I F V y := by
  let _ : Module Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) (polySec I F V) :=
    Module.compHom _ ((reesPolyMap I X).app (reesPr I X ⁻¹ᵁ V)).hom
  let L1 : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →ₗ[
      Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)] polySec I F V :=
    { toFun := fun y => lambdaMap I F V (theta₁ hF hV y)
      map_add' := fun y y' => by rw [map_add, map_add]
      map_smul' := fun s y => by
        rw [theta₁_smul, lambdaMap_smul, reesRingHom, RingHom.comp_apply,
          polyRingInv_polyRingHom]
        rfl }
  let L2 : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →ₗ[
      Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)] polySec I F V :=
    { toFun := unitB I F V
      map_add' := map_add _
      map_smul' := fun s y => pullbackUnitApp_smul_at _ _ _ s y }
  obtain ⟨ψ, -, huniq⟩ := isBaseChangeAt_reesPr (I := I) hF hV (polySec I F V)
    ((unitB I F V).comp (unitPr I F V)) (fun a m => unitB_unitPr_smul a m)
  have e1 := huniq L1 (fun m => by
    change lambdaMap I F V (theta₁ hF hV (unitPr I F V m)) = _
    rw [theta₁_unitPr, lambdaMap_single, pow_zero, map_one, one_smul]
    rfl)
  have e2 := huniq L2 (fun m => rfl)
  exact congrArg (fun L : _ →ₗ[Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)] polySec I F V => L y)
    (e1.trans e2.symm)

include hF hV in

theorem lambdaMap_thetaMap (x : polySec I F V) : lambdaMap I F V (thetaMap hF hV x) = x := by
  let L3 : polySec I F V →ₗ[polyRing I V] polySec I F V :=
    { toFun := fun x => lambdaMap I F V (thetaMap hF hV x)
      map_add' := fun x x' => by rw [map_add, map_add]
      map_smul' := fun s x => by
        rw [thetaMap_smul, lambdaMap_smul, polyRingInv_polyRingHom]
        rfl }
  obtain ⟨ψ, -, huniq⟩ := isBaseChangeAt_reesPolyMap (I := I) hF hV (polySec I F V)
    (unitB I F V) (fun s y => pullbackUnitApp_smul_at _ _ _ s y)
  have e1 := huniq L3 (fun y => by
    change lambdaMap I F V (thetaMap hF hV (unitB I F V y)) = _
    rw [thetaMap_unitB, lambdaMap_theta₁])
  have e2 := huniq LinearMap.id (fun y => rfl)
  exact congrArg (fun L : polySec I F V →ₗ[polyRing I V] polySec I F V => L x) (e1.trans e2.symm)

include hF hV in
lemma thetaMap_injective : Function.Injective (thetaMap (I := I) hF hV) :=
  Function.LeftInverse.injective (lambdaMap_thetaMap hF hV)

end

end GroundTheory.Arith.SchemeCoh
