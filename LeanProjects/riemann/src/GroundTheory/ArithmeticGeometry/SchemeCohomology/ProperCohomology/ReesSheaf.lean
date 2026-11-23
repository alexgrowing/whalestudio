import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

instance sectionsModuleA (A : Type u) [CommRing A] {X : Scheme.{u}} [X.Over (Spec (.of A))]
    (F : X.Modules) (V : X.Opens) : Module A Γ(F, V) :=
  Module.compHom _ (algV X V)

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {F : X.Modules} {V : X.Opens}

lemma sectionsModuleA_smul (a : A) (m : Γ(F, V)) : a • m = algV X V a • m := rfl

variable (A) in

def toPolyA (q : PolynomialModule Γ(X, V) Γ(F, V)) : PolynomialModule A Γ(F, V) :=
  PolynomialModule.ofCoeff A q.coeff

@[simp] lemma coeff_toPolyA (q : PolynomialModule Γ(X, V) Γ(F, V)) (n : ℕ) :
    (toPolyA A q).coeff n = q.coeff n := rfl

lemma toPolyA_add (q q' : PolynomialModule Γ(X, V) Γ(F, V)) :
    toPolyA A (q + q') = toPolyA A q + toPolyA A q' := rfl

lemma toPolyA_injective : Function.Injective (toPolyA A (F := F) (V := V)) := fun q q' h =>
  PolynomialModule.coeff_injective (R := Γ(X, V))
    (show q.coeff = q'.coeff from congrArg (fun p : PolynomialModule A Γ(F, V) => p.coeff) h)

lemma smul_mem_pow_smul {i j : ℕ} {c : Γ(X, V)} (hc : c ∈ (I.map (algV X V)) ^ i)
    {m : Γ(F, V)} (hm : m ∈ I ^ j • (⊤ : Submodule A Γ(F, V))) :
    c • m ∈ I ^ (i + j) • (⊤ : Submodule A Γ(F, V)) := by
  rw [← Ideal.map_pow] at hc
  have hstab : ∀ (d : Γ(X, V)) {k : ℕ} {x : Γ(F, V)}, x ∈ I ^ k • (⊤ : Submodule A Γ(F, V)) →
      d • x ∈ I ^ k • (⊤ : Submodule A Γ(F, V)) := by
    intro d k x hx
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
    · have : d • (a • y) = a • (d • y) := by
        rw [sectionsModuleA_smul, sectionsModuleA_smul, smul_smul, smul_smul, mul_comm]
      rw [this]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [smul_add]
      exact add_mem hy hy'
  refine Submodule.span_induction (p := fun c _ => c • m ∈ I ^ (i + j) • (⊤ : Submodule A Γ(F, V)))
    ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨a, ha, rfl⟩
    rw [← sectionsModuleA_smul, pow_add, mul_smul]
    exact Submodule.smul_mem_smul ha hm
  · simp
  · intro x y _ _ hx hy
    rw [add_smul]
    exact add_mem hx hy
  · intro d x _ hx
    rw [smul_eq_mul, mul_smul]
    exact hstab d hx

lemma toPolyA_smul_mem {p : Polynomial Γ(X, V)} (hp : p ∈ reesCoeffRing I X V)
    {q : PolynomialModule Γ(X, V) Γ(F, V)} (hq : toPolyA A q ∈ reesSubmodule I Γ(F, V)) :
    toPolyA A (p • q) ∈ reesSubmodule I Γ(F, V) := by
  intro n
  rw [coeff_toPolyA, PolynomialModule.smul_apply]
  refine Submodule.sum_mem _ fun x hx => ?_
  have hx : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  rw [← hx]
  exact smul_mem_pow_smul (hp x.1) (hq x.2)

lemma toPolyA_map_smul (r : reesAlgebra I) (q : PolynomialModule Γ(X, V) Γ(F, V)) :
    toPolyA A (((r : Polynomial A).map (algV X V)) • q) = r • toPolyA A q := by
  apply PolynomialModule.coeff_injective
  ext n
  change (((r : Polynomial A).map (algV X V)) • q).coeff n =
    ((r : Polynomial A) • toPolyA A q).coeff n
  rw [PolynomialModule.smul_apply, PolynomialModule.smul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Polynomial.coeff_map, coeff_toPolyA]
  rfl

variable (hF : IsCoherent F) (hV : IsAffineOpen V)

def targetToPolySec (z : Γ(reesTarget I F, reesPr I X ⁻¹ᵁ V)) : polySec I F V := z

lemma targetToPolySec_add (z z' : Γ(reesTarget I F, reesPr I X ⁻¹ᵁ V)) :
    targetToPolySec (z + z') = targetToPolySec z + targetToPolySec z' := rfl

lemma targetToPolySec_injective :
    Function.Injective (targetToPolySec (I := I) (F := F) (V := V)) := fun _ _ h => h

lemma targetToPolySec_smul (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V))
    (z : Γ(reesTarget I F, reesPr I X ⁻¹ᵁ V)) :
    targetToPolySec (s • z) = (reesPolyMap I X).app _ s • targetToPolySec z := rfl

lemma targetToPolySec_ι_π (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    targetToPolySec ((reesSheafι I F).app _ ((reesSheafπ I F).app _ y)) = unitB I F V y := by
  have h := congrArg (fun f => (Scheme.Modules.Hom.app f (reesPr I X ⁻¹ᵁ V)) y) (reesSheafπ_ι I F)
  exact h

variable (I) in

def reesSectionsMap (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) : PolynomialModule A Γ(F, V) :=
  toPolyA A (thetaMap hF hV (targetToPolySec ((reesSheafι I F).app _ x)))

lemma reesSectionsMap_add (x x' : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesSectionsMap I hF hV (x + x') = reesSectionsMap I hF hV x + reesSectionsMap I hF hV x' := by
  rw [reesSectionsMap, map_add, targetToPolySec_add, map_add, toPolyA_add]
  rfl

lemma reesSectionsMap_zero : reesSectionsMap I hF hV 0 = 0 := by
  change toPolyA A (thetaMap hF hV (targetToPolySec ((reesSheafι I F).app _ 0))) = 0
  rw [map_zero, show targetToPolySec (0 : Γ(reesTarget I F, reesPr I X ⁻¹ᵁ V)) = 0 from rfl,
    map_zero]
  rfl

lemma reesSectionsMap_injective : Function.Injective (reesSectionsMap I hF hV) :=
  toPolyA_injective.comp ((thetaMap_injective hF hV).comp
    (targetToPolySec_injective.comp (injective_reesSheafι_app _)))

lemma reesSectionsMap_π (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    reesSectionsMap I hF hV ((reesSheafπ I F).app _ y) = toPolyA A (theta₁ hF hV y) := by
  rw [reesSectionsMap, targetToPolySec_ι_π, thetaMap_unitB]

lemma reesSectionsMap_mem (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesSectionsMap I hF hV x ∈ reesSubmodule I Γ(F, V) := by
  obtain ⟨y, rfl⟩ := surjective_reesSheafπ_app hF (hV.preimage (reesPr I X)) x
  rw [reesSectionsMap_π]
  have hy : y ∈ Submodule.span Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)
      (Set.range (unitPr I F V)) := by
    rw [(isBaseChangeAt_reesPr (I := I) hF hV).span_range]
    trivial
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    rw [theta₁_unitPr]
    exact single_zero_mem_reesSubmodule I Γ(F, V) m
  | zero => rw [map_zero]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    rw [map_add, toPolyA_add]
    exact add_mem hz hz'
  | smul s z _ hz =>
    rw [theta₁_smul]
    exact toPolyA_smul_mem (reesRingHom_mem hV s) hz

lemma reesSectionsMap_smul (r : reesAlgebra I) (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesSectionsMap I hF hV (reesInr I V r • x) = r • reesSectionsMap I hF hV x := by
  rw [reesSectionsMap, Scheme.Modules.Hom.app_smul, targetToPolySec_smul, thetaMap_smul,
    ← RingHom.comp_apply, ← reesRingHom, reesRingHom_inr, toPolyA_map_smul]
  rfl

lemma reesSectionsMap_surjective (p : reesSubmodule I Γ(F, V)) :
    ∃ x, reesSectionsMap I hF hV x = p := by
  obtain ⟨p, hp⟩ := p
  rw [reesSubmodule_eq_span] at hp
  change ∃ x, reesSectionsMap I hF hV x = p
  refine Submodule.span_induction (p := fun z _ => ∃ x, reesSectionsMap I hF hV x = z)
    ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨m, rfl⟩
    refine ⟨(reesSheafπ I F).app _ (unitPr I F V m), ?_⟩
    rw [reesSectionsMap_π, theta₁_unitPr]
    rfl
  · exact ⟨0, reesSectionsMap_zero hF hV⟩
  · rintro z z' _ _ ⟨x, hx⟩ ⟨x', hx'⟩
    exact ⟨x + x', by rw [reesSectionsMap_add, hx, hx']⟩
  · rintro r z _ ⟨x, hx⟩
    exact ⟨reesInr I V r • x, by rw [reesSectionsMap_smul, hx]⟩

variable (I) in

def reesSectionsEquiv : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) ≃+ reesSubmodule I Γ(F, V) :=
  AddEquiv.ofBijective
    ({ toFun := fun x => ⟨reesSectionsMap I hF hV x, reesSectionsMap_mem hF hV x⟩
       map_zero' := Subtype.ext (reesSectionsMap_zero hF hV)
       map_add' := fun x x' => Subtype.ext (reesSectionsMap_add hF hV x x') } :
      Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) →+ reesSubmodule I Γ(F, V))
    ⟨fun x x' h => reesSectionsMap_injective hF hV (congrArg Subtype.val h), fun p => by
      obtain ⟨x, hx⟩ := reesSectionsMap_surjective hF hV p
      exact ⟨x, Subtype.ext hx⟩⟩

lemma reesSectionsEquiv_apply (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    (reesSectionsEquiv I hF hV x : PolynomialModule A Γ(F, V)) = reesSectionsMap I hF hV x := rfl

end

end GroundTheory.Arith.SchemeCoh
