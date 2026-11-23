import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesNatural
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalIdealMul
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CechFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules}

omit [IsNoetherianRing A] in
lemma algV_eq_toFunctions (V : X.Opens) (a : A) : algV X V a = toFunctions V a := rfl

def powSmulTopΓ (V : X.Opens) (n : ℕ) : Submodule Γ(X, V) Γ(F, V) where
  carrier := (I ^ n • ⊤ : Submodule A Γ(F, V))
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c x hx := by
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y z hy hz => ?_)
    · change c • (a • y) ∈ (I ^ n • ⊤ : Submodule A Γ(F, V))
      rw [sectionsModuleA_smul, smul_smul, mul_comm, ← smul_smul, ← sectionsModuleA_smul]
      exact Submodule.smul_mem_smul ha trivial
    · rw [smul_add]
      exact add_mem hy hz

lemma mem_pow_smul_top_iff {V : X.Opens} (n : ℕ) (m : Γ(F, V)) :
    m ∈ (I ^ n • ⊤ : Submodule A Γ(F, V)) ↔
      m ∈ (Ideal.map (toFunctions V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(F, V)) := by
  constructor
  · intro hm
    refine Submodule.smul_induction_on hm (fun a ha x _ => ?_) (fun x y hx hy => add_mem hx hy)
    rw [sectionsModuleA_smul, algV_eq_toFunctions]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) trivial
  · intro hm
    have h : I ^ n ≤ ((powSmulTopΓ (F := F) I V n).colon (Set.univ)).comap (toFunctions V) := by
      intro a ha
      rw [Ideal.mem_comap, Submodule.mem_colon]
      intro x _
      change toFunctions V a • x ∈ (I ^ n • ⊤ : Submodule A Γ(F, V))
      rw [← algV_eq_toFunctions, ← sectionsModuleA_smul]
      exact Submodule.smul_mem_smul ha trivial
    have h' := Ideal.map_le_iff_le_comap.2 h
    have : (Ideal.map (toFunctions V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(F, V)) ≤
        powSmulTopΓ I V n :=
      Submodule.smul_le.2 fun c hc x _ => Submodule.mem_colon.1 (h' hc) x trivial
    exact this hm

variable [F.IsQuasicoherent]

lemma mem_range_idealPowι_iff {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ) (m : Γ(F, V)) :
    m ∈ Set.range ((idealPowι I F n).app V) ↔ m ∈ (I ^ n • ⊤ : Submodule A Γ(F, V)) := by
  rw [range_idealPowι_app I F hV n, mem_pow_smul_top_iff]
  rfl

variable (hF : IsCoherent F)

section Sections

variable {V : X.Opens} (hV : IsAffineOpen V)

def reesCoef (n : ℕ) : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) →+ Γ(F, V) where
  toFun s := (reesSectionsMap I hF hV s).coeff n
  map_zero' := by rw [reesSectionsMap_zero]; rfl
  map_add' s s' := by rw [reesSectionsMap_add]; rfl

lemma reesCoef_mem (n : ℕ) (s : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesCoef I hF hV n s ∈ Set.range ((idealPowι I F n).app V) :=
  (mem_range_idealPowι_iff I hV n _).2 ((mem_reesSubmodule_iff.1 (reesSectionsMap_mem hF hV s)) n)

lemma idealPowι_app_injective (n : ℕ) : Function.Injective ((idealPowι I F n).app V) :=
  kernel_ι_app_injective _ V

def reesDeg (n : ℕ) : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) →+ Γ(idealPow I F n, V) where
  toFun s := (Equiv.ofInjective _ (idealPowι_app_injective I n)).symm
    ⟨reesCoef I hF hV n s, reesCoef_mem I hF hV n s⟩
  map_zero' := by
    apply idealPowι_app_injective I n
    refine (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n) _).trans ?_
    change reesCoef I hF hV n 0 = _
    rw [map_zero, map_zero]
  map_add' s s' := by
    apply idealPowι_app_injective I n
    refine (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n) _).trans ?_
    change reesCoef I hF hV n (s + s') = _
    rw [map_add, map_add]
    congr 1
    · exact (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n)
        ⟨reesCoef I hF hV n s, reesCoef_mem I hF hV n s⟩).symm
    · exact (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n)
        ⟨reesCoef I hF hV n s', reesCoef_mem I hF hV n s'⟩).symm

lemma idealPowι_reesDeg (n : ℕ) (s : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    (idealPowι I F n).app V (reesDeg I hF hV n s) = reesCoef I hF hV n s :=
  Equiv.apply_ofInjective_symm (idealPowι_app_injective I n)
    ⟨reesCoef I hF hV n s, reesCoef_mem I hF hV n s⟩

include hV in
lemma lsingle_mem_reesSubmodule (n : ℕ) (g : Γ(idealPow I F n, V)) :
    PolynomialModule.lsingle A n ((idealPowι I F n).app V g) ∈ reesSubmodule I Γ(F, V) := by
  rw [mem_reesSubmodule_iff]
  intro k
  rw [PolynomialModule.lsingle_apply]
  split_ifs with h
  · subst h
    exact (mem_range_idealPowι_iff I hV n _).1 ⟨g, rfl⟩
  · exact zero_mem _

include hF hV in

def reesInc (n : ℕ) : Γ(idealPow I F n, V) →+ Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) :=
  (reesSectionsEquiv I hF hV).symm.toAddMonoidHom.comp
    (AddMonoidHom.codRestrict
      ((PolynomialModule.lsingle A n).toAddMonoidHom.comp ((idealPowι I F n).app V).hom)
      (reesSubmodule I Γ(F, V)).toAddSubmonoid (lsingle_mem_reesSubmodule I hV n))

lemma reesSectionsMap_reesInc (n : ℕ) (g : Γ(idealPow I F n, V)) :
    reesSectionsMap I hF hV (reesInc I hF hV n g) =
      PolynomialModule.lsingle A n ((idealPowι I F n).app V g) := by
  rw [← reesSectionsEquiv_apply]
  change ((reesSectionsEquiv I hF hV ((reesSectionsEquiv I hF hV).symm _)) :
    PolynomialModule A Γ(F, V)) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

lemma reesCoef_reesInc (n k : ℕ) (g : Γ(idealPow I F n, V)) :
    reesCoef I hF hV k (reesInc I hF hV n g) = if n = k then (idealPowι I F n).app V g else 0 := by
  change (reesSectionsMap I hF hV (reesInc I hF hV n g)).coeff k = _
  rw [reesSectionsMap_reesInc, PolynomialModule.lsingle_apply]

lemma reesDeg_reesInc (n : ℕ) (g : Γ(idealPow I F n, V)) :
    reesDeg I hF hV n (reesInc I hF hV n g) = g := by
  apply idealPowι_app_injective I n
  rw [idealPowι_reesDeg, reesCoef_reesInc, if_pos rfl]

lemma reesDeg_reesInc_of_ne {n k : ℕ} (h : n ≠ k) (g : Γ(idealPow I F n, V)) :
    reesDeg I hF hV k (reesInc I hF hV n g) = 0 := by
  apply idealPowι_app_injective I k
  rw [idealPowι_reesDeg, reesCoef_reesInc, if_neg h, map_zero]

end Sections

end

end GroundTheory.Arith.SchemeCoh
