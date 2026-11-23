import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalDegree
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesCech
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules} [F.IsQuasicoherent] (hF : IsCoherent F)
  {ι : Type u} (𝔘 : ι → X.Opens)
  (hU : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a)))

omit [IsNoetherianRing A] [F.IsQuasicoherent] in
include hU in
lemma isAffineOpen_inter {m : ℕ} (t : Fin (m + 1) → ι) :
    IsAffineOpen (inter (X := X.toTopCat) 𝔘 t) := by
  rw [inter_eq_iInf]
  exact hU m t

set_option maxHeartbeats 2000000 in

lemma reesCoef_res {V V' : X.Opens} (hle : V' ≤ V) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (n : ℕ) (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesCoef I hF hV' n (resF _ (Scheme.Hom.preimage_mono _ hle) x) =
      resF F hle (reesCoef I hF hV n x) := by
  change (reesSectionsMap I hF hV' _).coeff n = resF F hle ((reesSectionsMap I hF hV x).coeff n)
  rw [← reesSectionsEquiv_apply, reesSectionsEquiv_res hle hF hV hV', reesSectionsEquiv_apply]
  rfl

set_option maxHeartbeats 2000000 in
lemma reesCoef_res' {V V' : X.Opens} (h : V' ≤ V) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (n : ℕ) (x : (reesPre I F).obj (op V)) :
    reesCoef I hF hV' n (res (reesPre I F) h x) = res (modulesAb F).obj h (reesCoef I hF hV n x) :=
  reesCoef_res I hF h hV hV' n x

set_option maxHeartbeats 2000000 in
lemma reesDeg_res' {V V' : X.Opens} (h : V' ≤ V) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (n : ℕ) (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesDeg I hF hV' n (res (reesPre I F) h x) =
      res (modulesAb (idealPow I F n)).obj h (reesDeg I hF hV n x) := by
  apply idealPowι_app_injective I n
  have e1 : res (modulesAb (idealPow I F n)).obj h (reesDeg I hF hV n x) =
    resF (idealPow I F n) h (reesDeg I hF hV n x) := rfl
  have e2 : res (reesPre I F) h x = resF (reesSheaf I F) (Scheme.Hom.preimage_mono _ h) x := rfl
  rw [e1, e2, idealPowι_reesDeg, app_resF, idealPowι_reesDeg]
  exact reesCoef_res I hF h hV hV' n x

set_option maxHeartbeats 2000000 in
lemma reesInc_res' {V V' : X.Opens} (h : V' ≤ V) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (n : ℕ) (x : Γ(idealPow I F n, V)) :
    reesInc I hF hV' n (res (modulesAb (idealPow I F n)).obj h x) =
      res (reesPre I F) h (reesInc I hF hV n x) := by
  apply reesSectionsMap_injective hF hV'
  have e1 : res (reesPre I F) h (reesInc I hF hV n x) =
    resF (reesSheaf I F) (Scheme.Hom.preimage_mono _ h) (reesInc I hF hV n x) := rfl
  have e2 : res (modulesAb (idealPow I F n)).obj h x = resF (idealPow I F n) h x := rfl
  rw [e1, e2, ← reesSectionsEquiv_apply hF hV' (resF _ _ _),
    reesSectionsEquiv_res h hF hV hV', reesSectionsEquiv_apply, reesSectionsMap_reesInc,
    reesSectionsMap_reesInc, PolynomialModule.map_lsingle, resFA_apply, app_resF]

def reesCoefFam (n : ℕ) : CechFamily (X := X.toTopCat) 𝔘 (reesPre I F) (modulesAb F).obj where
  φ t := reesCoef I hF (isAffineOpen_inter 𝔘 hU t) n
  res_comm _ _ h x := reesCoef_res' I hF h _ _ n x

set_option maxHeartbeats 2000000 in

def reesDegFam (n : ℕ) : CechFamily (X := X.toTopCat) 𝔘 (reesPre I F)
    (modulesAb (idealPow I F n)).obj where
  φ t := reesDeg I hF (isAffineOpen_inter 𝔘 hU t) n
  res_comm _ _ h x := reesDeg_res' I hF h _ _ n x

set_option maxHeartbeats 2000000 in

def reesIncFam (n : ℕ) : CechFamily (X := X.toTopCat) 𝔘 (modulesAb (idealPow I F n)).obj
    (reesPre I F) where
  φ t := reesInc I hF (isAffineOpen_inter 𝔘 hU t) n
  res_comm _ _ h x := reesInc_res' I hF h _ _ n x

end

end GroundTheory.Arith.SchemeCoh
