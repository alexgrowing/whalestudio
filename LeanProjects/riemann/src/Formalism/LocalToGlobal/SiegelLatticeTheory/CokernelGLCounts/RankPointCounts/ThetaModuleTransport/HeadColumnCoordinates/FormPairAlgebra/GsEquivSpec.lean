import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.GsLinSpec
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.PairGSteps

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
variable (hO : ∀ x ∈ O, cj x ∈ O)
include hO

theorem rel_b (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (t t' : O) :
    iL O cj hO Z t t' (bCls Z) = iR O cj hO Z t t' (t' • eCl (cjT O cj hO Z)) := by
  unfold bCls eCl
  rw [map_smul, iL, iR, Submodule.liftQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.eq, mem_relC_iff O cj hO Z t t']
  refine ⟨0, Pi.single (Fin.last r) 1, ?_, ?_⟩
  · funext j
    simp [elimL, elimR, Matrix.mulVec_single, Pi.single_apply]
  · funext j
    simp [elimL, elimR, Matrix.mulVec_zero, Pi.single_apply]

section Fwd

variable (t t' : O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
  (θ : DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t')

omit hO in
theorem gam_fwd (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t') : ∀ p ∈ GamC O cj (Z₁.map O.subtype) t t',
    (θ.toLinearMap p.1, p.2) ∈ GamC O cj (Z₂.map O.subtype) t t' := by
  intro p hp
  rw [← hΓ]
  exact ⟨p, hp, rfl⟩

omit hO in
theorem gam_bwd (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t') : ∀ p ∈ GamC O cj (Z₂.map O.subtype) t t',
    (θ.symm.toLinearMap p.1, p.2) ∈ GamC O cj (Z₁.map O.subtype) t t' := by
  intro p hp
  rw [← hΓ] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have e : θ.symm.toLinearMap (θ q.1) = q.1 := θ.symm_apply_apply q.1
  show (θ.symm.toLinearMap (θ q.1), q.2) ∈ _
  rw [e]
  exact hq

omit hO in
theorem gam_fwd' (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') : ∀ p ∈ GamC' O cj (Z₁.map O.subtype) t t',
    (θ.toLinearMap p.1, p.2) ∈ GamC' O cj (Z₂.map O.subtype) t t' := by
  intro p hp
  rw [← hΓ']
  exact ⟨p, hp, rfl⟩

omit hO in
theorem gam_bwd' (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') : ∀ p ∈ GamC' O cj (Z₂.map O.subtype) t t',
    (θ.symm.toLinearMap p.1, p.2) ∈ GamC' O cj (Z₁.map O.subtype) t t' := by
  intro p hp
  rw [← hΓ'] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have e : θ.symm.toLinearMap (θ q.1) = q.1 := θ.symm_apply_apply q.1
  show (θ.symm.toLinearMap (θ q.1), q.2) ∈ _
  rw [e]
  exact hq

def gsEquiv (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det) (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t')
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t') :
    MbMod (cjT O cj hO Z₁) ≃ₗ[O] MbMod (cjT O cj hO Z₂) :=
  LinearEquiv.ofLinear (gsLin O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd O cj t t' Z₁ Z₂ θ hΓ))
    (gsLin O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd O cj t t' Z₁ Z₂ θ hΓ))
    (by
      apply LinearMap.ext; intro m
      have s1 := gsLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd O cj t t' Z₁ Z₂ θ hΓ)
      have s2 := gsLin_spec O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd O cj t t' Z₁ Z₂ θ hΓ)
      apply uniqR O cj hO Z₂ hu₂ t t' hη₂
      · rw [LinearMap.comp_apply, ← (s1 _).1, ← (s2 m).1, LinearMap.id_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      · rw [LinearMap.comp_apply, (s1 _).2, (s2 m).2, LinearMap.id_apply])
    (by
      apply LinearMap.ext; intro m
      have s1 := gsLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd O cj t t' Z₁ Z₂ θ hΓ)
      have s2 := gsLin_spec O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd O cj t t' Z₁ Z₂ θ hΓ)
      apply uniqR O cj hO Z₁ hu₁ t t' hη₁
      · rw [LinearMap.comp_apply, ← (s2 _).1, ← (s1 m).1, LinearMap.id_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      · rw [LinearMap.comp_apply, (s2 _).2, (s1 m).2, LinearMap.id_apply])

def gEquiv (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det) (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') :
    MbMod Z₁ ≃ₗ[O] MbMod Z₂ :=
  LinearEquiv.ofLinear (gLin O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd' O cj t t' Z₁ Z₂ θ hΓ'))
    (gLin O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd' O cj t t' Z₁ Z₂ θ hΓ'))
    (by
      apply LinearMap.ext; intro m
      have s1 := gLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd' O cj t t' Z₁ Z₂ θ hΓ')
      have s2 := gLin_spec O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd' O cj t t' Z₁ Z₂ θ hΓ')
      apply uniqL O cj hO Z₂ hu₂ t t' hη₂
      · rw [LinearMap.comp_apply, ← (s1 _).1, ← (s2 m).1, LinearMap.id_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      · rw [LinearMap.comp_apply, (s1 _).2, (s2 m).2, LinearMap.id_apply])
    (by
      apply LinearMap.ext; intro m
      have s1 := gLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd' O cj t t' Z₁ Z₂ θ hΓ')
      have s2 := gLin_spec O cj hO t t' Z₂ Z₁ hu₂ hu₁ hη₁ θ.symm.toLinearMap (gam_bwd' O cj t t' Z₁ Z₂ θ hΓ')
      apply uniqL O cj hO Z₁ hu₁ t t' hη₁
      · rw [LinearMap.comp_apply, ← (s2 _).1, ← (s1 m).1, LinearMap.id_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
      · rw [LinearMap.comp_apply, (s2 _).2, (s1 m).2, LinearMap.id_apply])

theorem gsEquiv_spec (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det) (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t')
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t') (m : MbMod (cjT O cj hO Z₁)) :
    θ (iR O cj hO Z₁ t t' m) = iR O cj hO Z₂ t t' (gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ m) ∧
      lamSQ O cj hO Z₂ hu₂ (gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ m) = lamSQ O cj hO Z₁ hu₁ m := gsLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd O cj t t' Z₁ Z₂ θ hΓ) m

theorem gEquiv_spec (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det) (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') (m : MbMod Z₁) :
    θ (iL O cj hO Z₁ t t' m) = iL O cj hO Z₂ t t' (gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' m) ∧
      lamLQ O Z₂ hu₂ (gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' m) = lamLQ O Z₁ hu₁ m := gLin_spec O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη₂ θ.toLinearMap (gam_fwd' O cj t t' Z₁ Z₂ θ hΓ') m

end Fwd

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
