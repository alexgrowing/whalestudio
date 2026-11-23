import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.GsEquivSpec

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
variable (hO : ∀ x ∈ O, cj x ∈ O)
include hO

section Props

variable (t t' : O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
  (θ : DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t')

theorem elim_split (Y : Ix r → O) :
    (Submodule.Quotient.mk Y : DDc O cj (Z₂.map O.subtype) t t') =
      iL O cj hO Z₂ t t' (Submodule.Quotient.mk (fun a => Y (Sum.inl a))) +
        iR O cj hO Z₂ t t' (Submodule.Quotient.mk (fun b => Y (Sum.inr b))) := by
  have e1 : iL O cj hO Z₂ t t' (Submodule.Quotient.mk (fun a => Y (Sum.inl a))) =
      (Submodule.Quotient.mk (elimL O (fun a => Y (Sum.inl a))) : DDc O cj (Z₂.map O.subtype) t t') := rfl
  have e2 : iR O cj hO Z₂ t t' (Submodule.Quotient.mk (fun b => Y (Sum.inr b))) =
      (Submodule.Quotient.mk (elimR O (fun b => Y (Sum.inr b))) : DDc O cj (Z₂.map O.subtype) t t') := rfl
  rw [e1, e2, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  rcases i with i | i <;> simp [elimL, elimR]

theorem gs_e (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t') (hκ : kap O Z₂ = kap O Z₁)
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') :
    gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ (eCl (cjT O cj hO Z₁)) = eCl (cjT O cj hO Z₂) := by
  have sp := gsEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ (eCl (cjT O cj hO Z₁))
  have hp : ((Submodule.Quotient.mk (Sum.elim (0 : Fin (r + 1) → O) (Pi.single (Fin.last r) 1)) :
      DDc O cj (Z₁.map O.subtype) t t'), ((0 : E), (1 : E))) ∈ GamC' O cj (Z₁.map O.subtype) t t' :=
    ⟨Sum.elim 0 (Pi.single (Fin.last r) 1), fun b => Pi.single_eq_of_ne (Fin.castSucc_ne_last b) _,
      by simp [lamC, Matrix.mulVec, dotProduct]⟩
  obtain ⟨Y₂, hY₂, he⟩ := gam_fwd' O cj t t' Z₁ Z₂ θ hΓ' _ hp
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3⟩ := he
  have hr : (fun b => Y₂ (Sum.inr b)) = Pi.single (Fin.last r) 1 := by
    funext b
    refine Fin.lastCases ?_ (fun j => ?_) b
    · rw [Pi.single_eq_same]; exact Subtype.ext h3.symm
    · rw [hY₂ j, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  set gs := gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (gs (eCl (cjT O cj hO Z₁)))
  have key : iR O cj hO Z₂ t t' (gs (eCl (cjT O cj hO Z₁))) =
      iL O cj hO Z₂ t t' (Submodule.Quotient.mk (fun a => Y₂ (Sum.inl a))) +
        iR O cj hO Z₂ t t' (eCl (cjT O cj hO Z₂)) := by
    rw [← sp.1, eCl, iR_mk]
    show θ (Submodule.Quotient.mk (Sum.elim 0 (Pi.single (Fin.last r) 1))) = _
    rw [show θ (Submodule.Quotient.mk (Sum.elim 0 (Pi.single (Fin.last r) 1))) = Submodule.Quotient.mk Y₂ from h1,
      elim_split O cj hO t t' Z₂, hr]
    rfl
  have hz : (Submodule.Quotient.mk (Sum.elim (fun a => Y₂ (Sum.inl a)) (Pi.single (Fin.last r) 1 - v)) :
      DDc O cj (Z₂.map O.subtype) t t') = 0 := by
    rw [mk_elim O cj hO Z₂ t t', Submodule.Quotient.mk_sub, map_sub, ← eCl, hv, key]
    abel
  have hl : lamL O Z₂ (fun a => Y₂ (Sum.inl a)) = 0 := by rw [lamL_apply]; exact h2.symm
  have hl' : lamS O cj Z₂ (Pi.single (Fin.last r) 1 - v) = 0 := by
    have e1 := sp.2
    rw [← hv, lamSQ_mk, eCl, lamSQ_mk, lamS_e'] at e1
    rw [lamS_sub, lamS_e', e1, hκ, sub_self]
  have := (ker_zero O cj hO Z₂ hu₂ t t' hη₂ _ _ hz hl hl').2
  rw [Submodule.Quotient.mk_sub, sub_eq_zero] at this
  rw [← hv, ← this]
  rfl

theorem g_e (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t') (hκ : kap O Z₂ = kap O Z₁)
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') :
    gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' (eCl Z₁) = eCl Z₂ := by
  have sp := gEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' (eCl Z₁)
  have hp : ((Submodule.Quotient.mk (Sum.elim (Pi.single (Fin.last r) 1) (0 : Fin (r + 1) → O)) :
      DDc O cj (Z₁.map O.subtype) t t'), ((1 : E), (0 : E))) ∈ GamC O cj (Z₁.map O.subtype) t t' :=
    ⟨Sum.elim (Pi.single (Fin.last r) 1) 0, fun a => Pi.single_eq_of_ne (Fin.castSucc_ne_last a) _,
      by simp [lamStarC]⟩
  obtain ⟨Y₂, hY₂, he⟩ := gam_fwd O cj t t' Z₁ Z₂ θ hΓ _ hp
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3⟩ := he
  have hl0 : (fun a => Y₂ (Sum.inl a)) = Pi.single (Fin.last r) 1 := by
    funext b
    refine Fin.lastCases ?_ (fun j => ?_) b
    · rw [Pi.single_eq_same]; exact Subtype.ext h2.symm
    · rw [hY₂ j, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  set g := gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ'
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (g (eCl Z₁))
  have key : iL O cj hO Z₂ t t' (g (eCl Z₁)) =
      iL O cj hO Z₂ t t' (eCl Z₂) +
        iR O cj hO Z₂ t t' (Submodule.Quotient.mk (fun b => Y₂ (Sum.inr b))) := by
    rw [← sp.1, eCl, iL_mk]
    show θ (Submodule.Quotient.mk (Sum.elim (Pi.single (Fin.last r) 1) 0)) = _
    rw [show θ (Submodule.Quotient.mk (Sum.elim (Pi.single (Fin.last r) 1) 0)) = Submodule.Quotient.mk Y₂ from h1,
      elim_split O cj hO t t' Z₂, hl0]
    rfl
  have hz : (Submodule.Quotient.mk (Sum.elim (v - Pi.single (Fin.last r) 1) (-(fun b => Y₂ (Sum.inr b)))) :
      DDc O cj (Z₂.map O.subtype) t t') = 0 := by
    rw [mk_elim O cj hO Z₂ t t', Submodule.Quotient.mk_sub, Submodule.Quotient.mk_neg, map_sub, map_neg, ← eCl,
      hv, key]
    abel
  have hl : lamL O Z₂ (v - Pi.single (Fin.last r) 1) = 0 := by
    have e1 := sp.2
    rw [← hv, lamLQ_mk, eCl, lamLQ_mk, lamL_e'] at e1
    rw [map_sub, lamL_e', e1, hκ, sub_self]
  have hl' : lamS O cj Z₂ (-(fun b => Y₂ (Sum.inr b))) = 0 := by
    have : lamS O cj Z₂ (fun b => Y₂ (Sum.inr b)) = 0 := h3.symm
    rw [show (-(fun b => Y₂ (Sum.inr b)) : Fin (r + 1) → O) = 0 - (fun b => Y₂ (Sum.inr b)) by rw [zero_sub],
      lamS_sub, lamS_zero, this, sub_zero]
  have := (ker_zero O cj hO Z₂ hu₂ t t' hη₂ _ _ hz hl hl').1
  rw [Submodule.Quotient.mk_sub, sub_eq_zero] at this
  rw [← hv, this]
  rfl

theorem g_b (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hη₁ : EtaNZD O cj Z₁ t t') (hη₂ : EtaNZD O cj Z₂ t t') (hκ : kap O Z₂ = kap O Z₁)
    (hΓ : (fun p => (θ p.1, p.2)) '' GamC O cj (Z₁.map O.subtype) t t' = GamC O cj (Z₂.map O.subtype) t t')
    (hΓ' : (fun p => (θ p.1, p.2)) '' GamC' O cj (Z₁.map O.subtype) t t' = GamC' O cj (Z₂.map O.subtype) t t') :
    gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' (bCls Z₁) = bCls Z₂ := by
  have sp := gEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' (bCls Z₁)
  have sps := gsEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ (eCl (cjT O cj hO Z₁))
  apply uniqL O cj hO Z₂ hu₂ t t' hη₂
  · rw [← sp.1, rel_b, map_smul, map_smul, sps.1, gs_e O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hκ hΓ hΓ', rel_b,
      map_smul]
  · rw [sp.2, bCls, bCls, lamLQ_mk, lamLQ_mk, lamL_b O Z₁ hu₁, lamL_b O Z₂ hu₂]

end Props

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
