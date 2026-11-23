import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AssembleG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.ThetaPMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AlgTop

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem card_of_constr (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
    (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hη₂ : EtaNZD O cj Z₂ (t : E) (t' : E))
    (hf' : ∀ θ ∈ ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t',
      ∃ p : PairSet O cj hO Z₁ Z₂, (∀ m, θ (iL O cj hO Z₁ t t' m) = iL O cj hO Z₂ t t' (p.1.1 m)) ∧
        ∀ m, θ (iR O cj hO Z₁ t t' m) = iR O cj hO Z₂ t t' (p.1.2 m))
    (hb' : ∀ p : PairSet O cj hO Z₁ Z₂, ∃ θ ∈ ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t',
      (∀ m, θ (iL O cj hO Z₁ t t' m) = iL O cj hO Z₂ t t' (p.1.1 m)) ∧
        ∀ m, θ (iR O cj hO Z₁ t t' m) = iR O cj hO Z₂ t t' (p.1.2 m)) :
    Nat.card (ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t') =
      Nat.card (PairSet O cj hO Z₁ Z₂) := by
  choose F hF using hf'
  choose G hGmem hG using hb'
  have lamP : ∀ (q : PairSet O cj hO Z₁ Z₂) (m : MbMod Z₁),
      lamLQ O Z₂ hu₂ (q.1.1 m) = lamLQ O Z₁ hu₁ m := by
    intro q m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y₂, hy₂⟩ := Submodule.Quotient.mk_surjective _ (q.1.1 (Submodule.Quotient.mk y))
    rw [← hy₂, lamLQ_mk, lamLQ_mk]
    exact lam_keep O hu₁ hu₂ (q.1.1 : MbMod Z₁ →ₗ[O] MbMod Z₂) q.2.1.1 y y₂ hy₂.symm
  have lamQ : ∀ (q : PairSet O cj hO Z₁ Z₂) (m : MbMod (cjT O cj hO Z₁)),
      lamSQ O cj hO Z₂ hu₂ (q.1.2 m) = lamSQ O cj hO Z₁ hu₁ m := by
    intro q m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y₂, hy₂⟩ := Submodule.Quotient.mk_surjective _ (q.1.2 (Submodule.Quotient.mk y))
    rw [← hy₂, lamSQ_mk, lamSQ_mk]
    exact q.2.2.1 y y₂ hy₂.symm
  let f : ↥(ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) (t : E) (t' : E)) →
      PairSet O cj hO Z₁ Z₂ := fun θ => F θ.1 θ.2
  let g : PairSet O cj hO Z₁ Z₂ →
      ↥(ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) (t : E) (t' : E)) :=
    fun p => ⟨G p, hGmem p⟩
  have hfi : Function.Injective f := by
    intro θ θ' hθ
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hv : v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := (Sum.elim_comp_inl_inr v).symm
    rw [hv, mk_elim O cj hO Z₁ t t', map_add, map_add, (hF θ.1 θ.2).1, (hF θ.1 θ.2).2,
      (hF θ'.1 θ'.2).1, (hF θ'.1 θ'.2).2]
    change f θ = f θ' at hθ
    simp only [f] at hθ
    rw [hθ]
  have hgi : Function.Injective g := by
    intro p p' hp
    have h1 : G p = G p' := congrArg Subtype.val hp
    have k1 : ∀ m, p.1.1 m = p'.1.1 m := by
      intro m
      apply uniqL O cj hO Z₂ hu₂ t t' hη₂
      · rw [← (hG p).1, ← (hG p').1, h1]
      · rw [lamP p m, lamP p' m]
    have k2 : ∀ m, p.1.2 m = p'.1.2 m := by
      intro m
      apply uniqR O cj hO Z₂ hu₂ t t' hη₂
      · rw [← (hG p).2, ← (hG p').2, h1]
      · rw [lamQ p m, lamQ p' m]
    apply Subtype.ext
    apply Prod.ext
    · exact LinearEquiv.ext k1
    · exact LinearEquiv.ext k2
  obtain ⟨e, he⟩ := Function.Embedding.schroeder_bernstein hfi hgi
  exact Nat.card_congr (Equiv.ofBijective e he)

theorem bwd0 (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
    (ht : cj (t : E) = t) (ht' : cj (t' : E) = t') {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
    (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det) (p : PairSet O cj hO Z₁ Z₂) :
    ∃ θ ∈ ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t',
      (∀ m, θ (iL O cj hO Z₁ t t' m) = iL O cj hO Z₂ t t' (p.1.1 m)) ∧
        ∀ m, θ (iR O cj hO Z₁ t t' m) = iR O cj hO Z₂ t t' (p.1.2 m) := by
  refine ⟨thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p,
    thetaP_mem O cj hcj hO t t' ht ht' hu₁ hu₂ hκ₁ hκ₂ hG₁ hG₂ p, ?_, ?_⟩
  · intro m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have hy : p.1.1 (Submodule.Quotient.mk y) =
        Submodule.Quotient.mk (liftOf O (p.1.1 : MbMod Z₁ →ₗ[O] MbMod Z₂) y) :=
      (liftOf_spec O _ y).symm
    rw [iL_mk, hy, iL_mk]
    simp only [thetaP, thetaOf]
    erw [LinearEquiv.ofLinear_apply, Submodule.mapQ_apply, sumMap_apply]
    congr 1
    funext i
    cases i <;> simp <;> exact congrFun (map_zero _) _
  · intro m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have hy : p.1.2 (Submodule.Quotient.mk y) =
        Submodule.Quotient.mk
          (liftOf O (p.1.2 : MbMod (cjT O cj hO Z₁) →ₗ[O] MbMod (cjT O cj hO Z₂)) y) :=
      (liftOf_spec O _ y).symm
    rw [iR_mk, hy, iR_mk]
    simp only [thetaP, thetaOf]
    erw [LinearEquiv.ofLinear_apply, Submodule.mapQ_apply, sumMap_apply]
    congr 1
    funext i
    cases i <;> simp <;> exact congrFun (map_zero _) _

theorem stepPair_of_fwd (hf : FwdEx) : StepPair := by
  intro E _ O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hs₁ hs₂ hg₁ hg₂
  obtain ⟨t, rfl⟩ : ∃ t : O, (t : E) = T := ⟨⟨T, hT⟩, rfl⟩
  obtain ⟨t', rfl⟩ : ∃ t' : O, (t' : E) = T' := ⟨⟨T', hT'⟩, rfl⟩
  have hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0 :=
    hu₁.mul_left_eq_zero.mp ((kap_mul_det O Z₁ hu₁).trans hs₁)
  have hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0 :=
    hu₂.mul_left_eq_zero.mp ((kap_mul_det O Z₂ hu₂).trans hs₂)
  have hk : kap O Z₂ = kap O Z₁ := hκ₂.trans hκ₁.symm
  have hη : EtaNZD O cj Z₂ (t : E) (t' : E) := fun u hu => eta_nzd O cj hcj Z₂ hu₂ _ _ hg₂ u hu
  exact card_of_constr O cj hO t t' Z₁ Z₂ hu₁ hu₂ hη
    (hf E O cj hcj hO r t t' hcT hcT' Z₁ Z₂ hu₁ hu₂ hk hg₁ hg₂)
    (bwd0 O cj hcj hO t t' hcT hcT' hu₁ hu₂ hκ₁ hκ₂ hg₁ hg₂)

theorem locCnt0L_of_fwd (hf : FwdEx) : Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  locCnt0L_of_stepPair (stepPair_of_fwd hf)

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
