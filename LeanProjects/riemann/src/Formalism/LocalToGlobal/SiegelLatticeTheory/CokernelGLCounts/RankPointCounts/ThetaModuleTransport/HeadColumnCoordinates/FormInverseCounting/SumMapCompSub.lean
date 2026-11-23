import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.FormCAddRight

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def liftOf {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (f : MbMod Z →ₗ[O] MbMod Z') :
    (Fin (r + 1) → O) →ₗ[O] (Fin (r + 1) → O) :=
  (Module.projective_lifting_property (headCols Z').mkQ (f ∘ₗ (headCols Z).mkQ)
    (Submodule.mkQ_surjective _)).choose

theorem liftOf_spec {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (f : MbMod Z →ₗ[O] MbMod Z')
    (y : Fin (r + 1) → O) :
    (Submodule.Quotient.mk (liftOf O f y) : MbMod Z') = f (Submodule.Quotient.mk y) := LinearMap.congr_fun (Module.projective_lifting_property (headCols Z').mkQ (f ∘ₗ (headCols Z).mkQ)
    (Submodule.mkQ_surjective _)).choose_spec y

def sumMap (g gs : (Fin (r + 1) → O) →ₗ[O] (Fin (r + 1) → O)) : (Ix r → O) →ₗ[O] (Ix r → O) where
  toFun Y := Sum.elim (g fun j => Y (Sum.inl j)) (gs fun j => Y (Sum.inr j))
  map_add' Y W := by
    have h1 : (fun j => (Y + W) (Sum.inl j)) = (fun j => Y (Sum.inl j)) + (fun j => W (Sum.inl j)) := rfl
    have h2 : (fun j => (Y + W) (Sum.inr j)) = (fun j => Y (Sum.inr j)) + (fun j => W (Sum.inr j)) := rfl
    rw [h1, h2, map_add, map_add]
    funext i; cases i <;> rfl
  map_smul' c Y := by
    have h1 : (fun j => (c • Y) (Sum.inl j)) = c • (fun j => Y (Sum.inl j)) := rfl
    have h2 : (fun j => (c • Y) (Sum.inr j)) = c • (fun j => Y (Sum.inr j)) := rfl
    rw [h1, h2, map_smul, map_smul]
    funext i; cases i <;> rfl

theorem sumMap_apply (g gs : (Fin (r + 1) → O) →ₗ[O] (Fin (r + 1) → O)) (Y : Ix r → O) :
    sumMap O g gs Y = Sum.elim (g fun j => Y (Sum.inl j)) (gs fun j => Y (Sum.inr j)) := rfl

variable (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
variable {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}

theorem mk_gen (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (c₂ : Fin (r + 1) → O) (s : O) :
    (Submodule.Quotient.mk (Z.mulVec c₂ - s • Pi.single (Fin.last r) 1) : MbMod Z) =
      c₂ (Fin.last r) • bCls Z - s • eCl Z := by
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
  congr 1
  unfold bCls
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  have hsum : Z.mulVec c₂ - c₂ (Fin.last r) • (fun i => Z i (Fin.last r)) =
      ∑ a : Fin r, c₂ a.castSucc • (fun i => Z i a.castSucc) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Fin.sum_univ_castSucc]
    simp only [mul_comm]
    ring
  rw [hsum]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem sumMap_le (γ : MbMod Z₁ →ₗ[O] MbMod Z₂)
    (γs : MbMod (cjT O cj hO Z₁) →ₗ[O] MbMod (cjT O cj hO Z₂))
    (hb : γ (bCls Z₁) = bCls Z₂) (he : γ (eCl Z₁) = eCl Z₂)
    (hbs : γs (bCls (cjT O cj hO Z₁)) = bCls (cjT O cj hO Z₂))
    (hes : γs (eCl (cjT O cj hO Z₁)) = eCl (cjT O cj hO Z₂)) :
    relC O cj (Z₁.map O.subtype) t t' ≤
      (relC O cj (Z₂.map O.subtype) t t').comap (sumMap O (liftOf O γ) (liftOf O γs)) := by
  intro Y hY
  rw [Submodule.mem_comap, sumMap_apply]
  obtain ⟨c₁, c₂, h1, h2⟩ := (mem_relC_iff O cj hO Z₁ t t' Y).1 hY
  refine mem_relC_of_mk O cj hO Z₂ t t' _ _ (c₂ (Fin.last r)) (c₁ (Fin.last r)) ?_ ?_
  · rw [liftOf_spec, h1, mk_gen, map_sub, map_smul, map_smul, hb, he]
  · rw [liftOf_spec, h2, mk_gen, map_sub, map_smul, map_smul, hbs, hes]

theorem sumMap_comp_sub (g gs g' gs' : (Fin (r + 1) → O) →ₗ[O] (Fin (r + 1) → O)) (Y : Ix r → O) :
    sumMap O g gs (sumMap O g' gs' Y) - Y =
      Sum.elim (g (g' fun j => Y (Sum.inl j)) - fun j => Y (Sum.inl j))
        (gs (gs' fun j => Y (Sum.inr j)) - fun j => Y (Sum.inr j)) := by
  funext i
  cases i <;> rfl

def thetaOf (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O) (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂)
    (γs : MbMod (cjT O cj hO Z₁) ≃ₗ[O] MbMod (cjT O cj hO Z₂))
    (hb : γ (bCls Z₁) = bCls Z₂) (he : γ (eCl Z₁) = eCl Z₂)
    (hbs : γs (bCls (cjT O cj hO Z₁)) = bCls (cjT O cj hO Z₂))
    (hes : γs (eCl (cjT O cj hO Z₁)) = eCl (cjT O cj hO Z₂)) :
    DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t' :=
  LinearEquiv.ofLinear
    ((relC O cj (Z₁.map O.subtype) t t').mapQ _ (sumMap O (liftOf O γ.toLinearMap) (liftOf O γs.toLinearMap))
      (sumMap_le O cj hO t t' γ.toLinearMap γs.toLinearMap hb he hbs hes))
    ((relC O cj (Z₂.map O.subtype) t t').mapQ _
      (sumMap O (liftOf O γ.symm.toLinearMap) (liftOf O γs.symm.toLinearMap))
      (sumMap_le O cj hO t t' γ.symm.toLinearMap γs.symm.toLinearMap
        (by rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq, hb])
        (by rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq, he])
        (by rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq, hbs])
        (by rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq, hes])))
    (by
      refine LinearMap.ext fun m => ?_
      obtain ⟨Y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      simp only [LinearMap.comp_apply, Submodule.mapQ_apply, LinearMap.id_apply]
      rw [Submodule.Quotient.eq, sumMap_comp_sub]
      apply mem_relC_of_K
      · rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, liftOf_spec, liftOf_spec,
          sub_eq_zero]
        exact γ.apply_symm_apply _
      · rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, liftOf_spec, liftOf_spec,
          sub_eq_zero]
        exact γs.apply_symm_apply _)
    (by
      refine LinearMap.ext fun m => ?_
      obtain ⟨Y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      simp only [LinearMap.comp_apply, Submodule.mapQ_apply, LinearMap.id_apply]
      rw [Submodule.Quotient.eq, sumMap_comp_sub]
      apply mem_relC_of_K
      · rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, liftOf_spec, liftOf_spec,
          sub_eq_zero]
        exact γ.symm_apply_apply _
      · rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, liftOf_spec, liftOf_spec,
          sub_eq_zero]
        exact γs.symm_apply_apply _)

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
