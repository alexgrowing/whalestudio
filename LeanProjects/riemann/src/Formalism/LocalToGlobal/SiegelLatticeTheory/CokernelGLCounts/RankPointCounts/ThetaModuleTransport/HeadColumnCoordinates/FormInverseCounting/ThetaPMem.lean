import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.FormPair

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}
theorem elim_sub (a b c d : Fin (r + 1) → O) :
    (Sum.elim a b : Ix r → O) - Sum.elim c d = Sum.elim (a - c) (b - d) := by
  funext i; cases i <;> rfl

variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
variable {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
include hcj

def thetaP (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0) (p : PairSet O cj hO Z₁ Z₂) :
    DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t' :=
  thetaOf O cj hO t t' p.1.1 p.1.2 p.2.1.1 p.2.1.2 (pair_b O cj hcj hO hu₁ hu₂ p)
    (pair_e O cj hcj hO hu₁ hu₂ hκ₁ hκ₂ p)

private theorem thetaP_mk_eq_mk_sum_elim_liftOf (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0) (p : PairSet O cj hO Z₁ Z₂)
    (Y : Ix r → O) :
    thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk Y) =
      Submodule.Quotient.mk (Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
        (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j))) := rfl

private theorem mk_sum_elim_eq_of_sub_mem_headCols (a a' b b' : Fin (r + 1) → O) (ha : a - a' ∈ headCols Z₂)
    (hb : b - b' ∈ headCols (cjT O cj hO Z₂)) :
    (Submodule.Quotient.mk (Sum.elim a b) : DDc O cj (Z₂.map O.subtype) t t') =
      Submodule.Quotient.mk (Sum.elim a' b') := by
  apply (Submodule.Quotient.eq _).mpr
  rw [elim_sub]
  exact mem_relC_of_K O cj hO Z₂ t t' _ _ ha hb

private theorem lamC_eq_of_pairSet_mk_eq (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (p : PairSet O cj hO Z₁ Z₂) (y y₂ : Fin (r + 1) → O)
    (h : p.1.1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk y₂) :
    lamC (Z₂.map O.subtype) (fun j => ((y₂ j : O) : E)) = lamC (Z₁.map O.subtype) (fun j => ((y j : O) : E)) := by
  have key := lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 y y₂ h
  simpa [lamL_apply] using key

theorem thetaP_mem (ht : cj (t : E) = t) (ht' : cj (t' : E) = t')
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
    (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det)
    (p : PairSet O cj hO Z₁ Z₂) :
    thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p ∈ ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t' := by
  have hl : ∀ y : Fin (r + 1) → O,
      p.1.1 (Submodule.Quotient.mk (liftOf O p.1.1.symm.toLinearMap y)) = Submodule.Quotient.mk y := by
    intro y
    rw [liftOf_spec]
    exact p.1.1.apply_symm_apply _
  have hr : ∀ y : Fin (r + 1) → O,
      p.1.2 (Submodule.Quotient.mk (liftOf O p.1.2.symm.toLinearMap y)) = Submodule.Quotient.mk y := by
    intro y
    rw [liftOf_spec]
    exact p.1.2.apply_symm_apply _
  have he2 := pair_e O cj hcj hO hu₁ hu₂ hκ₁ hκ₂ p
  refine ⟨?_, ?_, ?_⟩
  · intro Y W Y₂ W₂ hY hW
    rw [thetaP_mk_eq_mk_sum_elim_liftOf] at hY hW
    have hY' := (Submodule.Quotient.eq _).mp hY.symm
    have hW' := (Submodule.Quotient.eq _).mp hW.symm
    have e1 : formC O cj (Z₂.map O.subtype) t t' Y₂ W₂ - formC O cj (Z₁.map O.subtype) t t' Y W =
        formC O cj (Z₂.map O.subtype) t t' (Y₂ - Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
            (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j))) W₂ +
          formC O cj (Z₂.map O.subtype) t t' (Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
            (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j)))
            (W₂ - Sum.elim (liftOf O p.1.1.toLinearMap fun j => W (Sum.inl j))
              (liftOf O p.1.2.toLinearMap fun j => W (Sum.inr j))) +
          (formC O cj (Z₂.map O.subtype) t t'
            (Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
              (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j)))
            (Sum.elim (liftOf O p.1.1.toLinearMap fun j => W (Sum.inl j))
              (liftOf O p.1.2.toLinearMap fun j => W (Sum.inr j))) -
            formC O cj (Z₁.map O.subtype) t t' Y W) := by
      rw [formC_sub_left, formC_sub_right]
      ring
    rw [e1]
    exact O.add_mem (O.add_mem (formC_rel_left O cj _ _ _ hG₂ hO _ _ hY')
      (formC_rel_right O cj hcj _ _ _ ht ht' hG₂ hO _ _ hW'))
      (form_pair O cj hcj hO t t' ht ht' hu₁ hu₂ hκ₁ hκ₂ hG₁ hG₂ p Y W)
  · apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨Y, hY0, rfl⟩, rfl⟩
      simp only [GamC, Set.mem_setOf_eq]
      refine ⟨Sum.elim (Y (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1)
        (liftOf O p.1.2.toLinearMap fun j => Y (Sum.inr j)), fun a => ?_, ?_⟩
      · simp [Pi.single_apply, Fin.castSucc_ne_last]
      · refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk Y) = _
          rw [thetaP_mk_eq_mk_sum_elim_liftOf, supp_inl O Y hY0]
          exact mk_sum_elim_eq_of_sub_mem_headCols O cj hcj hO t t' _ _ _ _ (lift_e_mem O (f := p.1.1.toLinearMap) p.2.1.2 _)
            (by rw [sub_self]; exact zero_mem _)
        · simp
        · exact (p.2.2.1 _ _ (liftOf_spec O _ _).symm).symm
    · rintro _ ⟨Y₂, hY0, rfl⟩
      refine ⟨(Submodule.Quotient.mk (Sum.elim (Y₂ (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1)
          (liftOf O p.1.2.symm.toLinearMap fun j => Y₂ (Sum.inr j))),
          (((Sum.elim (Y₂ (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1)
            (liftOf O p.1.2.symm.toLinearMap fun j => Y₂ (Sum.inr j)) : Ix r → O) (Sum.inl (Fin.last r)) : O) : E),
          lamStarC cj (Z₁.map O.subtype) fun b => (((Sum.elim (Y₂ (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1)
            (liftOf O p.1.2.symm.toLinearMap fun j => Y₂ (Sum.inr j)) : Ix r → O) (Sum.inr b) : O) : E)), ?_, ?_⟩
      · simp only [GamC, Set.mem_setOf_eq]
        refine ⟨_, fun a => ?_, rfl⟩
        simp [Pi.single_apply, Fin.castSucc_ne_last]
      · have hY₂ : Y₂ = Sum.elim (Y₂ (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1) (fun j => Y₂ (Sum.inr j)) := by
          rw [← supp_inl O Y₂ hY0]
          exact elim_eta O Y₂
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk _) = Submodule.Quotient.mk Y₂
          rw [thetaP_mk_eq_mk_sum_elim_liftOf]
          conv_rhs => rw [hY₂]
          exact mk_sum_elim_eq_of_sub_mem_headCols O cj hcj hO t t' _ _ _ _ (lift_e_mem O (f := p.1.1.toLinearMap) p.2.1.2 _)
            (lift_rep_mem O p.1.2 _ _ (liftOf_spec O _ _))
        · simp
        · exact (p.2.2.1 _ _ (hr _)).symm
  · apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨Y, hY0, rfl⟩, rfl⟩
      simp only [GamC', Set.mem_setOf_eq]
      refine ⟨Sum.elim (liftOf O p.1.1.toLinearMap fun j => Y (Sum.inl j))
        (Y (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1), fun a => ?_, ?_⟩
      · simp [Pi.single_apply, Fin.castSucc_ne_last]
      · refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk Y) = _
          rw [thetaP_mk_eq_mk_sum_elim_liftOf, supp_inr O Y hY0]
          exact mk_sum_elim_eq_of_sub_mem_headCols O cj hcj hO t t' _ _ _ _ (by rw [sub_self]; exact zero_mem _)
            (lift_e_mem O (f := p.1.2.toLinearMap) he2 _)
        · exact (lamC_eq_of_pairSet_mk_eq O cj hcj hO hu₁ hu₂ p _ _ (liftOf_spec O _ _).symm).symm
        · simp
    · rintro _ ⟨Y₂, hY0, rfl⟩
      refine ⟨(Submodule.Quotient.mk (Sum.elim (liftOf O p.1.1.symm.toLinearMap fun j => Y₂ (Sum.inl j))
          (Y₂ (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1)),
          lamC (Z₁.map O.subtype) fun a => (((Sum.elim (liftOf O p.1.1.symm.toLinearMap fun j => Y₂ (Sum.inl j))
            (Y₂ (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1) : Ix r → O) (Sum.inl a) : O) : E),
          (((Sum.elim (liftOf O p.1.1.symm.toLinearMap fun j => Y₂ (Sum.inl j))
            (Y₂ (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1) : Ix r → O) (Sum.inr (Fin.last r)) : O) : E)),
          ?_, ?_⟩
      · simp only [GamC', Set.mem_setOf_eq]
        refine ⟨_, fun a => ?_, rfl⟩
        simp [Pi.single_apply, Fin.castSucc_ne_last]
      · have hY₂ : Y₂ = Sum.elim (fun j => Y₂ (Sum.inl j)) (Y₂ (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1) := by
          rw [← supp_inr O Y₂ hY0]
          exact elim_eta O Y₂
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · show thetaP O cj hcj hO t t' hu₁ hu₂ hκ₁ hκ₂ p (Submodule.Quotient.mk _) = Submodule.Quotient.mk Y₂
          rw [thetaP_mk_eq_mk_sum_elim_liftOf]
          conv_rhs => rw [hY₂]
          exact mk_sum_elim_eq_of_sub_mem_headCols O cj hcj hO t t' _ _ _ _ (lift_rep_mem O p.1.1 _ _ (liftOf_spec O _ _))
            (lift_e_mem O (f := p.1.2.toLinearMap) he2 _)
        · exact (lamC_eq_of_pairSet_mk_eq O cj hcj hO hu₁ hu₂ p _ _ (hl _)).symm
        · simp

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
