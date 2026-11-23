import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondCoeffSecondIdempotent

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)
variable {T T' : F} {TT : M.R} {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)}
variable (h₁ : GHyp M g T T' TT Zh₁ Z₁ Zσ₁) (h₂ : GHyp M g T T' TT Zh₂ Z₂ Zσ₂)

theorem linear_firstIsoComponent (θ : DG g Zh₁ T T' ≃ₗ[M.L.O] DG g Zh₂ T T') : OLin hs (th1 hs h₁ h₂ θ) := by
  intro c l l₂ hl
  have key : ∀ x, th1 hs h₁ h₂ θ x = (splitH hs h₂ (θ ((splitH hs h₁).symm (x, 0)))).1 := fun x => rfl
  set v := (splitH hs h₁).symm (mk1 hs Z₁ TT l, 0) with hv
  have hv1 : splitH hs h₁ v = ((l : DD1 hs Z₁ TT), ((0 : Fin (r + 1) → M.R) : DD1 hs Zσ₁ TT)) := by
    rw [hv, AddEquiv.apply_symm_apply]
    rfl
  have hav := splitH_smul hs h₁ (dgO g c) v l 0 hv1
  rw [firstCoeff_diagonal, secondCoeff_diagonal, smul_zero] at hav
  have hθv : splitH hs h₂ (θ v) = ((l₂ : DD1 hs Z₂ TT), ((0 : Fin (r + 1) → M.R) : DD1 hs Zσ₂ TT)) := by
    refine Prod.ext ?_ ?_
    · rw [← key]
      exact hl
    · rw [lin_split1 hs h₁ h₂ θ (mk1 hs Z₁ TT l)]
      rfl
  have h2 := splitH_smul hs h₂ (dgO g c) (θ v) l₂ 0 hθv
  rw [firstCoeff_diagonal, secondCoeff_diagonal, smul_zero] at h2
  have hs1 : (splitH hs h₁).symm (mk1 hs Z₁ TT (dgR hs c • l), 0) = dgO g c • v := by
    rw [AddEquiv.symm_apply_eq, hav]
    rfl
  rw [key, hs1, LinearEquiv.map_smul, h2]

theorem linear_secondIsoComponent (θ : DG g Zh₁ T T' ≃ₗ[M.L.O] DG g Zh₂ T T') : OLin hs (th2 hs h₁ h₂ θ) := by
  intro c l l₂ hl
  have key : ∀ y, th2 hs h₁ h₂ θ y = (splitH hs h₂ (θ ((splitH hs h₁).symm (0, y)))).2 := fun y => rfl
  set v := (splitH hs h₁).symm (0, mk1 hs Zσ₁ TT l) with hv
  have hv1 : splitH hs h₁ v = (((0 : Fin (r + 1) → M.R) : DD1 hs Z₁ TT), (l : DD1 hs Zσ₁ TT)) := by
    rw [hv, AddEquiv.apply_symm_apply]
    rfl
  have hav := splitH_smul hs h₁ (dgO g c) v 0 l hv1
  rw [firstCoeff_diagonal, secondCoeff_diagonal, smul_zero] at hav
  have hθv : splitH hs h₂ (θ v) = (((0 : Fin (r + 1) → M.R) : DD1 hs Z₂ TT), (l₂ : DD1 hs Zσ₂ TT)) := by
    refine Prod.ext ?_ ?_
    · rw [lin_split2 hs h₁ h₂ θ (mk1 hs Zσ₁ TT l)]
      rfl
    · rw [← key]
      exact hl
  have h2 := splitH_smul hs h₂ (dgO g c) (θ v) 0 l₂ hθv
  rw [firstCoeff_diagonal, secondCoeff_diagonal, smul_zero] at h2
  have hs1 : (splitH hs h₁).symm (0, mk1 hs Zσ₁ TT (dgR hs c • l)) = dgO g c • v := by
    rw [AddEquiv.symm_apply_eq, hav]
    rfl
  rw [key, hs1, LinearEquiv.map_smul, h2]

theorem thetaOf_smul (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
    (o₁ : OLin hs θ₁) (o₂ : OLin hs θ₂) (a : M.L.O) (v : DG g Zh₁ T T') :
    thetaOf hs h₁ h₂ θ₁ θ₂ (a • v) = a • thetaOf hs h₁ h₂ θ₁ θ₂ v := by
  obtain ⟨l, w, hlw⟩ := splitH_split hs h₁ v
  obtain ⟨l₂, hl₂⟩ := QuotientAddGroup.mk_surjective (θ₁ (l : DD1 hs Z₁ TT))
  obtain ⟨w₂, hw₂⟩ := QuotientAddGroup.mk_surjective (θ₂ (w : DD1 hs Zσ₁ TT))
  have e1 := o₁ (c1 g a) l l₂ hl₂.symm
  have e2 := o₂ (c2 g a) w w₂ hw₂.symm
  have hu : splitH hs h₂ (thetaOf hs h₁ h₂ θ₁ θ₂ v) = ((l₂ : DD1 hs Z₂ TT), (w₂ : DD1 hs Zσ₂ TT)) := by
    simp only [thetaOf, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, hlw]
    exact Prod.ext hl₂.symm hw₂.symm
  have hau := splitH_smul hs h₂ a _ l₂ w₂ hu
  apply (splitH hs h₂).injective
  rw [hau]
  simp only [thetaOf, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, splitH_smul hs h₁ a v l w hlw]
  exact Prod.ext e1 e2

def linOf (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
    (o₁ : OLin hs θ₁) (o₂ : OLin hs θ₂) : DG g Zh₁ T T' ≃ₗ[M.L.O] DG g Zh₂ T T' where
  toFun := thetaOf hs h₁ h₂ θ₁ θ₂
  invFun := (thetaOf hs h₁ h₂ θ₁ θ₂).symm
  map_add' := map_add _
  map_smul' a v := thetaOf_smul hs h₁ h₂ θ₁ θ₂ o₁ o₂ a v
  left_inv := (thetaOf hs h₁ h₂ θ₁ θ₂).symm_apply_apply
  right_inv := (thetaOf hs h₁ h₂ θ₁ θ₂).apply_symm_apply

theorem firstIsoComponent_linearOf (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
    (o₁ : OLin hs θ₁) (o₂ : OLin hs θ₂) : th1 hs h₁ h₂ (linOf hs h₁ h₂ θ₁ θ₂ o₁ o₂) = θ₁ := by
  ext x
  show (splitH hs h₂ (thetaOf hs h₁ h₂ θ₁ θ₂ ((splitH hs h₁).symm (x, 0)))).1 = θ₁ x
  simp only [thetaOf, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rfl

theorem secondIsoComponent_linearOf (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
    (o₁ : OLin hs θ₁) (o₂ : OLin hs θ₂) : th2 hs h₁ h₂ (linOf hs h₁ h₂ θ₁ θ₂ o₁ o₂) = θ₂ := by
  ext x
  show (splitH hs h₂ (thetaOf hs h₁ h₂ θ₁ θ₂ ((splitH hs h₁).symm (0, x)))).2 = θ₂ x
  simp only [thetaOf, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rfl

theorem stepSplit_of (hG : GamSplitP) (hF : FormSplitP) : StepSplit := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ hK
  have cond : ∀ (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
      (o₁ : OLin hs θ₁) (o₂ : OLin hs θ₂),
      linOf hs h₁ h₂ θ₁ θ₂ o₁ o₂ ∈ ThetaGC M.L.O (↑M.L.cj) ((algebraMap F E) ↑g.q)
          ((algebraMap F E) (↑g.q)⁻¹) Zh₁ Zh₂ ((algebraMap F E) T) ((algebraMap F E) T') ↔
        Match1 hs θ₁ (ZZm g Zh₁ T T') (ZZm g Zh₂ T T') ∧
          Match1 hs θ₂ (ZZm g (Zh₁.map ⇑M.L.cj) T T') (ZZm g (Zh₂.map ⇑M.L.cj) T T') ∧
            IsoB hs Zh₁ Zh₂ T T' θ₁ θ₂ := by
    intro θ₁ θ₂ o₁ o₂
    have e := and_congr (hF F E M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ θ₁ θ₂)
      (hG F E M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ hK θ₁ θ₂ o₁ o₂)
    exact e.trans ⟨fun ⟨a, b, c⟩ => ⟨b, c, a⟩, fun ⟨b, c, a⟩ => ⟨a, b, c⟩⟩
  have back : ∀ θ : DG g Zh₁ T T' ≃ₗ[M.L.O] DG g Zh₂ T T',
      linOf hs h₁ h₂ (th1 hs h₁ h₂ θ) (th2 hs h₁ h₂ θ) (linear_firstIsoComponent hs h₁ h₂ θ) (linear_secondIsoComponent hs h₁ h₂ θ) = θ :=
    fun θ => LinearEquiv.ext fun v => (theta_eq hs h₁ h₂ θ v).symm
  refine Nat.card_congr
    { toFun := fun θ => ⟨(th1 hs h₁ h₂ θ.1, th2 hs h₁ h₂ θ.1), linear_firstIsoComponent hs h₁ h₂ θ.1,
        linear_secondIsoComponent hs h₁ h₂ θ.1, (cond _ _ (linear_firstIsoComponent hs h₁ h₂ θ.1) (linear_secondIsoComponent hs h₁ h₂ θ.1)).1
          ((back θ.1).symm ▸ θ.2)⟩
      invFun := fun p => ⟨linOf hs h₁ h₂ p.1.1 p.1.2 p.2.1 p.2.2.1,
        (cond _ _ p.2.1 p.2.2.1).2 p.2.2.2⟩
      left_inv := fun θ => Subtype.ext (back θ.1)
      right_inv := fun p => Subtype.ext (Prod.ext (firstIsoComponent_linearOf hs h₁ h₂ p.1.1 p.1.2 p.2.1 p.2.2.1)
        (secondIsoComponent_linearOf hs h₁ h₂ p.1.1 p.1.2 p.2.1 p.2.2.1)) }

end Formalism.L2.SG.LocalCountModules.AlgGSplit
