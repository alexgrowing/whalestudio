import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.FormSplitP

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

section Block

variable {A B C D : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
variable (Θ : A × B ≃+ C × D)

def blk1 (h1 : ∀ x, (Θ (x, 0)).2 = 0) (h1' : ∀ z, (Θ.symm (z, 0)).2 = 0) : A ≃+ C where
  toFun x := (Θ (x, 0)).1
  invFun z := (Θ.symm (z, 0)).1
  left_inv x := by
    have e1 : Θ (x, 0) = ((Θ (x, 0)).1, 0) := Prod.ext rfl (h1 x)
    have := Θ.symm_apply_apply (x, 0)
    rw [e1] at this
    simp only [this]
  right_inv z := by
    have e1 : Θ.symm (z, 0) = ((Θ.symm (z, 0)).1, 0) := Prod.ext rfl (h1' z)
    have := Θ.apply_symm_apply (z, 0)
    rw [e1] at this
    simp only [this]
  map_add' x y := by
    rw [show ((x + y, 0) : A × B) = (x, 0) + (y, 0) by simp, map_add]
    rfl

def blk2 (h2 : ∀ y, (Θ (0, y)).1 = 0) (h2' : ∀ z, (Θ.symm (0, z)).1 = 0) : B ≃+ D where
  toFun y := (Θ (0, y)).2
  invFun z := (Θ.symm (0, z)).2
  left_inv y := by
    have e1 : Θ (0, y) = (0, (Θ (0, y)).2) := Prod.ext (h2 y) rfl
    have := Θ.symm_apply_apply (0, y)
    rw [e1] at this
    simp only [this]
  right_inv z := by
    have e1 : Θ.symm (0, z) = (0, (Θ.symm (0, z)).2) := Prod.ext (h2' z) rfl
    have := Θ.apply_symm_apply (0, z)
    rw [e1] at this
    simp only [this]
  map_add' x y := by
    rw [show ((0, x + y) : A × B) = (0, x) + (0, y) by simp, map_add]
    rfl

theorem blk_eq (h1 : ∀ x, (Θ (x, 0)).2 = 0) (h1' : ∀ z, (Θ.symm (z, 0)).2 = 0)
    (h2 : ∀ y, (Θ (0, y)).1 = 0) (h2' : ∀ z, (Θ.symm (0, z)).1 = 0) (p : A × B) :
    Θ p = (blk1 Θ h1 h1' p.1, blk2 Θ h2 h2' p.2) := by
  have e : p = (p.1, 0) + (0, p.2) := by simp
  conv_lhs => rw [e]
  rw [map_add]
  ext
  · simp [blk1, h2]
  · simp [blk2, h1]

end Block

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def eps1 (g : SplitG M.L) : M.L.O := ⟨g.e.symm (1, 0), mem_O_of_comp g _ (by simp) (by simp)⟩

def eps2 (g : SplitG M.L) : M.L.O := ⟨g.e.symm (0, 1), mem_O_of_comp g _ (by simp) (by simp)⟩

def dgO (g : SplitG M.L) (c : 𝒪[F]) : M.L.O :=
  ⟨algebraMap F E c, mem_O_of_comp g _ (by rw [Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.e_alg]; exact c.2)
    (by rw [Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.e_alg]; exact c.2)⟩

theorem firstCoeff_firstIdempotent : c1 g (eps1 g) = 1 := Subtype.ext (by simp [c1, eps1])
theorem secondCoeff_firstIdempotent : c2 g (eps1 g) = 0 := Subtype.ext (by simp [c2, eps1])
theorem firstCoeff_secondIdempotent : c1 g (eps2 g) = 0 := Subtype.ext (by simp [c1, eps2])
theorem secondCoeff_secondIdempotent : c2 g (eps2 g) = 1 := Subtype.ext (by simp [c2, eps2])
theorem firstCoeff_diagonal (c : 𝒪[F]) : c1 g (dgO g c) = c := Subtype.ext (by simp [c1, dgO, Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.e_alg])
theorem secondCoeff_diagonal (c : 𝒪[F]) : c2 g (dgO g c) = c := Subtype.ext (by simp [c2, dgO, Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.e_alg])

variable (hs : M.split = some g)
variable {T T' : F} {TT : M.R} {Zh Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Z Zσ Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)}

theorem splitH_symm_mk (h : GHyp M g T T' TT Zh Z Zσ) (l w : Fin (r + 1) → M.R) :
    (splitH hs h).symm ((QuotientAddGroup.mk l : DD1 hs Z TT), (QuotientAddGroup.mk w : DD1 hs Zσ TT)) =
      (Submodule.Quotient.mk (iota1 hs l + iota2 hs w) : DG g Zh T T') := rfl

theorem splitH_mk (h : GHyp M g T T' TT Zh Z Zσ) (Y : Ix r → M.L.O) :
    splitH hs h (Submodule.Quotient.mk Y : DG g Zh T T') =
      ((QuotientAddGroup.mk (cmp1 hs Y) : DD1 hs Z TT), (QuotientAddGroup.mk (cmp2 hs Y) : DD1 hs Zσ TT)) := rfl

theorem splitH_smul (h : GHyp M g T T' TT Zh Z Zσ) (a : M.L.O) (v : DG g Zh T T') (l w : Fin (r + 1) → M.R)
    (hv : splitH hs h v = ((QuotientAddGroup.mk l : DD1 hs Z TT), (QuotientAddGroup.mk w : DD1 hs Zσ TT))) :
    splitH hs h (a • v) = ((QuotientAddGroup.mk (dgR hs (c1 g a) • l) : DD1 hs Z TT),
      (QuotientAddGroup.mk (dgR hs (c2 g a) • w) : DD1 hs Zσ TT)) := by
  have hv' : v = (splitH hs h).symm ((QuotientAddGroup.mk l : DD1 hs Z TT),
      (QuotientAddGroup.mk w : DD1 hs Zσ TT)) := by rw [← hv, AddEquiv.symm_apply_apply]
  rw [hv', splitH_symm_mk, ← Submodule.Quotient.mk_smul, splitH_mk, firstComponent_smul, secondComponent_smul, map_add, map_add,
    firstComponent_iotaOne, firstComponent_iotaTwo, secondComponent_iotaOne, secondComponent_iotaTwo, add_zero, zero_add]

theorem splitH_split (h : GHyp M g T T' TT Zh Z Zσ) (v : DG g Zh T T') :
    ∃ l w : Fin (r + 1) → M.R,
      splitH hs h v = ((QuotientAddGroup.mk l : DD1 hs Z TT), (QuotientAddGroup.mk w : DD1 hs Zσ TT)) := by
  obtain ⟨l, hl⟩ := QuotientAddGroup.mk_surjective (splitH hs h v).1
  obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (splitH hs h v).2
  exact ⟨l, w, Prod.ext hl.symm hw.symm⟩

theorem firstIdempotent_split (h : GHyp M g T T' TT Zh Z Zσ) (v : DG g Zh T T') :
    splitH hs h (eps1 g • v) = ((splitH hs h v).1, 0) := by
  obtain ⟨Y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [← Submodule.Quotient.mk_smul, splitH_mk, splitH_mk, firstComponent_smul, secondComponent_smul, firstCoeff_firstIdempotent, secondCoeff_firstIdempotent, map_one,
    map_zero, one_smul, zero_smul]
  rfl

theorem secondIdempotent_split (h : GHyp M g T T' TT Zh Z Zσ) (v : DG g Zh T T') :
    splitH hs h (eps2 g • v) = (0, (splitH hs h v).2) := by
  obtain ⟨Y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [← Submodule.Quotient.mk_smul, splitH_mk, splitH_mk, firstComponent_smul, secondComponent_smul, firstCoeff_secondIdempotent, secondCoeff_secondIdempotent, map_one,
    map_zero, one_smul, zero_smul]
  rfl

variable (h₁ : GHyp M g T T' TT Zh₁ Z₁ Zσ₁) (h₂ : GHyp M g T T' TT Zh₂ Z₂ Zσ₂)

def bigT (θ : DG g Zh₁ T T' ≃ₗ[M.L.O] DG g Zh₂ T T') :
    DD1 hs Z₁ TT × DD1 hs Zσ₁ TT ≃+ DD1 hs Z₂ TT × DD1 hs Zσ₂ TT :=
  (splitH hs h₁).symm.trans (θ.toAddEquiv.trans (splitH hs h₂))

theorem lin_split1 {Zh Zh' : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {Z Zσ Z' Zσ' : M.Mat (r + 1)}
    (h : GHyp M g T T' TT Zh Z Zσ) (h' : GHyp M g T T' TT Zh' Z' Zσ')
    (θ : DG g Zh T T' ≃ₗ[M.L.O] DG g Zh' T T') (x : DD1 hs Z TT) :
    (splitH hs h' (θ ((splitH hs h).symm (x, 0)))).2 = 0 := by
  set u := (splitH hs h).symm (x, 0) with hu_def
  have hu : eps1 g • u = u := by
    apply (splitH hs h).injective
    rw [firstIdempotent_split, hu_def, AddEquiv.apply_symm_apply]
  have hθ : θ u = eps1 g • θ u := by rw [← map_smul, hu]
  rw [hθ, firstIdempotent_split]

theorem lin_split2 {Zh Zh' : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {Z Zσ Z' Zσ' : M.Mat (r + 1)}
    (h : GHyp M g T T' TT Zh Z Zσ) (h' : GHyp M g T T' TT Zh' Z' Zσ')
    (θ : DG g Zh T T' ≃ₗ[M.L.O] DG g Zh' T T') (y : DD1 hs Zσ TT) :
    (splitH hs h' (θ ((splitH hs h).symm (0, y)))).1 = 0 := by
  set u := (splitH hs h).symm (0, y) with hu_def
  have hu : eps2 g • u = u := by
    apply (splitH hs h).injective
    rw [secondIdempotent_split, hu_def, AddEquiv.apply_symm_apply]
  have hθ : θ u = eps2 g • θ u := by rw [← map_smul, hu]
  rw [hθ, secondIdempotent_split]

def th1 (θ : DG g Zh₁ T T' ≃ₗ[M.L.O] DG g Zh₂ T T') : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT :=
  blk1 (bigT hs h₁ h₂ θ) (fun x => lin_split1 hs h₁ h₂ θ x) (fun z => lin_split1 hs h₂ h₁ θ.symm z)

def th2 (θ : DG g Zh₁ T T' ≃ₗ[M.L.O] DG g Zh₂ T T') : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT :=
  blk2 (bigT hs h₁ h₂ θ) (fun y => lin_split2 hs h₁ h₂ θ y) (fun z => lin_split2 hs h₂ h₁ θ.symm z)

theorem bigT_eq (θ : DG g Zh₁ T T' ≃ₗ[M.L.O] DG g Zh₂ T T') (p : DD1 hs Z₁ TT × DD1 hs Zσ₁ TT) :
    bigT hs h₁ h₂ θ p = (th1 hs h₁ h₂ θ p.1, th2 hs h₁ h₂ θ p.2) := blk_eq _ _ _ _ _ p

theorem theta_eq (θ : DG g Zh₁ T T' ≃ₗ[M.L.O] DG g Zh₂ T T') (v : DG g Zh₁ T T') :
    θ v = thetaOf hs h₁ h₂ (th1 hs h₁ h₂ θ) (th2 hs h₁ h₂ θ) v := by
  have e : θ v = (splitH hs h₂).symm (bigT hs h₁ h₂ θ (splitH hs h₁ v)) := by simp [bigT]
  rw [e, bigT_eq]
  rfl

end Formalism.L2.SG.LocalCountModules.AlgGSplit
