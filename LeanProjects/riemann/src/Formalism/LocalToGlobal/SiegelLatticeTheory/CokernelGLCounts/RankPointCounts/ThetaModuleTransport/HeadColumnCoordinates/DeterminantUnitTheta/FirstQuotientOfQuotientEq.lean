import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.LaGLinApply

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

section Basic

variable (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R)

theorem quotientMk_eq_iff_sub_mem_LL (x y : Fin (r + 1) → M.R) : mk1 hs Z TT x = mk1 hs Z TT y ↔ x - y ∈ LL hs Z TT := by
  exact QuotientAddGroup.eq_iff_sub_mem

theorem firstQuotient_of_quotient_eq {x y : Fin (r + 1) → M.R}
    (h : (Submodule.Quotient.mk x : MbMod Z.Z) = Submodule.Quotient.mk y) : mk1 hs Z TT x = mk1 hs Z TT y := by
  rw [quotientMk_eq_iff_sub_mem_LL]
  rw [Submodule.Quotient.eq] at h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun M.R).mp h
  rw [LL, AddMonoidHom.mem_range]
  refine ⟨Fin.snoc (α := fun _ => M.R) c 0, ?_⟩
  simp only [llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.snoc_last, map_zero, mul_zero, zero_smul, sub_zero]
  rw [← hc]
  funext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, mul_comm]

theorem mk_llMap (w : Fin (r + 1) → M.R) :
    (Submodule.Quotient.mk (llMap hs Z TT w) : MbMod Z.Z) =
      w (Fin.last r) • bCls Z.Z - (TT * dgR hs (trO hs (w (Fin.last r)))) • eCl Z.Z := by
  simp only [llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
  congr 1
  unfold bCls
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  have hsum : Z.Z.mulVec w - w (Fin.last r) • (fun i => Z.Z i (Fin.last r)) =
      ∑ a : Fin r, w a.castSucc • (fun i => Z.Z i a.castSucc) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Fin.sum_univ_castSucc]
    simp only [mul_comm]
    ring
  rw [hsum]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end Basic

theorem mk_eq_of (hs : M.split = some g) (T T' : F) (TT : M.R) (hTT : g.e (TT : E) = (T, T'))
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z : M.Mat (r + 1))
    (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (hu : IsUnit Zh.det)
    (hG : IsUnit (Zh.det * M.L.cj Zh.det - algebraMap F E (T * T') *
      ((Zh.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det)))
    {x y : Fin (r + 1) → M.R} (h1 : mk1 hs Z TT x = mk1 hs Z TT y)
    (h2 : laG (ZZm g Zh T T') x = laG (ZZm g Zh T T') y) :
    (Submodule.Quotient.mk x : MbMod Z.Z) = Submodule.Quotient.mk y := by
  rw [Submodule.Quotient.eq]
  apply ker_fact hs T T' TT hTT Zh Z hZ hu hG
  · have e : mk1 hs Z TT (x - y) = mk1 hs Z TT x - mk1 hs Z TT y :=
      map_sub (QuotientAddGroup.mk' (LL hs Z TT)) x y
    rw [e, h1, sub_self]
  · have e2 : laG (ZZm g Zh T T') (x - y) = laG (ZZm g Zh T T') x - laG (ZZm g Zh T T') y := by
      unfold laG
      have hfun : (fun i => ((x - y) i : E)) = (fun i => (x i : E)) - (fun i => (y i : E)) := by
        funext i
        simp
      rw [hfun, Matrix.mulVec_sub, Pi.sub_apply]
    rw [e2, h2, sub_self]

section ThetaOf

variable (hs : M.split = some g) {Z₁ Z₂ : M.Mat (r + 1)} (TT : M.R)

def liftG (γ : MbMod Z₁.Z →ₗ[M.R] MbMod Z₂.Z) (v : Fin (r + 1) → M.R) : Fin (r + 1) → M.R :=
  Classical.choose (Submodule.Quotient.mk_surjective _ (γ (Submodule.Quotient.mk v)))

theorem liftG_spec (γ : MbMod Z₁.Z →ₗ[M.R] MbMod Z₂.Z) (v : Fin (r + 1) → M.R) :
    (Submodule.Quotient.mk (liftG γ v) : MbMod Z₂.Z) = γ (Submodule.Quotient.mk v) := Classical.choose_spec (Submodule.Quotient.mk_surjective _ (γ (Submodule.Quotient.mk v)))

def thF (γ : MbMod Z₁.Z →ₗ[M.R] MbMod Z₂.Z) : (Fin (r + 1) → M.R) →+ DD1 hs Z₂ TT where
  toFun v := mk1 hs Z₂ TT (liftG γ v)
  map_zero' := by
    rw [show (0 : DD1 hs Z₂ TT) = mk1 hs Z₂ TT 0 from rfl]
    apply firstQuotient_of_quotient_eq
    rw [liftG_spec, Submodule.Quotient.mk_zero, map_zero, Submodule.Quotient.mk_zero]
  map_add' v w := by
    rw [show mk1 hs Z₂ TT (liftG γ v) + mk1 hs Z₂ TT (liftG γ w) = mk1 hs Z₂ TT (liftG γ v + liftG γ w)
      from rfl]
    apply firstQuotient_of_quotient_eq
    rw [liftG_spec, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, liftG_spec, liftG_spec, map_add]

theorem thF_ker (γ : MbMod Z₁.Z →ₗ[M.R] MbMod Z₂.Z) (hb : γ (bCls Z₁.Z) = bCls Z₂.Z)
    (he : γ (eCl Z₁.Z) = eCl Z₂.Z) : LL hs Z₁ TT ≤ (thF hs TT γ).ker := by
  intro l hl
  obtain ⟨m, rfl⟩ := hl
  rw [AddMonoidHom.mem_ker]
  show mk1 hs Z₂ TT (liftG γ (llMap hs Z₁ TT m)) = 0
  rw [firstQuotient_of_quotient_eq hs Z₂ TT (y := llMap hs Z₂ TT m) ?_, (firstQuotient_eq_zero_iff hs Z₂ TT _).mpr ⟨m, rfl⟩]
  rw [liftG_spec, mk_llMap, mk_llMap, map_sub, map_smul, map_smul, hb, he]

def thOf (γ : MbMod Z₁.Z →ₗ[M.R] MbMod Z₂.Z) (hb : γ (bCls Z₁.Z) = bCls Z₂.Z)
    (he : γ (eCl Z₁.Z) = eCl Z₂.Z) : DD1 hs Z₁ TT →+ DD1 hs Z₂ TT :=
  QuotientAddGroup.lift (LL hs Z₁ TT) (thF hs TT γ) (thF_ker hs TT γ hb he)

theorem thOf_spec (γ : MbMod Z₁.Z →ₗ[M.R] MbMod Z₂.Z) (hb : γ (bCls Z₁.Z) = bCls Z₂.Z)
    (he : γ (eCl Z₁.Z) = eCl Z₂.Z) {v w : Fin (r + 1) → M.R}
    (h : γ (Submodule.Quotient.mk v) = Submodule.Quotient.mk w) :
    thOf hs TT γ hb he (mk1 hs Z₁ TT v) = mk1 hs Z₂ TT w := by
  show thF hs TT γ v = mk1 hs Z₂ TT w
  apply firstQuotient_of_quotient_eq
  rw [liftG_spec, h]

def thEquiv (γ : IsoMbe Z₁.Z Z₂.Z) : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT :=
  have hb' : γ.1.symm (bCls Z₂.Z) = bCls Z₁.Z := (LinearEquiv.symm_apply_eq _).2 γ.2.1.symm
  have he' : γ.1.symm (eCl Z₂.Z) = eCl Z₁.Z := (LinearEquiv.symm_apply_eq _).2 γ.2.2.symm
  { toFun := thOf hs TT γ.1.toLinearMap γ.2.1 γ.2.2
    invFun := thOf hs TT γ.1.symm.toLinearMap hb' he'
    left_inv := fun x => by
      induction x using QuotientAddGroup.induction_on with
      | H v =>
        obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (γ.1 (Submodule.Quotient.mk v))
        show thOf hs TT γ.1.symm.toLinearMap hb' he' (thOf hs TT γ.1.toLinearMap γ.2.1 γ.2.2 (mk1 hs Z₁ TT v)) =
          mk1 hs Z₁ TT v
        rw [thOf_spec hs TT _ _ _ hw.symm, thOf_spec hs TT _ _ _]
        show γ.1.symm _ = _
        rw [hw, LinearEquiv.symm_apply_apply]
    right_inv := fun x => by
      induction x using QuotientAddGroup.induction_on with
      | H v =>
        obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (γ.1.symm (Submodule.Quotient.mk v))
        show thOf hs TT γ.1.toLinearMap γ.2.1 γ.2.2 (thOf hs TT γ.1.symm.toLinearMap hb' he' (mk1 hs Z₂ TT v)) =
          mk1 hs Z₂ TT v
        rw [thOf_spec hs TT _ _ _ hw.symm, thOf_spec hs TT _ _ _]
        show γ.1 _ = _
        rw [hw, LinearEquiv.apply_symm_apply]
    map_add' := map_add _ }

theorem thEquiv_spec (γ : IsoMbe Z₁.Z Z₂.Z) {v w : Fin (r + 1) → M.R}
    (h : γ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk w) :
    thEquiv hs TT γ (mk1 hs Z₁ TT v) = mk1 hs Z₂ TT w := thOf_spec hs TT γ.1.toLinearMap γ.2.1 γ.2.2 h

end ThetaOf

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
