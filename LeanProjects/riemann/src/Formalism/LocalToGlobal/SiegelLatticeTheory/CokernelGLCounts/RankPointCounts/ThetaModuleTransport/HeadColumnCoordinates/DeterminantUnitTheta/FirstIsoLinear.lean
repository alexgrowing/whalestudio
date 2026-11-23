import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.FirstQuotientOfQuotientEq

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem olin_symm (hs : M.split = some g) {Z₁ Z₂ : M.Mat (r + 1)} {TT : M.R}
    (θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (h : OLin hs θ) : OLin hs θ.symm := by
  intro c l l₂ hl
  have h1 : θ (mk1 hs Z₁ TT l₂) = mk1 hs Z₂ TT l := by rw [← hl, AddEquiv.apply_symm_apply]
  have h2 := h c l₂ l h1
  rw [← h2, AddEquiv.symm_apply_apply]

theorem match1_symm (hs : M.split = some g) {Z₁ Z₂ : M.Mat (r + 1)} {TT : M.R}
    (θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) {Zm₁ Zm₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (h : Match1 hs θ Zm₁ Zm₂) : Match1 hs θ.symm Zm₂ Zm₁ := by
  unfold Match1 at h ⊢
  rw [← h, Set.image_image]
  simp

theorem firstIso_linear (hs : M.split = some g) (T T' : F) (TT : M.R) (hTT : g.e (TT : E) = (T, T'))
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : M.Mat (r + 1))
    (hZ₁ : Z₁.Z.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T')
    (hZ₂ : Z₂.Z.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T') (hu₁ : IsUnit Zh₁.det) (hu₂ : IsUnit Zh₂.det)
    (hG₂ : IsUnit (Zh₂.det * M.L.cj Zh₂.det - algebraMap F E (T * T') *
      ((Zh₂.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₂.submatrix Fin.castSucc Fin.castSucc).det)))
    (θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (hO : OLin hs θ)
    (hM : Match1 hs θ (ZZm g Zh₁ T T') (ZZm g Zh₂ T T')) :
    ∃ γ₀ : MbMod Z₁.Z →ₗ[M.R] MbMod Z₂.Z, ∀ l x : Fin (r + 1) → M.R,
      γ₀ (Submodule.Quotient.mk l) = Submodule.Quotient.mk x →
        θ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT x ∧ laG (ZZm g Zh₂ T T') x = laG (ZZm g Zh₁ T T') l := by
  have hex : ∀ l : Fin (r + 1) → M.R, ∃ x : Fin (r + 1) → M.R,
      θ (mk1 hs Z₁ TT (q2 hs • l)) = mk1 hs Z₂ TT (q2 hs • x) ∧ θ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT x ∧
        laG (ZZm g Zh₂ T T') x = laG (ZZm g Zh₁ T T') l := by
    intro l
    have hp : (mk1 hs Z₁ TT ((0 : M.R) • eV r + q2 hs • l), mk1 hs Z₁ TT l, (0 : M.R), laG (ZZm g Zh₁ T T') l) ∈
        Gam1 hs Z₁ TT (ZZm g Zh₁ T T') := ⟨l, 0, rfl⟩
    have hq : (θ (mk1 hs Z₁ TT ((0 : M.R) • eV r + q2 hs • l)), θ (mk1 hs Z₁ TT l), (0 : M.R), laG (ZZm g Zh₁ T T') l) ∈
        Gam1 hs Z₂ TT (ZZm g Zh₂ T T') := by
      rw [← hM]; exact ⟨_, hp, rfl⟩
    obtain ⟨x, η, hx⟩ := hq
    simp only [Prod.mk.injEq] at hx
    obtain ⟨h1, h2, h3, h4⟩ := hx
    subst h3
    simp only [zero_smul, zero_add] at h1
    exact ⟨x, h1, h2, h4.symm⟩
  choose H hH using hex
  have hU : ∀ {l x y : Fin (r + 1) → M.R}, θ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT x →
      θ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT y → laG (ZZm g Zh₂ T T') x = laG (ZZm g Zh₂ T T') y →
      (Submodule.Quotient.mk x : MbMod Z₂.Z) = Submodule.Quotient.mk y := by
    intro l x y hx hy hL
    exact mk_eq_of hs T T' TT hTT Zh₂ Z₂ hZ₂ hu₂ hG₂ (hx.symm.trans hy) hL
  have hLlin : ∀ (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (s : M.R) (v w : Fin (r + 1) → M.R),
      laG (ZZm g Zh T T') (v + w) = laG (ZZm g Zh T T') v + laG (ZZm g Zh T T') w ∧
        laG (ZZm g Zh T T') (s • v) = (s : E) * laG (ZZm g Zh T T') v := by
    intro Zh s v w
    refine ⟨?_, ?_⟩
    · rw [← laGLin_apply, map_add]; rfl
    · rw [← laGLin_apply, map_smul, Subring.smul_def, smul_eq_mul]; rfl
  let γ₀ : (Fin (r + 1) → M.R) →ₗ[M.R] MbMod Z₂.Z :=
    { toFun := fun l => Submodule.Quotient.mk (H l)
      map_add' := fun l l' => by
        rw [← Submodule.Quotient.mk_add]
        refine hU (hH (l + l')).2.1 ?_ ?_
        · rw [show mk1 hs Z₁ TT (l + l') = mk1 hs Z₁ TT l + mk1 hs Z₁ TT l' from rfl, map_add, (hH l).2.1,
            (hH l').2.1]; rfl
        · rw [(hH (l + l')).2.2, (hLlin Zh₁ 1 l l').1, (hLlin Zh₂ 1 (H l) (H l')).1, (hH l).2.2, (hH l').2.2]
      map_smul' := fun s l => by
        obtain ⟨a, b, rfl⟩ := R_decomp hs s
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        refine hU (hH _).2.1 ?_ ?_
        · rw [add_smul, mul_smul, add_smul, mul_smul]
          rw [show mk1 hs Z₁ TT (dgR hs a • l + dgR hs b • q2 hs • l) =
            mk1 hs Z₁ TT (dgR hs a • l) + mk1 hs Z₁ TT (dgR hs b • q2 hs • l) from rfl, map_add,
            hO a l (H l) (hH l).2.1, hO b _ _ (hH l).1]; rfl
        · rw [(hH _).2.2, (hLlin Zh₁ (dgR hs a + dgR hs b * q2 hs) l l).2,
            (hLlin Zh₂ (dgR hs a + dgR hs b * q2 hs) (H l) l).2, (hH l).2.2] }
  have hker : headCols Z₁.Z ≤ LinearMap.ker γ₀ := by
    intro l hl
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk (H l) : MbMod Z₂.Z) = 0
    rw [← Submodule.Quotient.mk_zero]
    refine hU (hH l).2.1 ?_ ?_
    · rw [(firstQuotient_eq_zero_iff hs Z₁ TT l).2 (headCols_le_LL hs Z₁ TT hl), map_zero]; rfl
    · rw [(hH l).2.2, laG_headCols Zh₁ T T' Z₁ hZ₁ (unit_zzm hs Zh₁ T T' hu₁) hl]
      rw [← laGLin_apply (M := M) (ZZm g Zh₂ T T') 0, map_zero]
  refine ⟨(headCols Z₁.Z).liftQ γ₀ hker, fun l x hx => ?_⟩
  have hx' : (Submodule.Quotient.mk (H l) : MbMod Z₂.Z) = Submodule.Quotient.mk x := hx
  have hd : H l - x ∈ headCols Z₂.Z := (Submodule.Quotient.eq _).1 hx'
  refine ⟨(hH l).2.1.trans (firstQuotient_of_quotient_eq hs Z₂ TT hx'), ?_⟩
  rw [← (hH l).2.2]
  have := laG_headCols Zh₂ T T' Z₂ hZ₂ (unit_zzm hs Zh₂ T T' hu₂) hd
  rw [← laGLin_apply, map_sub, sub_eq_zero] at this
  exact this.symm

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
