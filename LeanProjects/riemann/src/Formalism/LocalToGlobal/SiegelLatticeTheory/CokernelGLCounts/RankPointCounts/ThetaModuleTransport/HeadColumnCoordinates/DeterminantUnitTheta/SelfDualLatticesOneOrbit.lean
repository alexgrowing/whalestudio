import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.FirstIsoLinear

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

theorem firstIso_uniqueness_holds : FirstIsometryUniqueness := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ H₁ H₂ hK θ γ γ' hγ hγ'
  obtain ⟨-, -, hTT, hZ₁, -, hu₁, -⟩ := H₁
  obtain ⟨-, -, -, hZ₂, -, hu₂, hG₂⟩ := H₂
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (γ.1 (Submodule.Quotient.mk v))
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (γ'.1 (Submodule.Quotient.mk v))
  rw [← ha, ← hb]
  refine mk_eq_of hs T T' TT hTT Zh₂ Z₂ hZ₂ hu₂ hG₂ ?_ ?_
  · rw [← hγ v a ha.symm, ← hγ' v b hb.symm]
  · rw [← laM_mk Zh₂ T T' Z₂ hZ₂ (unit_zzm hs Zh₂ T T' hu₂), ← laM_mk Zh₂ T T' Z₂ hZ₂ (unit_zzm hs Zh₂ T T' hu₂),
      ha, hb]
    show laM Zh₂ T T' Z₂ hZ₂ _ (γ.1.toLinearMap _) = laM Zh₂ T T' Z₂ hZ₂ _ (γ'.1.toLinearMap _)
    rw [laM_equiv hs T T' Zh₁ Zh₂ Z₁ Z₂ hZ₁ hZ₂ hu₁ hu₂ hK _ γ.2.1,
      laM_equiv hs T T' Zh₁ Zh₂ Z₁ Z₂ hZ₁ hZ₂ hu₁ hu₂ hK _ γ'.2.1]

theorem firstIso_backward_holds : FirstIsometryBackward := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ H₁ H₂ hK γ
  obtain ⟨-, -, hTT, hZ₁, -, hu₁, -⟩ := H₁
  obtain ⟨-, -, -, hZ₂, -, hu₂, -⟩ := H₂
  have hLa : ∀ l x : Fin (r + 1) → M.R, γ.1 (Submodule.Quotient.mk l) = Submodule.Quotient.mk x →
      laG (ZZm g Zh₂ T T') x = laG (ZZm g Zh₁ T T') l := by
    intro l x h
    rw [← laM_mk Zh₂ T T' Z₂ hZ₂ (unit_zzm hs Zh₂ T T' hu₂), ← laM_mk Zh₁ T T' Z₁ hZ₁ (unit_zzm hs Zh₁ T T' hu₁),
      ← h]
    exact laM_equiv hs T T' Zh₁ Zh₂ Z₁ Z₂ hZ₁ hZ₂ hu₁ hu₂ hK γ.1.toLinearMap γ.2.1 _
  have hpt : ∀ (η : M.R) (l x : Fin (r + 1) → M.R), γ.1 (Submodule.Quotient.mk l) = Submodule.Quotient.mk x →
      γ.1 (Submodule.Quotient.mk (η • eV r + q2 hs • l)) = Submodule.Quotient.mk (η • eV r + q2 hs • x) := by
    intro η l x h
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_add, map_smul,
      map_smul, h, show (Submodule.Quotient.mk (eV r) : MbMod Z₁.Z) = eCl Z₁.Z from rfl, γ.2.2]
    rfl
  refine ⟨thEquiv hs TT γ, ?_, ?_, fun l l₂ h => thEquiv_spec hs TT γ h⟩
  · intro c l l₂ h
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (γ.1 (Submodule.Quotient.mk l))
    have h1 := thEquiv_spec hs TT γ hw.symm
    rw [h1, quotientMk_eq_iff_sub_mem_LL] at h
    have h2 : γ.1 (Submodule.Quotient.mk (dgR hs c • l)) = Submodule.Quotient.mk (dgR hs c • w) := by
      rw [Submodule.Quotient.mk_smul, map_smul, ← hw, Submodule.Quotient.mk_smul]
    rw [thEquiv_spec hs TT γ h2, quotientMk_eq_iff_sub_mem_LL, ← smul_sub]
    exact LL_dg_smul hs Z₂ TT c h
  · ext ⟨d, d', η, t⟩
    constructor
    · rintro ⟨_, ⟨l, η₀, rfl⟩, he⟩
      obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (γ.1 (Submodule.Quotient.mk l))
      refine ⟨w, η₀, ?_⟩
      rw [← he]
      simp only [Prod.mk.injEq]
      exact ⟨thEquiv_spec hs TT γ (hpt η₀ l w hw.symm), thEquiv_spec hs TT γ hw.symm, trivial,
        (hLa l w hw.symm).symm⟩
    · rintro ⟨x, η₀, he⟩
      obtain ⟨l, hl⟩ := Submodule.Quotient.mk_surjective _ (γ.1.symm (Submodule.Quotient.mk x))
      have hx : γ.1 (Submodule.Quotient.mk l) = Submodule.Quotient.mk x := by
        rw [hl, LinearEquiv.apply_symm_apply]
      refine ⟨(mk1 hs Z₁ TT (η₀ • eV r + q2 hs • l), mk1 hs Z₁ TT l, η₀, laG (ZZm g Zh₁ T T') l), ⟨l, η₀, rfl⟩, ?_⟩
      rw [he]
      simp only [Prod.mk.injEq]
      exact ⟨thEquiv_spec hs TT γ (hpt η₀ l x hx), thEquiv_spec hs TT γ hx, trivial, (hLa l x hx).symm⟩

theorem firstIso_forward_holds : FirstIsometryForward := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ H₁ H₂ hK θ hO hM
  obtain ⟨-, -, hTT, hZ₁, -, hu₁, hG₁⟩ := H₁
  obtain ⟨-, -, -, hZ₂, -, hu₂, hG₂⟩ := H₂
  obtain ⟨γ₀, h₀⟩ := firstIso_linear hs T T' TT hTT Zh₁ Zh₂ Z₁ Z₂ hZ₁ hZ₂ hu₁ hu₂ hG₂ θ hO hM
  obtain ⟨γ₁, h₁⟩ := firstIso_linear hs T T' TT hTT Zh₂ Zh₁ Z₂ Z₁ hZ₂ hZ₁ hu₂ hu₁ hG₁ θ.symm (olin_symm hs θ hO)
    (match1_symm hs θ hM)
  have c10 : γ₁ ∘ₗ γ₀ = LinearMap.id := by
    apply LinearMap.ext
    intro m
    obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (γ₀ (Submodule.Quotient.mk l))
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (γ₁ (Submodule.Quotient.mk x))
    obtain ⟨e1, e2⟩ := h₀ l x hx.symm
    obtain ⟨e3, e4⟩ := h₁ x y hy.symm
    rw [LinearMap.comp_apply, ← hx, ← hy, LinearMap.id_apply]
    refine mk_eq_of hs T T' TT hTT Zh₁ Z₁ hZ₁ hu₁ hG₁ ?_ (e4.trans e2)
    rw [← e3, ← e1, AddEquiv.symm_apply_apply]
  have c01 : γ₀ ∘ₗ γ₁ = LinearMap.id := by
    apply LinearMap.ext
    intro m
    obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (γ₁ (Submodule.Quotient.mk l))
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (γ₀ (Submodule.Quotient.mk x))
    obtain ⟨e1, e2⟩ := h₁ l x hx.symm
    obtain ⟨e3, e4⟩ := h₀ x y hy.symm
    rw [LinearMap.comp_apply, ← hx, ← hy, LinearMap.id_apply]
    refine mk_eq_of hs T T' TT hTT Zh₂ Z₂ hZ₂ hu₂ hG₂ ?_ (e4.trans e2)
    rw [← e3, ← e1, AddEquiv.apply_symm_apply]
  let γ : MbMod Z₁.Z ≃ₗ[M.R] MbMod Z₂.Z :=
    { γ₀ with
      invFun := γ₁
      left_inv := fun x => by simpa using LinearMap.congr_fun c10 x
      right_inv := fun x => by simpa using LinearMap.congr_fun c01 x }
  have hkap := kap_common hs T T' Zh₁ Zh₂ hu₁ hu₂ hK
  have hb : γ (bCls Z₁.Z) = bCls Z₂.Z := by
    show γ₀ (bCls Z₁.Z) = bCls Z₂.Z
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (γ₀ (bCls Z₁.Z))
    rw [← hx]
    rw [bCls, col_eq_mulVec] at hx
    obtain ⟨e1, e2⟩ := h₀ _ x hx.symm
    rw [bCls, col_eq_mulVec]
    have z1 : mk1 hs Z₁ TT (Z₁.Z.mulVec (eV r)) = 0 := by
      rw [firstQuotient_eq_zero_iff]
      refine ⟨eV r, ?_⟩
      show Z₁.Z.mulVec (eV r) - (TT * dgR hs (trO hs (eV (M := M) r (Fin.last r)))) • eV r = _
      simp [eV, trO_one]
    have z2 : mk1 hs Z₂ TT (Z₂.Z.mulVec (eV r)) = 0 := by
      rw [firstQuotient_eq_zero_iff]
      refine ⟨eV r, ?_⟩
      show Z₂.Z.mulVec (eV r) - (TT * dgR hs (trO hs (eV (M := M) r (Fin.last r)))) • eV r = _
      simp [eV, trO_one]
    refine mk_eq_of hs T T' TT hTT Zh₂ Z₂ hZ₂ hu₂ hG₂ ?_ ?_
    · rw [← e1, z1, z2, map_zero]
    · rw [e2, laG_b Zh₁ T T' Z₁ hZ₁ (unit_zzm hs Zh₁ T T' hu₁), laG_b Zh₂ T T' Z₂ hZ₂ (unit_zzm hs Zh₂ T T' hu₂),
        hkap]
  have hthe : θ (mk1 hs Z₁ TT (eV r)) = mk1 hs Z₂ TT (eV r) := by
    have hp : (mk1 hs Z₁ TT ((1 : M.R) • eV r + q2 hs • (0 : Fin (r + 1) → M.R)), mk1 hs Z₁ TT 0, (1 : M.R),
        laG (ZZm g Zh₁ T T') (0 : Fin (r + 1) → M.R)) ∈ Gam1 hs Z₁ TT (ZZm g Zh₁ T T') := ⟨0, 1, rfl⟩
    have hq : (θ (mk1 hs Z₁ TT ((1 : M.R) • eV r + q2 hs • (0 : Fin (r + 1) → M.R))), θ (mk1 hs Z₁ TT 0),
        (1 : M.R), laG (ZZm g Zh₁ T T') (0 : Fin (r + 1) → M.R)) ∈ Gam1 hs Z₂ TT (ZZm g Zh₂ T T') := by
      rw [← hM]; exact ⟨_, hp, rfl⟩
    obtain ⟨x, η, hx⟩ := hq
    simp only [Prod.mk.injEq] at hx
    obtain ⟨h1, h2, h3, h4⟩ := hx
    subst h3
    have hz : θ (mk1 hs Z₁ TT 0) = 0 := map_zero θ
    rw [hz, eq_comm, firstQuotient_eq_zero_iff] at h2
    have hx0 : x ∈ headCols Z₂.Z := by
      refine ker_fact hs T T' TT hTT Zh₂ Z₂ hZ₂ hu₂ hG₂ x ((firstQuotient_eq_zero_iff hs Z₂ TT x).2 h2) ?_
      rw [← h4, ← laGLin_apply (M := M) (ZZm g Zh₁ T T') 0, map_zero]
    simp only [one_smul, smul_zero, add_zero] at h1
    rw [h1, quotientMk_eq_iff_sub_mem_LL, add_sub_cancel_left]
    exact headCols_le_LL hs Z₂ TT (Submodule.smul_mem _ _ hx0)
  have he : γ (eCl Z₁.Z) = eCl Z₂.Z := by
    show γ₀ (eCl Z₁.Z) = eCl Z₂.Z
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (γ₀ (eCl Z₁.Z))
    rw [← hx]
    obtain ⟨e1, e2⟩ := h₀ (eV r) x hx.symm
    refine mk_eq_of hs T T' TT hTT Zh₂ Z₂ hZ₂ hu₂ hG₂ ?_ ?_
    · rw [← e1, hthe]
    · rw [e2, laG_e, laG_e, hkap]
  exact ⟨⟨γ, hb, he⟩, fun l l₂ h => (h₀ l l₂ h).1⟩

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
