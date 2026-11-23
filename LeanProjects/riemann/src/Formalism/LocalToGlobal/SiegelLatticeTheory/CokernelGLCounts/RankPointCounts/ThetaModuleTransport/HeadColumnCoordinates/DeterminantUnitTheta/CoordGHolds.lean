import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GraphTransport4

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section Parts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

private theorem mem_span_sum_elim_swap (f f' : Fin (r + 1) → V) (u : V)
    (hu : u ∈ Submodule.span E (Set.range (Sum.elim f f'))) :
    u ∈ Submodule.span E (Set.range (Sum.elim f' f)) := by
  rwa [Set.Sum.elim_range, Set.union_comm, ← Set.Sum.elim_range]

theorem gamR_sep {g : SplitG M.L} {t₁ t₂ : Term V M r} (hg₁ : GoodG H g t₁) (hg₂ : GoodG H g t₂)
    (hD0₁ : H.Dl t₁.f t₁.f' r = 0) (hD0₂ : H.Dl t₂.f t₂.f' r = 0) (hT : t₂.T = t₁.T) (hT' : t₂.T' = t₁.T') (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f')
    (hz : φ (H.mkW t₁.f ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩) = H.mkW t₂.f ⟨_, z_mem H t₂.f t₂.T hg₂.2.1⟩)
    (ho : φ (H.mkW t₁.f ⟨_, omP_mem H t₁.f t₁.f' hg₁.2.2.2.1⟩) =
      H.mkW t₂.f ⟨_, omP_mem H t₂.f t₂.f' hg₂.2.2.2.1⟩)
    (hz' : φ' (H.mkW t₁.f' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩) =
      H.mkW t₂.f' ⟨_, z_mem H t₂.f' t₂.T' hg₂.2.2.1⟩)
    (ho' : φ' (H.mkW t₁.f' ⟨_, omP_mem H t₁.f' t₁.f (unit_swap H t₁.f t₁.f' hg₁.2.2.2.1)⟩) =
      H.mkW t₂.f' ⟨_, omP_mem H t₂.f' t₂.f (unit_swap H t₂.f t₂.f' hg₂.2.2.2.1)⟩) :
    ∀ p ∈ GamR H t₁ (algebraMap F E (g.q : F)), ∀ p₂ ∈ GamR H t₂ (algebraMap F E (g.q : F)),
      PcG H hg₂ p₂.2.2.1 = PcG H hg₁ p.2.2.1 → PcG' H hg₂ p₂.2.2.2 = PcG' H hg₁ p.2.2.2 →
      p₂.2.2.1 = φ p.2.2.1 ∧ p₂.2.2.2 = φ' p.2.2.2 := by
  intro p hp p₂ hp₂ e1 e2
  obtain ⟨u, u', u'', hu, hu', -, rfl⟩ := hp
  obtain ⟨v, v', v'', hv, hv', -, rfl⟩ := hp₂
  simp only [PcG, PcG', coordW_mk, Prod.mk.injEq] at e1 e2
  obtain ⟨a1, a2⟩ := e1
  obtain ⟨b1, b2⟩ := e2
  have D1 := mkW_decomp H t₁.f t₁.f' t₁.T t₁.T' hg₁.2.1 hg₁.2.2.1 hg₁.2.2.2.1 hD0₁ ⟨u, hu⟩
    (mem_span_of_sharpG H hg₁ u)
  have D2 := mkW_decomp H t₂.f t₂.f' t₂.T t₂.T' hg₂.2.1 hg₂.2.2.1 hg₂.2.2.2.1 hD0₂ ⟨v, hv⟩
    (mem_span_of_sharpG H hg₂ v)
  have D1' := mkW_decomp H t₁.f' t₁.f t₁.T' t₁.T hg₁.2.2.1 hg₁.2.1
    (unit_swap H t₁.f t₁.f' hg₁.2.2.2.1) (by rw [dl_swap_r, hD0₁, map_zero]) ⟨u', hu'⟩
    (mem_span_sum_elim_swap t₁.f t₁.f' _ (mem_span_of_sharpG H hg₁ u'))
  have D2' := mkW_decomp H t₂.f' t₂.f t₂.T' t₂.T hg₂.2.2.1 hg₂.2.1
    (unit_swap H t₂.f t₂.f' hg₂.2.2.2.1) (by rw [dl_swap_r, hD0₂, map_zero]) ⟨v', hv'⟩
    (mem_span_sum_elim_swap t₂.f t₂.f' _ (mem_span_of_sharpG H hg₂ v'))
  dsimp only at D1 D2 D1' D2'
  have eT : algebraMap F E t₂.T = algebraMap F E t₁.T := by rw [hT]
  have eT' : algebraMap F E t₂.T' = algebraMap F E t₁.T' := by rw [hT']
  constructor
  · show H.mkW t₂.f ⟨v, hv⟩ = φ (H.mkW t₁.f ⟨u, hu⟩)
    rw [D1, D2, map_add, map_smul, map_smul, hz, ho, a1, a2, eT]
  · show H.mkW t₂.f' ⟨v', hv'⟩ = φ' (H.mkW t₁.f' ⟨u', hu'⟩)
    rw [D1', D2', map_add, map_smul, map_smul, hz', ho', b1, b2, eT']

theorem isomD_iffG {g : SplitG M.L} {t₁ t₂ : Term V M r} (hg₁ : GoodG H g t₁) (hg₂ : GoodG H g t₂)
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) :
    IsomD H t₁ t₂ θ ↔ ∀ Y W Y₂ W₂ : Ix r → M.L.O,
      PsiG H hg₂ (θ ((PsiG H hg₁).symm (Submodule.Quotient.mk Y))) = Submodule.Quotient.mk Y₂ →
      PsiG H hg₂ (θ ((PsiG H hg₁).symm (Submodule.Quotient.mk W))) = Submodule.Quotient.mk W₂ →
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t₂.f t₂.f')
          (algebraMap F E t₂.T) (algebraMap F E t₂.T') Y₂ W₂ -
        formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t₁.f t₁.f')
          (algebraMap F E t₁.T) (algebraMap F E t₁.T') Y W ∈ M.L.O := by
  constructor
  · intro hI Y W Y₂ W₂ h1 h2
    rw [PsiG_symm_mk] at h1 h2
    have e1 : θ (ddMk H t₁ ((sharpEquiv H t₁ (unit_gramHG H hg₁)).symm Y)) =
        ddMk H t₂ ((sharpEquiv H t₂ (unit_gramHG H hg₂)).symm Y₂) := by
      rw [← PsiG_symm_mk H hg₂, ← h1, LinearEquiv.symm_apply_apply]
    have e2 : θ (ddMk H t₁ ((sharpEquiv H t₁ (unit_gramHG H hg₁)).symm W)) =
        ddMk H t₂ ((sharpEquiv H t₂ (unit_gramHG H hg₂)).symm W₂) := by
      rw [← PsiG_symm_mk H hg₂, ← h2, LinearEquiv.symm_apply_apply]
    have k := hI _ _ _ _ e1 e2
    rw [h_eq_formG H hg₂, h_eq_formG H hg₁] at k
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply] at k
    exact k
  · intro hI x y x₂ y₂ h1 h2
    have k1 : PsiG H hg₂ (θ ((PsiG H hg₁).symm
        (Submodule.Quotient.mk (sharpEquiv H t₁ (unit_gramHG H hg₁) x)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramHG H hg₂) x₂) := by
      rw [PsiG_symm_mk, LinearEquiv.symm_apply_apply, h1, PsiG_mk]
    have k2 : PsiG H hg₂ (θ ((PsiG H hg₁).symm
        (Submodule.Quotient.mk (sharpEquiv H t₁ (unit_gramHG H hg₁) y)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramHG H hg₂) y₂) := by
      rw [PsiG_symm_mk, LinearEquiv.symm_apply_apply, h2, PsiG_mk]
    have k := hI _ _ _ _ k1 k2
    rw [h_eq_formG H hg₂ x₂ y₂, h_eq_formG H hg₁ x y]
    exact k

end Parts

theorem coordG_holds : CoordG := by
  unfold CoordG
  intro F _ _ _ E _ _ _ _ M g hsplit r n V _ _ H _ t₁ f₂ f₂' φ φ' hyp hD0 hDu hZZ
  obtain ⟨hGen, hF₂, hF₂', hId, hS, hS'⟩ := hyp
  have hTerm := hGen.1
  have hFr := hTerm.2.1
  have hFr' := hTerm.2.2.1
  have hF₁ : MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hFr.2.1, hFr.2.2.1⟩
  have hF₁' : MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hFr'.2.1, hFr'.2.2.1⟩
  have hDu₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hTerm.2.2.2.1
  have hg₁ : GoodG H g t₁ := ⟨hsplit, hF₁, hF₁', hDu₁, unit_gramH_of H hsplit hF₁ hF₁' hDu₁ hD0⟩
  have hD0₂ : H.Dl f₂ f₂' r = 0 := by
    have e := hId.2.2.2.2.2
    rw [hD0, zero_mul] at e
    exact (hDu₁.mul_left_eq_zero).mp e.symm
  set t₂ : Term V M r := { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } with ht₂
  have hg₂ : GoodG H g t₂ :=
    ⟨hsplit, hF₂, hF₂', hDu, unit_gramH_of H hsplit (t := t₂) hF₂ hF₂' hDu hD0₂⟩
  have hMM : MMInt H t₂ := mmInt_G H hg₂ hFr.2.2.2.1 (hTerm.2.2.2.2.2 g hsplit).2.1 hZZ
  have hz : φ (H.mkW t₁.f ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩) =
      H.mkW t₂.f ⟨_, z_mem H t₂.f t₂.T hg₂.2.1⟩ := by
    have e := hS ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩ ⟨_, z_mem H t₂.f t₂.T hg₂.2.1⟩ rfl rfl
    rwa [one_smul, one_smul] at e
  have hz' : φ' (H.mkW t₁.f' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩) =
      H.mkW t₂.f' ⟨_, z_mem H t₂.f' t₂.T' hg₂.2.2.1⟩ := by
    have e := hS' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩ ⟨_, z_mem H t₂.f' t₂.T' hg₂.2.2.1⟩ rfl rfl
    rwa [one_smul, one_smul] at e
  have ho := sends_omP H φ hDu₁ hDu hId.2.2.2.1
  have ho' := sends_omP' H φ' hDu₁ hDu hId.2.2.2.2.1
  have hP : ∀ w, PcG H hg₂ (φ w) = PcG H hg₁ w :=
    fun w => coordW_comp H φ hId.1 _ _ _ _ _ _ _ _ hz ho w
  have hP' : ∀ w, PcG' H hg₂ (φ' w) = PcG' H hg₁ w :=
    fun w => coordW_comp H φ' hId.2.1 _ _ _ _ _ _ _ _ ho' hz' w
  have hinj := gamR_sep H hg₁ hg₂ hD0 hD0₂ rfl rfl φ φ' hz ho hz' ho'
  apply Nat.card_congr
  refine Equiv.subtypeEquiv
    ⟨fun θ => (PsiG H hg₁).symm.trans (θ.trans (PsiG H hg₂)),
      fun ψ => (PsiG H hg₁).trans (ψ.trans (PsiG H hg₂).symm),
      fun θ => by ext x; simp, fun ψ => by ext x; simp⟩ ?_
  intro θ
  have hGR := graph_transport4 (PsiG H hg₁).toEquiv (PsiG H hg₂).toEquiv θ.toEquiv φ φ'
    (PcG H hg₁) (PcG H hg₂) (PcG' H hg₁) (PcG' H hg₂) _ _ _ _ (gamR_image H hg₁) (gamR_image H hg₂)
    hP hP' hinj
  constructor
  · rintro ⟨-, -, hI, -, hG⟩
    exact ⟨(isomD_iffG H hg₁ hg₂ θ).1 hI, hGR.1 (hG g hsplit)⟩
  · rintro ⟨hI, hG⟩
    refine ⟨hDu, hMM, (isomD_iffG H hg₁ hg₂ θ).2 hI,
      fun h => (Option.some_ne_none g (hsplit.symm.trans h)).elim, ?_⟩
    intro g' hg'
    rw [hsplit] at hg'
    obtain rfl := Option.some.inj hg'
    exact hGR.2 hG

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
