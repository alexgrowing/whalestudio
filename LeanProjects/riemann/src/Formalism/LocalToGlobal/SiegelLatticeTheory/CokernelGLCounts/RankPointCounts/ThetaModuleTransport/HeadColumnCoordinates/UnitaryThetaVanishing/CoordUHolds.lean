import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.MemSpanOfSharpU

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

section Parts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem mmInt_U {t : Term V M r} (hg : GoodU H t) (hT : t.T ∈ 𝒪[F]) (hT' : t.T' ∈ 𝒪[F])
    (hint : ∀ a b, H.Zhat t.f t.f' a b ∈ M.L.O) : MMInt H t := by
  have hTO : algebraMap F E t.T ∈ M.L.O := Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨t.T, hT⟩
  have hTO' : algebraMap F E t.T' ∈ M.L.O := Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨t.T', hT'⟩
  have hgen : ∀ i j, H.h (H.MMfam t i) (H.MMfam t j) ∈ M.L.O := by
    intro i j
    have e := congrFun (congrFun (gramH_eqU H hg) i) j
    simp only [gramH, Matrix.of_apply] at e
    rw [e]
    rcases i with a | a <;> rcases j with b | b
    · simp only [gramC, Matrix.fromBlocks_apply₁₁, Matrix.of_apply]
      split_ifs
      · exact neg_mem hTO
      · exact zero_mem _
    · simp only [gramC, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
      exact cj_mem_O M.L (hint a b)
    · simp only [gramC, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]
      exact hint b a
    · simp only [gramC, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      split_ifs
      · exact neg_mem hTO'
      · exact zero_mem _
  have hzero : ∀ y : V, H.h 0 y = 0 := by
    intro y
    have h0 := H.h_smul_left 0 0 y
    rwa [zero_smul, zero_mul] at h0
  have h1 : ∀ i, ∀ m ∈ MMo H t, H.h m (H.MMfam t i) ∈ M.L.O := by
    intro i m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hgen j i
    | zero => rw [hzero]; exact zero_mem _
    | add x y _ _ hx hy => rw [H.h_add_left]; exact add_mem hx hy
    | smul c x _ hx => rw [Subring.smul_def, H.h_smul_left]; exact mul_mem c.2 hx
  intro m hm m' hm'
  have h2 : ∀ i, H.h (H.MMfam t i) m' ∈ M.L.O := by
    intro i
    rw [H.h_herm]
    exact cj_mem_O M.L (h1 i m' hm')
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact h2 j
  | zero => rw [hzero]; exact zero_mem _
  | add x y _ _ hx hy => rw [H.h_add_left]; exact add_mem hx hy
  | smul c x _ hx => rw [Subring.smul_def, H.h_smul_left]; exact mul_mem c.2 hx

theorem PsiU_symm_mk {t : Term V M r} (hg : GoodU H t) (Y : Ix r → M.L.O) :
    (PsiU H hg).symm (Submodule.Quotient.mk Y) =
      ddMk H t ((sharpEquiv H t (unit_gramHU H hg)).symm Y) := by
  rw [LinearEquiv.symm_apply_eq, PsiU_mk, LinearEquiv.apply_symm_apply]

theorem isomD_iffU {t₁ t₂ : Term V M r} (hg₁ : GoodU H t₁) (hg₂ : GoodU H t₂)
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) :
    IsomD H t₁ t₂ θ ↔ ∀ Y W Y₂ W₂ : Ix r → M.L.O,
      PsiU H hg₂ (θ ((PsiU H hg₁).symm (Submodule.Quotient.mk Y))) = Submodule.Quotient.mk Y₂ →
      PsiU H hg₂ (θ ((PsiU H hg₁).symm (Submodule.Quotient.mk W))) = Submodule.Quotient.mk W₂ →
      formC M.L.O (M.L.cj : E →+* E) (H.Zhat t₂.f t₂.f') (algebraMap F E t₂.T) (algebraMap F E t₂.T')
          Y₂ W₂ -
        formC M.L.O (M.L.cj : E →+* E) (H.Zhat t₁.f t₁.f') (algebraMap F E t₁.T)
          (algebraMap F E t₁.T') Y W ∈ M.L.O := by
  unfold IsomD
  constructor
  · intro h Y W Y₂ W₂ hY hW
    rw [PsiU_symm_mk H hg₁, ← LinearEquiv.eq_symm_apply, PsiU_symm_mk H hg₂] at hY hW
    have key := h _ _ _ _ hY hW
    rw [h_eq_formCU H hg₂, h_eq_formCU H hg₁] at key
    simpa only [LinearEquiv.apply_symm_apply] using key
  · intro h x y x₂ y₂ hx hy
    have hx' : PsiU H hg₂ (θ ((PsiU H hg₁).symm
        (Submodule.Quotient.mk (sharpEquiv H t₁ (unit_gramHU H hg₁) x)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramHU H hg₂) x₂) := by
      rw [PsiU_symm_mk H hg₁, LinearEquiv.symm_apply_apply, hx, PsiU_mk]
    have hy' : PsiU H hg₂ (θ ((PsiU H hg₁).symm
        (Submodule.Quotient.mk (sharpEquiv H t₁ (unit_gramHU H hg₁) y)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramHU H hg₂) y₂) := by
      rw [PsiU_symm_mk H hg₁, LinearEquiv.symm_apply_apply, hy, PsiU_mk]
    rw [h_eq_formCU H hg₂, h_eq_formCU H hg₁]
    exact h _ _ _ _ hx' hy'

theorem kap_eq (f₁ f₁' f₂ f₂' : Fin (r + 1) → V) (hD₁ : IsUnit (H.Dl f₁ f₁' (r + 1)))
    (hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)))
    (hrel : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    kapU H f₂ f₂' = kapU H f₁ f₁' := by
  obtain ⟨u₁, hu₁⟩ := hD₁
  obtain ⟨u₂, hu₂⟩ := hD₂
  simp only [kapU]
  rw [← hu₁, ← hu₂] at hrel ⊢
  rw [Ring.inverse_unit, Ring.inverse_unit, Units.inv_mul_eq_iff_eq_mul, mul_left_comm,
    Units.eq_inv_mul_iff_mul_eq]
  linear_combination -hrel

private theorem Dl_swap_eq_cj_Dl (f f' : Fin (r + 1) → V) (l : ℕ) :
    H.Dl f' f l = M.L.cj (H.Dl f f' l) := by
  unfold HermSp.Dl
  split_ifs with hl
  · rw [AlgEquiv.map_det, ← Matrix.det_transpose]
    congr 1
    ext a b
    simp only [HermSp.Zhat, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply,
      AlgEquiv.mapMatrix_apply, Matrix.map_apply]
    exact H.h_herm _ _
  · simp

theorem rel_swap (f₁ f₁' f₂ f₂' : Fin (r + 1) → V)
    (hrel : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    H.Dl f₁' f₁ r * H.Dl f₂' f₂ (r + 1) = H.Dl f₂' f₂ r * H.Dl f₁' f₁ (r + 1) := by
  rw [Dl_swap_eq_cj_Dl H f₁, Dl_swap_eq_cj_Dl H f₂, Dl_swap_eq_cj_Dl H f₂, Dl_swap_eq_cj_Dl H f₁, ← map_mul, ← map_mul,
    hrel]

end Parts

private theorem image_prod_map_eq_iff_image_transport_eq {A₁ A₂ B₁ B₂ C₁ C₂ D : Type*} (G₁ : Set (A₁ × B₁)) (G₂ : Set (A₂ × B₂))
    (Ψ₁ : A₁ → C₁) (Ψ₁' : C₁ → A₁) (hΨ₁ : ∀ a, Ψ₁' (Ψ₁ a) = a) (Ψ₂ : A₂ → C₂)
    (hΨ₂ : Function.Injective Ψ₂) (P₁ : B₁ → D) (P₂ : B₂ → D) (θ : A₁ → A₂) (φ : B₁ → B₂)
    (hP : ∀ b, P₂ (φ b) = P₁ b)
    (sep : ∀ p ∈ G₁, ∀ q ∈ G₂, P₂ q.2 = P₁ p.2 → q.2 = φ p.2) :
    (fun p : A₁ × B₁ => (θ p.1, φ p.2)) '' G₁ = G₂ ↔
      (fun p : C₁ × D => (Ψ₂ (θ (Ψ₁' p.1)), p.2)) '' ((fun p : A₁ × B₁ => (Ψ₁ p.1, P₁ p.2)) '' G₁) =
        (fun p : A₂ × B₂ => (Ψ₂ p.1, P₂ p.2)) '' G₂ := by
  rw [Set.image_image]
  simp only [hΨ₁]
  constructor
  · intro h
    rw [← h, Set.image_image]
    simp only [hP]
  · intro h
    ext ⟨x, y⟩
    constructor
    · rintro ⟨p, hp, hpq⟩
      have hm : (Ψ₂ (θ p.1), P₁ p.2) ∈ (fun p : A₂ × B₂ => (Ψ₂ p.1, P₂ p.2)) '' G₂ := by
        rw [← h]
        exact ⟨p, hp, rfl⟩
      obtain ⟨q, hq, hqe⟩ := hm
      simp only [Prod.mk.injEq] at hqe hpq
      have h1 := hΨ₂ hqe.1
      have h2 := sep p hp q hq hqe.2
      rw [← hpq.1, ← hpq.2, ← h1, ← h2]
      exact hq
    · intro hq
      have hm : (Ψ₂ x, P₂ y) ∈ (fun p : A₁ × B₁ => (Ψ₂ (θ p.1), P₁ p.2)) '' G₁ := by
        rw [h]
        exact ⟨(x, y), hq, rfl⟩
      obtain ⟨p, hp, hpe⟩ := hm
      simp only [Prod.mk.injEq] at hpe
      have h1 := hΨ₂ hpe.1
      have h2 := sep p hp (x, y) hq hpe.2.symm
      refine ⟨p, hp, ?_⟩
      simp only [Prod.mk.injEq]
      exact ⟨h1, h2.symm⟩

theorem coordU_holds : CoordU := by
  intro F _ _ _ E _ _ _ _ M hsplit r n V _ _ H _ t₁ f₂ f₂' φ φ' hyp hDr hD₂ hZ
  obtain ⟨⟨⟨_, hF₁, hF₁', hD₁, hG₁, _⟩, _⟩, hK₂, hK₂', hId, hS, hS'⟩ := hyp
  obtain ⟨hiso, hiso', _, hom', hom, hrel⟩ := hId
  set t₂ : Term V M r := { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } with ht₂
  have hK₁ : MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hF₁.2.1, hF₁.2.2.1⟩
  have hK₁' : MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hF₁'.2.1, hF₁'.2.2.1⟩
  have hT : t₁.T ∈ 𝒪[F] := hF₁.2.2.2.1
  have hT' : t₁.T' ∈ 𝒪[F] := hF₁'.2.2.2.1
  have hG₁u := Formalism.L2.SG.LsDatumA.isUnit_Gdet H _ _ _ _ hG₁
  have hN₁ : IsUnit (H.normE (H.Dl t₁.f t₁.f' (r + 1))) := hD₁.mul (hD₁.map M.L.cj)
  have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
  have e := gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hrel
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have hm : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁u
    exact isUnit_of_mul_isUnit_left hm
  have hg₁ : GoodU H t₁ := ⟨hsplit, hK₁, hK₁', hD₁, hG₁u⟩
  have hg₂ : GoodU H t₂ := ⟨hsplit, hK₂, hK₂', hD₂, hG₂⟩
  have hint₂ : MMInt H t₂ := mmInt_U H hg₂ hT hT' hZ
  have hD₁s : IsUnit (H.Dl t₁.f' t₁.f (r + 1)) := by
    rw [Dl_swap_eq_cj_Dl]
    exact hD₁.map _
  have hD₂s : IsUnit (H.Dl f₂' f₂ (r + 1)) := by
    rw [Dl_swap_eq_cj_Dl]
    exact hD₂.map _
  have hnu : nuU H t₂.f t₂.f' = nuU H t₁.f t₁.f' := by
    show nuU H f₂ f₂' = nuU H t₁.f t₁.f'
    unfold nuU
    rw [h_omP_omPU H f₂ f₂' t₁.T' hK₂', h_omP_omPU H t₁.f t₁.f' t₁.T' hK₁',
      kap_eq H t₁.f t₁.f' f₂ f₂' hD₁ hD₂ hrel]
  have hnu' : nuU H t₂.f' t₂.f = nuU H t₁.f' t₁.f := by
    show nuU H f₂' f₂ = nuU H t₁.f' t₁.f
    unfold nuU
    rw [h_omP_omPU H f₂' f₂ t₁.T hK₂, h_omP_omPU H t₁.f' t₁.f t₁.T hK₁,
      kap_eq H t₁.f' t₁.f f₂' f₂ hD₁s hD₂s (rel_swap H _ _ _ _ hrel)]
  have sends1 : ∀ {g₁ g₂ : Fin (r + 1) → V} (ψ : H.Wb g₁ →ₗ[E] H.Wb g₂) (v₁ v₂ : V)
      (h₁ : v₁ ∈ H.perp (H.X g₁)) (h₂ : v₂ ∈ H.perp (H.X g₂)), H.SendsTo ψ 1 1 v₁ v₂ →
      ψ (H.mkW g₁ ⟨v₁, h₁⟩) = H.mkW g₂ ⟨v₂, h₂⟩ := by
    intro g₁ g₂ ψ v₁ v₂ h₁ h₂ hs
    simpa only [one_smul] using hs ⟨v₁, h₁⟩ ⟨v₂, h₂⟩ rfl rfl
  have hc : ∀ w, PcU H hg₂ (φ w) = PcU H hg₁ w := by
    intro w
    unfold PcU
    refine coordW_comp H φ hiso _ _ _ _ _ _ _ _ ?_ ?_ w
    · exact sends1 _ _ _ _ _ hS
    · exact sends_omP H φ hD₁ hD₂ hom'
  have hc' : ∀ w, PcU' H hg₂ (φ' w) = PcU' H hg₁ w := by
    intro w
    unfold PcU'
    refine coordW_comp H φ' hiso' _ _ _ _ _ _ _ _ ?_ ?_ w
    · exact sends_omP' H φ' hD₁ hD₂ hom
    · exact sends1 _ _ _ _ _ hS'
  have sep := gam_sepU H hg₁ hg₂ rfl hnu φ (sends1 _ _ _ _ _ hS) (sends_omP H φ hD₁ hD₂ hom')
  have sep' := gam_sepU' H hg₁ hg₂ rfl hnu' φ' (sends1 _ _ _ _ _ hS') (sends_omP' H φ' hD₁ hD₂ hom)
  let eqv : (DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) ≃
      (DDc M.L.O (M.L.cj : E →+* E) (H.Zhat t₁.f t₁.f') (algebraMap F E t₁.T) (algebraMap F E t₁.T') ≃ₗ[M.L.O]
        DDc M.L.O (M.L.cj : E →+* E) (H.Zhat f₂ f₂') (algebraMap F E t₁.T) (algebraMap F E t₁.T')) :=
    { toFun := fun θ => ((PsiU H hg₁).symm.trans θ).trans (PsiU H hg₂)
      invFun := fun ψ => ((PsiU H hg₁).trans ψ).trans (PsiU H hg₂).symm
      left_inv := fun θ => by
        ext x
        simp
      right_inv := fun ψ => by
        ext x
        simp }
  refine Nat.card_congr (Equiv.subtypeEquiv eqv ?_)
  intro θ
  simp only [Theta, ThetaC, Set.mem_setOf_eq]
  rw [isomD_iffU H hg₁ hg₂ θ]
  have key := image_prod_map_eq_iff_image_transport_eq (Gam H t₁) (Gam H t₂) (PsiU H hg₁) (PsiU H hg₁).symm
    (PsiU H hg₁).symm_apply_apply (PsiU H hg₂) (PsiU H hg₂).injective (PcU H hg₁) (PcU H hg₂) θ φ
    hc sep
  have key' := image_prod_map_eq_iff_image_transport_eq (Gam' H t₁) (Gam' H t₂) (PsiU H hg₁) (PsiU H hg₁).symm
    (PsiU H hg₁).symm_apply_apply (PsiU H hg₂) (PsiU H hg₂).injective (PcU' H hg₁) (PcU' H hg₂) θ φ'
    hc' sep'
  constructor
  · rintro ⟨_, _, hI, hGm, _⟩
    obtain ⟨hA, hB⟩ := hGm hsplit
    refine ⟨hI, ?_, ?_⟩
    · rw [← gam_imageU H hg₁]
      refine Eq.trans ?_ (gam_imageU H hg₂)
      exact key.1 hA
    · rw [← gam_imageU' H hg₁]
      refine Eq.trans ?_ (gam_imageU' H hg₂)
      exact key'.1 hB
  · rintro ⟨hI, hA, hB⟩
    refine ⟨hD₂, hint₂, hI, fun _ => ⟨?_, ?_⟩, fun g hg => ?_⟩
    · refine key.2 ?_
      rw [gam_imageU H hg₁]
      exact hA.trans (gam_imageU H hg₂).symm
    · refine key'.2 ?_
      rw [gam_imageU' H hg₁]
      exact hB.trans (gam_imageU' H hg₂).symm
    · rw [hsplit] at hg
      cases hg

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU
