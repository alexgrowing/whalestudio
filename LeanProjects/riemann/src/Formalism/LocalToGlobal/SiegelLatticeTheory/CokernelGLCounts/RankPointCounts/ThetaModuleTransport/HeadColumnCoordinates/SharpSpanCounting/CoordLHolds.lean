import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.MemSpanOfSharp

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

section Parts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

private theorem h_MMfam_mem_O_of_goodL_integral {t : Term V M r} (hg : GoodL H t) (hT : t.T ∈ 𝒪[F]) (hT' : t.T' ∈ 𝒪[F])
    (hint : ∀ a b, H.Zhat t.f t.f' a b ∈ M.L.O) (i j : Fin (r + 1) ⊕ Fin (r + 1)) :
    H.h (H.MMfam t i) (H.MMfam t j) ∈ M.L.O := by
  have alg : ∀ T : F, T ∈ 𝒪[F] → algebraMap F E T ∈ M.L.O := by
    intro T hT
    rw [M.L.O_def]
    have e : algebraMap F E T = algebraMap 𝒪[F] E ⟨T, hT⟩ := rfl
    rw [e]
    exact isIntegral_algebraMap
  rw [mmfam_none H hg.1 t]
  rcases i with a | a <;> rcases j with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · by_cases h : a ≠ Fin.last r ∨ b ≠ Fin.last r
    · rw [hg.2.1.1 a b h]
      exact zero_mem _
    · push_neg at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hg.2.1.2]
      exact neg_mem (alg _ hT)
  · rw [H.h_herm (t.f' b) (t.f a)]
    exact cj_mem_O _ (hint a b)
  · exact hint b a
  · by_cases h : a ≠ Fin.last r ∨ b ≠ Fin.last r
    · rw [hg.2.2.1.1 a b h]
      exact zero_mem _
    · push_neg at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hg.2.2.1.2]
      exact neg_mem (alg _ hT')

theorem mmInt_L {t : Term V M r} (hg : GoodL H t) (hT : t.T ∈ 𝒪[F]) (hT' : t.T' ∈ 𝒪[F])
    (hint : ∀ a b, H.Zhat t.f t.f' a b ∈ M.L.O) : MMInt H t := by
  intro m hm m' hm'
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hm' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact h_MMfam_mem_O_of_goodL_integral H hg hT hT' hint i j
    | zero =>
      rw [h_zero_right]
      exact zero_mem _
    | add y y' _ _ h1 h2 =>
      rw [h_add_right]
      exact add_mem h1 h2
    | smul c y _ h1 =>
      rw [show c • y = (c : E) • y from rfl, h_smul_right]
      exact mul_mem (cj_mem_O _ c.2) h1
  | zero =>
    have h0 : H.h 0 m' = 0 := by simpa using H.h_smul_left 0 0 m'
    rw [h0]
    exact zero_mem _
  | add x x' _ _ h1 h2 =>
    rw [H.h_add_left]
    exact add_mem h1 h2
  | smul c x _ h1 =>
    rw [show c • x = (c : E) • x from rfl, H.h_smul_left]
    exact mul_mem c.2 h1

theorem Psi_symm_mk {t : Term V M r} (hg : GoodL H t) (Y : Ix r → M.L.O) :
    (Psi H hg).symm (Submodule.Quotient.mk Y) =
      ddMk H t ((sharpEquiv H t (unit_gramH H hg)).symm Y) := by
  rw [LinearEquiv.symm_apply_eq, Psi_mk, LinearEquiv.apply_symm_apply]

private theorem map_mkW_inverse_smul_of_sendsTo {f₁ f₂ : Fin (r + 1) → V} (φ : H.Wb f₁ ≃ₗ[E] H.Wb f₂) {D₁ D₂ : E}
    (hD₁ : IsUnit D₁) (hD₂ : IsUnit D₂) {v₁ v₂ : V} (h₁ : v₁ ∈ H.perp (H.X f₁))
    (h₂ : v₂ ∈ H.perp (H.X f₂)) (hS : H.SendsTo (φ : H.Wb f₁ →ₗ[E] H.Wb f₂) D₂ D₁ v₁ v₂)
    (k₁ : Ring.inverse D₁ • v₁ ∈ H.perp (H.X f₁)) (k₂ : Ring.inverse D₂ • v₂ ∈ H.perp (H.X f₂)) :
    φ (H.mkW f₁ ⟨Ring.inverse D₁ • v₁, k₁⟩) = H.mkW f₂ ⟨Ring.inverse D₂ • v₂, k₂⟩ := by
  obtain ⟨u₁, rfl⟩ := hD₁
  obtain ⟨u₂, rfl⟩ := hD₂
  have S := hS ⟨v₁, h₁⟩ ⟨v₂, h₂⟩ rfl rfl
  simp only [LinearEquiv.coe_coe] at S
  have e₁ : (⟨Ring.inverse (u₁ : E) • v₁, k₁⟩ : H.perp (H.X f₁)) =
      Ring.inverse (u₁ : E) • (⟨v₁, h₁⟩ : H.perp (H.X f₁)) := rfl
  have e₂ : (⟨Ring.inverse (u₂ : E) • v₂, k₂⟩ : H.perp (H.X f₂)) =
      Ring.inverse (u₂ : E) • (⟨v₂, h₂⟩ : H.perp (H.X f₂)) := rfl
  rw [e₁, e₂, map_smul, map_smul, map_smul, Ring.inverse_unit, Ring.inverse_unit]
  have S' : φ (H.mkW f₁ ⟨v₁, h₁⟩) = ((u₂⁻¹ : Eˣ) * (u₁ : E)) • H.mkW f₂ ⟨v₂, h₂⟩ := by
    rw [mul_smul, ← S, smul_smul, Units.inv_mul, one_smul]
  rw [S', smul_smul, mul_left_comm, Units.inv_mul, mul_one]

private theorem hermSp_om_eq_om'_swap (f f' : Fin (r + 1) → V) : H.om f f' = H.om' f' f := by
  have hZ : H.Zhat f' f = (H.Zhat f f').transpose.map (M.L.cj : E →+* E) := by
    ext a b
    simp only [HermSp.Zhat, Matrix.of_apply, Matrix.map_apply, Matrix.transpose_apply]
    rw [H.h_herm]
    rfl
  have hA : ∀ b, (H.Zhat f' f).adjugate b (Fin.last r) =
      M.L.cj ((H.Zhat f f').adjugate (Fin.last r) b) := by
    intro b
    rw [hZ, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate, RingHom.mapMatrix_apply,
      Matrix.map_apply, ← Matrix.adjugate_transpose, Matrix.transpose_apply]
    rfl
  simp only [HermSp.om, HermSp.om', hA]

theorem isomD_iff {t₁ t₂ : Term V M r} (hg₁ : GoodL H t₁) (hg₂ : GoodL H t₂)
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) :
    IsomD H t₁ t₂ θ ↔ ∀ Y W Y₂ W₂ : Ix r → M.L.O,
      Psi H hg₂ (θ ((Psi H hg₁).symm (Submodule.Quotient.mk Y))) = Submodule.Quotient.mk Y₂ →
      Psi H hg₂ (θ ((Psi H hg₁).symm (Submodule.Quotient.mk W))) = Submodule.Quotient.mk W₂ →
      formC M.L.O (M.L.cj : E →+* E) (H.Zhat t₂.f t₂.f') (algebraMap F E t₂.T) (algebraMap F E t₂.T')
          Y₂ W₂ -
        formC M.L.O (M.L.cj : E →+* E) (H.Zhat t₁.f t₁.f') (algebraMap F E t₁.T)
          (algebraMap F E t₁.T') Y W ∈ M.L.O := by
  constructor
  · intro hD Y W Y₂ W₂ hY hW
    rw [Psi_symm_mk] at hY hW
    rw [← LinearEquiv.eq_symm_apply, Psi_symm_mk] at hY hW
    have key := hD _ _ _ _ hY hW
    rw [h_eq_formC H hg₂, h_eq_formC H hg₁] at key
    simpa only [LinearEquiv.apply_symm_apply] using key
  · intro hC x y x₂ y₂ hx hy
    have hx' : Psi H hg₂ (θ ((Psi H hg₁).symm (Submodule.Quotient.mk
        (sharpEquiv H t₁ (unit_gramH H hg₁) x)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramH H hg₂) x₂) := by
      rw [Psi_symm_mk, LinearEquiv.symm_apply_apply, hx, Psi_mk]
    have hy' : Psi H hg₂ (θ ((Psi H hg₁).symm (Submodule.Quotient.mk
        (sharpEquiv H t₁ (unit_gramH H hg₁) y)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramH H hg₂) y₂) := by
      rw [Psi_symm_mk, LinearEquiv.symm_apply_apply, hy, Psi_mk]
    have key := hC _ _ _ _ hx' hy'
    rw [h_eq_formC H hg₂, h_eq_formC H hg₁]
    exact key

end Parts

theorem coordL_holds : CoordL := by
  intro F _ _ _ E _ _ _ _ M _hOK hsplit r n V _ _ H _hn t₁ f₂ f₂' φ φ' hyp hDl hD₂ hint
  set t₂ : Term V M r := { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } with ht₂
  have fr := hyp.1.1.2.1
  have fr' := hyp.1.1.2.2.1
  have hg₁ : GoodL H t₁ :=
    ⟨hsplit, ⟨fr.2.1, fr.2.2.1⟩, ⟨fr'.2.1, fr'.2.2.1⟩, dl_succ_unit hyp, hDl⟩
  have hg₂ : GoodL H t₂ := ⟨hsplit, hyp.2.1, hyp.2.2.1, hD₂, dl_zero_two hyp hDl⟩
  have hmm : MMInt H t₂ := mmInt_L H hg₂ fr.2.2.2.1 fr'.2.2.2.1 hint
  obtain ⟨hiso, hiso', -, hS, hS', -⟩ := hyp.2.2.2.1
  have hz : φ (H.mkW t₁.f ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩) =
      H.mkW t₂.f ⟨_, z_mem H t₂.f t₂.T hg₂.2.1⟩ := by
    simpa using hyp.2.2.2.2.1 ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩ ⟨_, z_mem H t₂.f t₂.T hg₂.2.1⟩ rfl rfl
  have hz' : φ' (H.mkW t₁.f' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩) =
      H.mkW t₂.f' ⟨_, z_mem H t₂.f' t₂.T' hg₂.2.2.1⟩ := by
    simpa using hyp.2.2.2.2.2 ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩ ⟨_, z_mem H t₂.f' t₂.T' hg₂.2.2.1⟩ rfl rfl
  have ho : φ (H.mkW t₁.f ⟨_, omP_mem H t₁.f t₁.f' hg₁.2.2.2.1⟩) =
      H.mkW t₂.f ⟨_, omP_mem H t₂.f t₂.f' hg₂.2.2.2.1⟩ :=
    map_mkW_inverse_smul_of_sendsTo H φ hg₁.2.2.2.1 hg₂.2.2.2.1 (om'_mem H _ _) (om'_mem H _ _) hS _ _
  have hS'' : H.SendsTo (φ' : H.Wb t₁.f' →ₗ[E] H.Wb t₂.f') (H.Dl t₂.f' t₂.f (r + 1))
      (H.Dl t₁.f' t₁.f (r + 1)) (H.om' t₁.f' t₁.f) (H.om' t₂.f' t₂.f) := by
    rw [dl_swap_full H t₂.f t₂.f', dl_swap_full H t₁.f t₁.f', ← hermSp_om_eq_om'_swap H t₁.f t₁.f',
      ← hermSp_om_eq_om'_swap H t₂.f t₂.f']
    exact hS'
  have ho' : φ' (H.mkW t₁.f' ⟨_, omP_mem H t₁.f' t₁.f (unit_swap H t₁.f t₁.f' hg₁.2.2.2.1)⟩) =
      H.mkW t₂.f' ⟨_, omP_mem H t₂.f' t₂.f (unit_swap H t₂.f t₂.f' hg₂.2.2.2.1)⟩ :=
    map_mkW_inverse_smul_of_sendsTo H φ' (unit_swap H _ _ hg₁.2.2.2.1) (unit_swap H _ _ hg₂.2.2.2.1)
      (om'_mem H _ _) (om'_mem H _ _) hS'' _ _
  have hPc : ∀ w, PcL H hg₂ (φ w) = PcL H hg₁ w := fun w =>
    coordW_comp H φ hiso _ _ _ _ _ _ _ _ hz ho w
  have hPc' : ∀ w, PcL' H hg₂ (φ' w) = PcL' H hg₁ w := fun w =>
    coordW_comp H φ' hiso' _ _ _ _ _ _ _ _ ho' hz' w
  have hmem : ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂, θ ∈ Theta H t₁ t₂ φ φ' ↔
      ((Psi H hg₁).symm.trans θ).trans (Psi H hg₂) ∈
        ThetaC M.L.O (M.L.cj : E →+* E) (H.Zhat t₁.f t₁.f') (H.Zhat f₂ f₂')
          (algebraMap F E t₁.T) (algebraMap F E t₁.T') := by
    intro θ
    have g1 := graph_transport (Psi H hg₁).toEquiv (Psi H hg₂).toEquiv θ.toEquiv φ
      (PcL H hg₁) (PcL H hg₂) (Gam H t₁) (Gam H t₂) _ _ (gam_image H hg₁) (gam_image H hg₂) hPc
      (gam_sep H hg₁ hg₂ rfl φ hz ho)
    have g2 := graph_transport (Psi H hg₁).toEquiv (Psi H hg₂).toEquiv θ.toEquiv φ'
      (PcL' H hg₁) (PcL' H hg₂) (Gam' H t₁) (Gam' H t₂) _ _ (gam_image' H hg₁) (gam_image' H hg₂)
      hPc' (gam_sep' H hg₁ hg₂ rfl φ' hz' ho')
    simp only [Theta, ThetaC, Set.mem_setOf_eq]
    constructor
    · rintro ⟨-, -, hI, hG, -⟩
      obtain ⟨a, b⟩ := hG hsplit
      exact ⟨(isomD_iff H hg₁ hg₂ θ).1 hI, g1.1 a, g2.1 b⟩
    · rintro ⟨hI, a, b⟩
      refine ⟨hD₂, hmm, (isomD_iff H hg₁ hg₂ θ).2 hI, fun _ => ⟨g1.2 a, g2.2 b⟩, ?_⟩
      intro g hg
      rw [hsplit] at hg
      cases hg
  let e : (DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) ≃
      (DDc M.L.O (M.L.cj : E →+* E) (H.Zhat t₁.f t₁.f') (algebraMap F E t₁.T) (algebraMap F E t₁.T')
        ≃ₗ[M.L.O] DDc M.L.O (M.L.cj : E →+* E) (H.Zhat f₂ f₂') (algebraMap F E t₁.T)
          (algebraMap F E t₁.T')) :=
    { toFun := fun θ => ((Psi H hg₁).symm.trans θ).trans (Psi H hg₂)
      invFun := fun θc => ((Psi H hg₁).trans θc).trans (Psi H hg₂).symm
      left_inv := fun θ => by
        ext x
        simp
      right_inv := fun θc => by
        ext x
        simp }
  exact Nat.card_congr (e.subtypeEquiv hmem)

end Formalism.L2.SG.LocalCountModules.LocCntCommon
