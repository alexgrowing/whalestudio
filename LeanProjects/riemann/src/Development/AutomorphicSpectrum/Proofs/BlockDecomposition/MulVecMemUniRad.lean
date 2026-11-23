import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMulRightInvariantOfCenter

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotVan

section Radical

variable {n : ℕ} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}

theorem uOf_val' (hW : W₁ ≤ W₂) (X : nilrad W₁ W₂) : (uOf hW X).val = 1 + X.1 := rfl

theorem uOf_eq (hW : W₁ ≤ W₂) (X : nilrad W₁ W₂) : uOf hW X = GlobalTheory.CompanionTheory.LocVan.uOf X := Units.ext rfl

theorem uOf_inv_val (hW : W₁ ≤ W₂) (X : nilrad W₁ W₂) :
    ((uOf hW X)⁻¹ : GL (Fin n) ℂ).val = 1 - X.1 + X.1 * X.1 := rfl

def uniRad (hW : W₁ ≤ W₂) : Subgroup (GL (Fin n) ℂ) where
  carrier := {g | g.val - 1 ∈ nilrad W₁ W₂}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have e : (a * b).val - 1 = (a.val - 1) + (b.val - 1) + (a.val - 1) * (b.val - 1) := by
      rw [Units.val_mul]; noncomm_ring
    change (a * b).val - 1 ∈ nilrad W₁ W₂
    rw [e]
    exact (nilrad W₁ W₂).add_mem ((nilrad W₁ W₂).add_mem ha hb) (GlobalTheory.CompanionTheory.LocVan.nil_mul_mem hW ha hb)
  inv_mem' := fun {a} ha => by
    have e : a = uOf hW ⟨a.val - 1, ha⟩ := Units.ext (by rw [uOf_val']; simp)
    change (a⁻¹ : GL (Fin n) ℂ).val - 1 ∈ nilrad W₁ W₂
    rw [e, uOf_inv_val]
    simp only [uOf_val', add_sub_cancel_left]
    rw [show (1 - (a.val - 1) + (a.val - 1) * (a.val - 1) - 1 : Matrix (Fin n) (Fin n) ℂ) =
        -(a.val - 1) + (a.val - 1) * (a.val - 1) by abel]
    exact (nilrad W₁ W₂).add_mem ((nilrad W₁ W₂).neg_mem ha) (GlobalTheory.CompanionTheory.LocVan.nil_mul_mem hW ha ha)

theorem mem_uniRad (hW : W₁ ≤ W₂) (g : GL (Fin n) ℂ) : g ∈ uniRad hW ↔ g.val - 1 ∈ nilrad W₁ W₂ := Iff.rfl

theorem uOf_mem (hW : W₁ ≤ W₂) (X : nilrad W₁ W₂) : uOf hW X ∈ uniRad hW := by
  rw [mem_uniRad, uOf_val']
  simpa using X.2

theorem mulVec_mem_uniRad (hW : W₁ ≤ W₂) {g : GL (Fin n) ℂ} (hg : g ∈ uniRad hW) :
    (∀ y ∈ W₁, g.val *ᵥ y ∈ W₁) ∧ ∀ y ∈ W₂, g.val *ᵥ y ∈ W₂ := by
  have e : ∀ y, g.val *ᵥ y = y + (g.val - 1) *ᵥ y := fun y => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  exact ⟨fun y hy => by rw [e, hg.2.2 y hy, add_zero]; exact hy,
    fun y hy => by rw [e]; exact W₂.add_mem hy (hg.1 y)⟩

theorem uniRad_le (hW : W₁ ≤ W₂) : uniRad hW ≤ flagStab W₁ W₂ := fun g hg =>
  ⟨img_eq_of_mapsTo g W₁ (mulVec_mem_uniRad hW hg).1 (mulVec_mem_uniRad hW ((uniRad hW).inv_mem hg)).1,
   img_eq_of_mapsTo g W₂ (mulVec_mem_uniRad hW hg).2 (mulVec_mem_uniRad hW ((uniRad hW).inv_mem hg)).2⟩

instance uniRad_normal (hW : W₁ ≤ W₂) : ((uniRad hW).subgroupOf (flagStab W₁ W₂)).Normal := ⟨fun u hu q => by
  rw [Subgroup.mem_subgroupOf, mem_uniRad] at hu ⊢
  have h := GlobalTheory.CompanionTheory.LocVan.conj_mem q.1 hu
  have h₁ : img q.1 W₁ = W₁ := q.2.1
  have h₂ : img q.1 W₂ = W₂ := q.2.2
  rw [h₁, h₂] at h
  have hid : q.1.val * (q.1⁻¹ : GL (Fin n) ℂ).val = 1 := Units.mul_inv _
  have e : (((q * u * q⁻¹ : flagStab W₁ W₂) : GL (Fin n) ℂ)).val - 1 =
      q.1.val * ((u : GL (Fin n) ℂ).val - 1) * (q.1⁻¹ : GL (Fin n) ℂ).val := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_sub, sub_mul, mul_one, hid]
  rw [e]
  exact h⟩

theorem isClosed_stab (A : Submodule ℂ (Fin n → ℂ)) : IsClosed {g : GL (Fin n) ℂ | img g A = A} := by
  have hA : IsClosed (A : Set (Fin n → ℂ)) := Submodule.closed_of_finiteDimensional A
  have e : {g : GL (Fin n) ℂ | img g A = A} =
      (⋂ y ∈ A, (fun g : GL (Fin n) ℂ => g.val *ᵥ y) ⁻¹' (A : Set (Fin n → ℂ))) ∩
      ⋂ y ∈ A, (fun g : GL (Fin n) ℂ => (g⁻¹ : GL (Fin n) ℂ).val *ᵥ y) ⁻¹' (A : Set (Fin n → ℂ)) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun h => ⟨fun y hy => mulVec_mem_of_img g h hy, fun y hy => inv_mulVec_mem_of_img g h hy⟩,
      fun h => img_eq_of_mapsTo g A h.1 h.2⟩
  rw [e]
  refine IsClosed.inter (isClosed_biInter fun y _ => hA.preimage ?_) (isClosed_biInter fun y _ => hA.preimage ?_)
  · exact Units.continuous_val.matrix_mulVec continuous_const
  · exact (Units.continuous_val.comp continuous_inv).matrix_mulVec continuous_const

theorem isClosed_flagStab (A B : Submodule ℂ (Fin n → ℂ)) :
    IsClosed (flagStab A B : Set (GL (Fin n) ℂ)) :=
  (isClosed_stab A).inter (isClosed_stab B)

theorem isClosed_radQ (hW : W₁ ≤ W₂) :
    IsClosed (((uniRad hW).subgroupOf (flagStab W₁ W₂) : Subgroup (flagStab W₁ W₂)) : Set (flagStab W₁ W₂)) := by
  have h : Continuous fun q : flagStab W₁ W₂ => (q : GL (Fin n) ℂ).val - 1 :=
    (Units.continuous_val.comp continuous_subtype_val).sub continuous_const
  exact (GlobalTheory.CompanionTheory.LocVan.isClosed_nilrad W₁ W₂).preimage h

def radHomeo (hW : W₁ ≤ W₂) : nilrad W₁ W₂ ≃ₜ (uniRad hW).subgroupOf (flagStab W₁ W₂) where
  toFun X := ⟨⟨uOf hW X, uniRad_le hW (uOf_mem hW X)⟩, Subgroup.mem_subgroupOf.2 (uOf_mem hW X)⟩
  invFun u := ⟨(u : flagStab W₁ W₂).1.val - 1, Subgroup.mem_subgroupOf.1 u.2⟩
  left_inv X := Subtype.ext (by simp [uOf_val'])
  right_inv u := Subtype.ext (Subtype.ext (Units.ext (by simp [uOf_val'])))
  continuous_toFun := by
    have h : Continuous (uOf hW) := by
      have : uOf hW = GlobalTheory.CompanionTheory.LocVan.uOf := funext (uOf_eq hW)
      rw [this]; exact GlobalTheory.CompanionTheory.LocVan.continuous_uOf
    exact (h.subtype_mk _).subtype_mk _
  continuous_invFun := Continuous.subtype_mk
    ((Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub continuous_const) _

theorem radHomeo_coe (hW : W₁ ≤ W₂) (X : nilrad W₁ W₂) :
    (((radHomeo hW X : (uniRad hW).subgroupOf (flagStab W₁ W₂)) : flagStab W₁ W₂) : GL (Fin n) ℂ) = uOf hW X := rfl

theorem map_nmul [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)]
    (hW : W₁ ≤ W₂) (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure] (A : nilrad W₁ W₂) :
    Measure.map (GlobalTheory.CompanionTheory.LocVan.nmul hW A) ν = ν := by
  let P : nilrad W₁ W₂ → nilrad W₁ W₂ := fun X => ⟨A.1 * X.1, GlobalTheory.CompanionTheory.LocVan.nil_mul_mem hW A.2 X.2⟩
  have hPc : Continuous P :=
    Continuous.subtype_mk (continuous_const.matrix_mul continuous_subtype_val) _
  have hsh : Measure.map (fun X => X + P X) ν = ν :=
    GlobalTheory.CompanionTheory.NilChangeVar.map_shear ν (GlobalTheory.CompanionTheory.NilChangeVar.nilrad2 W₁ W₂) P hPc
      (fun X => GlobalTheory.CompanionTheory.NilChangeVar.nil_mul_mem A.2 X.2)
      (fun X Y hY => Subtype.ext (by
        change A.1 * (X.1 + Y.1) = A.1 * X.1
        rw [mul_add, GlobalTheory.CompanionTheory.NilChangeVar.nil_mul_two A.2 hY.1, add_zero]))
  have hf : GlobalTheory.CompanionTheory.LocVan.nmul hW A = (fun X => X + A) ∘ fun X => X + P X := by
    funext X
    refine Subtype.ext ?_
    change A.1 + X.1 + A.1 * X.1 = X.1 + A.1 * X.1 + A.1
    abel
  have hm : Measurable fun X : nilrad W₁ W₂ => X + P X := (continuous_id.add hPc).measurable
  rw [hf, ← Measure.map_map (measurable_add_const A) hm, hsh]
  exact map_add_right_eq_self ν A

theorem radHomeo_nmul (hW : W₁ ≤ W₂) (A X : nilrad W₁ W₂) :
    radHomeo hW (GlobalTheory.CompanionTheory.LocVan.nmul hW A X) = radHomeo hW A * radHomeo hW X :=
  Subtype.ext (Subtype.ext (Units.ext (by
    change 1 + (A.1 + X.1 + A.1 * X.1) = (1 + A.1) * (1 + X.1)
    noncomm_ring)))

theorem isHaar_radHomeo [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)]
    (hW : W₁ ≤ W₂) (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure] :
    (ν.map (radHomeo hW)).IsHaarMeasure := by
  have hm := (radHomeo hW).measurable
  haveI : IsFiniteMeasureOnCompacts (ν.map (radHomeo hW)) := ⟨fun K hK => by
    rw [(radHomeo hW).measurableEmbedding.map_apply]
    exact ((radHomeo hW).isCompact_preimage.2 hK).measure_lt_top⟩
  haveI : (ν.map (radHomeo hW)).IsOpenPosMeasure :=
    (radHomeo hW).continuous.isOpenPosMeasure_map (radHomeo hW).surjective
  haveI : (ν.map (radHomeo hW)).IsMulLeftInvariant := ⟨fun a => by
    obtain ⟨A, rfl⟩ := (radHomeo hW).surjective a
    have hc : (fun x => radHomeo hW A * x) ∘ (radHomeo hW) = (radHomeo hW) ∘ GlobalTheory.CompanionTheory.LocVan.nmul hW A :=
      funext fun X => (radHomeo_nmul hW A X).symm
    have hnm : Measurable (GlobalTheory.CompanionTheory.LocVan.nmul hW A) := by
      have : Continuous (GlobalTheory.CompanionTheory.LocVan.nmul hW A) := Continuous.subtype_mk
        ((continuous_const.add continuous_subtype_val).add
          (continuous_const.matrix_mul continuous_subtype_val)) _
      exact this.measurable
    rw [Measure.map_map (measurable_const_mul _) hm, hc, ← Measure.map_map hm hnm, map_nmul hW ν A]⟩
  exact ⟨⟩

end Radical

end GlobalTheory.CompanionTheory.QuotVan
end

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotVan

theorem quotVanish : QuotVanish := by
  intro n _ _ μ _ d μT _ W₁ W₂ hW _ _ ν _ F hs h₁ h₂ hF hFT hFK h0
  haveI := GlobalTheory.CompanionTheory.LocVan.locallyCompact_GL n
  haveI := GlobalTheory.CompanionTheory.LocVan.secondCountable_GL n
  haveI := isMulRightInvariant_GL n μ
  haveI : SigmaFinite μT := GlobalTheory.CompanionTheory.LocVan.sigmaFinite_twCent d μT
  haveI : μT.IsInvInvariant := GlobalTheory.CompanionTheory.LocVan.invInvariant_twCent d μT fun a ha b hb => twCent_comm hs ha hb
  have hσ : ∀ x : ℂ, starRingEnd ℂ (starRingEnd ℂ x) = x := fun x => by simp
  have g₁ : img (d * thetaR (starRingEnd ℂ) n d) W₁ = W₁ := by
    rw [← GlobalTheory.CompanionTheory.FlagCent.perpD_perpD _ hσ, h₁, h₂]
  have g₂ : img (d * thetaR (starRingEnd ℂ) n d) W₂ = W₂ := by
    rw [← GlobalTheory.CompanionTheory.FlagCent.perpD_perpD _ hσ, h₂, h₁]
  obtain ⟨V₂, V₃, c₁, d₁, c₂, d₂, s₂, s₃⟩ := exists_levi_spaces _ hs hW g₁ g₂
  haveI := isHaar_radHomeo hW ν
  refine absVanish μ (flagStab W₁ W₂) (uK n) (isClosed_flagStab W₁ W₂) (isCompact_uK n) ?_
    ((uniRad hW).subgroupOf (flagStab W₁ W₂)) ((flagStab V₂ V₃).subgroupOf (flagStab W₁ W₂))
    (isClosed_radQ hW) ((isClosed_flagStab V₂ V₃).preimage continuous_subtype_val) ?_ ?_
    (ν.map (radHomeo hW)) (twCent (thetaR (starRingEnd ℂ) n) d) ?_ μT F hF hFT
    (fun k hk x => hFK x k hk) ?_
  · intro g
    obtain ⟨q, hq, k, hk, e⟩ := GlobalTheory.CompanionTheory.IwaDecomp.iwaFlag n W₁ W₂ hW g
    exact ⟨q, hq, k, hk, e⟩
  · intro q
    obtain ⟨u, m, e, hu, m₁, m₂, m₃, m₄⟩ := levi_decomp c₁ d₁ c₂ d₂ q.1 q.2.1 q.2.2
    exact ⟨⟨u, uniRad_le hW hu⟩, Subgroup.mem_subgroupOf.2 hu, ⟨m, m₁, m₂⟩,
      Subgroup.mem_subgroupOf.2 ⟨m₃, m₄⟩, Subtype.ext e⟩
  · refine eq_bot_iff.2 fun x hx => ?_
    have hN := Subgroup.mem_subgroupOf.1 hx.1
    have hM := Subgroup.mem_subgroupOf.1 hx.2
    exact Subgroup.mem_bot.2 (Subtype.ext (levi_inf c₁ d₁ c₂ d₂ x.1 hN hM.1 hM.2))
  · intro t ht
    have hc := GlobalTheory.CompanionTheory.FlagCent.commute_norm (starRingEnd ℂ) hσ ht
    obtain ⟨t₁, t₂⟩ := GlobalTheory.CompanionTheory.FlagCent.twCent_preserves_flag (starRingEnd ℂ) hσ d hs W₁ W₂ h₁ h₂ ht
    exact ⟨⟨t₁, t₂⟩, Subgroup.mem_subgroupOf.2
      ⟨GlobalTheory.CompanionTheory.FlagCent.img_eq_of_commute _ t hs hc V₂ s₂, GlobalTheory.CompanionTheory.FlagCent.img_eq_of_commute _ t hs hc V₃ s₃⟩⟩
  · intro x
    obtain ⟨q, hq, k, hk, rfl⟩ := GlobalTheory.CompanionTheory.IwaDecomp.iwaFlag n W₁ W₂ hW x
    rw [(radHomeo hW).measurableEmbedding.integral_map]
    have e : ∀ X, F ((((radHomeo hW X : (uniRad hW).subgroupOf (flagStab W₁ W₂)) : flagStab W₁ W₂) :
        GL (Fin n) ℂ) * (q * k)) = F (uOf hW X * q) := fun X => by
      rw [radHomeo_coe, ← mul_assoc, hFK _ k hk]
    simp only [e]
    exact h0 q hq

end GlobalTheory.CompanionTheory.QuotVan
end
