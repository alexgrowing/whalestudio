import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFibre

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm SectionScalarValuation

section FEGen

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem exists_fe_gen (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : IsQ D.toPre ϖ Q) (k : ℕ)
    (mu α : D.toPre.X) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.deltaφ D.toPre F k α mu) (DegPre.deltaε k)), u.IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
        (DegPre.famMult D.toPre F k mu α) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨Ix, _, φV, εV, e', he', hC, c₀, hc₀, hval⟩ := famMult_data D hϖ hQ k mu α
  obtain ⟨eB, heB, veB⟩ := exists_eB D.toPre k α mu e' he' hC
  have hc0 : c₀ ≠ 0 := ne_zero_of_hasVal hϖ hc₀
  set c : F := algebraMap (FractionRing V) F c₀ with hc
  have hcne : c ≠ 0 := (map_ne_zero _).2 hc0
  let cU : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ :=
    ⟨gF D.toPre F c, gF D.toPre F c⁻¹, by rw [← map_mul, mul_inv_cancel₀ hcne, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hcne, map_one]⟩
  let g0 : LB.Gen (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top cU⟩
  have hg0 : g0.IsGen := fun i j => by
    have hg : (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 := by
      simp [LB.LinComb]; rfl
    calc res _ (g0.s i) = res _ (g0.s j) := (res_res' _ _ cU).trans (res_res' _ _ cU).symm
      _ = _ := by rw [hg, _root_.one_mul]
  have hformU : FormEq (Sum.elim (fun i => (DegPre.prB D.toPre F).left ≫ Sum.elim (D.toPre.famφB (α + k • mu))
        (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i) i) PEmpty.elim)
      (Sum.elim (DegPre.deltaε k) PEmpty.elim) (DegPre.deltaφ D.toPre F k α mu) (DegPre.deltaε k) := fun U _ h => by
    have e0 : ∀ f : PEmpty → U, ∏ i, f i = 1 := fun f => Fintype.prod_empty f
    rw [Fintype.prod_sum_type, e0, _root_.mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases i with i | i
    · simp only [Sum.elim_inl, DegPre.deltaφ, GC.famφ_eq]
    · simp only [Sum.elim_inr, DegPre.deltaφ, GC.famφ_eq]
      rw [← Category.assoc, trF_prB, Category.assoc]
      rfl
  obtain ⟨u, hu, vu⟩ := exists_gen hL hformU
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ eB (DegPre.prB D.toPre F).left) g0)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ heB _) hg0)
  have hval_u : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L z J →
      (val u ρ z J).val = (val eB (ρ ≫ (DegPre.prB D.toPre F).left) z J).val * gs ρ z ⊤ (gF D.toPre F c) := by
    intro Z ρ z J hJ
    rw [vu Z ρ z J hJ, val_mul hJ, val_pull hJ, Units.val_mul]
    congr 1
    have hmem : ρ z ∈ LB.wchart D.toPre.P.L (K := PEmpty) PEmpty.elim (fun k => J (ρ ≫ PEmpty.elim k)) :=
      Set.mem_iInter.2 fun k => k.elim
    exact (congrArg Units.val (gm_res ρ z le_top hmem cU)).trans (gs_unit ρ z ⊤ (by trivial) cU).symm
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have hcorr : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (DegPre.famMult D.toPre F k mu α) := corr_of_val hL fun y J hJ => Units.ext (by
    have C : IsCub (cubV D.toPre.cub (T := TF (R := V) F) y J) := isCub_cubV D.toPre.cub hJ
    have E2 : val eB ((DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left) y J =
        val e' (DegPre.jFR (R := V) F) y J := by
      have E1 := veB (TF (R := V) F) (DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F) y J hJ
      rw [z₂, C.N_one, C.face₂, inv_one, _root_.one_mul, _root_.one_mul] at E1
      have e3 : (1 : TF (R := V) F ⟶ D.toPre.P.A).left ≫ D.toPre.P.A.hom = DegPre.jFR (R := V) F := Over.w _
      rw [e3] at E1
      have e4 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
        rw [← Over.comp_left, z₂]
      rw [e4]; exact E1
    rw [val_pull hJ, Category.id_comp, hval_u _ _ y J hJ, hval F (TF (R := V) F).left (𝟙 (TF (R := V) F).left) y J hJ, E2, gs_gF_zF, gs_scal_jFK,
      Category.id_comp, ← hc]
    exact mul_comm _ _)
  exact ⟨u, hu, hcorr⟩

theorem fam_eq_zero (hϖ : Irreducible ϖ) (G : Fam D.toPre F 1)
    (h0 : ∀ j : Fin 4 → D.toPre.P.L.ι, (G.s 0).f j = 0) :
    ∀ (mu : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι), (G.s mu).f j = 0 := by
  classical
  choose Q hQ using fun χ => QForm.exists_QVal hϖ D χ
  intro mu j
  obtain ⟨u, hu, hc⟩ := exists_fe_gen (F := F) hϖ (Q := Q) hQ 1 mu 0
  have hrel := G.fe mu 0 u hu hc
  have e01 : (0 : D.toPre.X) + 1 • mu = mu := by simp
  rw [e01] at hrel
  have hL := D.toPre.P.isLB
  refine TopCat.Presheaf.section_ext (DegPre.BF D.toPre F).left.sheaf _ _ 0 fun y hy => ?_
  choose ch hch using WeightPf.exists_chart D.toPre.P.L hL
  let j₁ : Fin 4 → D.toPre.P.L.ι := fun k => ch ((DegPre.famφ D.toPre F mu k).base y)
  let j₂ : Fin 4 → D.toPre.P.L.ι := fun k => ch (((DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k).base y)
  let j₃ : Fin 4 ⊕ Fin 4 → D.toPre.P.L.ι := fun k => ch ((DegPre.deltaφ D.toPre F 1 0 mu k).base y)
  have hcoh : LB.Coh D.toPre.P.L (Sum.elim (DegPre.famφ D.toPre F mu)
      (Sum.elim (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k)
        (DegPre.deltaφ D.toPre F 1 0 mu))) (Sum.elim j₁ (Sum.elim j₂ j₃)) := by
    have key : ∀ z, (Sum.elim j₁ (Sum.elim j₂ j₃)) z = ch (((Sum.elim (DegPre.famφ D.toPre F mu)
        (Sum.elim (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k)
          (DegPre.deltaφ D.toPre F 1 0 mu))) z).base y) := by
      rintro (z | z | z) <;> rfl
    intro a b hab
    rw [key a, key b, hab]
  have E := hrel j₁ j₂ j₃ hcoh
  have hy1 : y ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ := Set.mem_iInter.2 fun k => hch _
  have hy2 : y ∈ LB.wchart D.toPre.P.L (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k) j₂ :=
    Set.mem_iInter.2 fun k => hch _
  have hy3 : y ∈ LB.wchart D.toPre.P.L (DegPre.deltaφ D.toPre F 1 0 mu) j₃ := Set.mem_iInter.2 fun k => hch _

  have hz : ((DegPre.BF D.toPre F).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
      LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k) j₂ ⊓
        LB.wchart D.toPre.P.L (DegPre.deltaφ D.toPre F 1 0 mu) j₃ ≤ _)).op).hom ((G.s mu).f j₁) = 0 := by
    erw [E, h0 j₂, map_zero, map_zero, zero_mul]

  let W := LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j ⊓
    (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ ⊓
      LB.wchart D.toPre.P.L (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k) j₂ ⊓
      LB.wchart D.toPre.P.L (DegPre.deltaφ D.toPre F 1 0 mu) j₃)
  have hyW : y ∈ W := ⟨hy, ⟨⟨hy1, hy2⟩, hy3⟩⟩
  have hW1 : W ≤ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j ⊓ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ :=
    le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have hc1 := congrArg (rs hW1) ((G.s mu).compat j j₁)
  have hWz : rs (inf_le_left : W ≤ _) ((G.s mu).f j) = 0 := by
    erw [rs_rs, rs_mul, rs_rs] at hc1
    erw [hc1]
    have := congrArg (rs (inf_le_right : W ≤ _)) hz
    erw [rs_rs] at this
    erw [this]
    exact (congrArg _ (map_zero _)).trans (mul_zero _)
  show (DegPre.BF D.toPre F).left.presheaf.germ _ y hy ((G.s mu).f j) = (DegPre.BF D.toPre F).left.presheaf.germ _ y hy 0
  erw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left : W ≤ _)) y hyW]
  exact (congrArg _ hWz).trans ((map_zero _).trans (map_zero _).symm)

end FEGen

section Local

end Local

end ReciprocityTheory.ChartRestriction.G.DVR.TG
