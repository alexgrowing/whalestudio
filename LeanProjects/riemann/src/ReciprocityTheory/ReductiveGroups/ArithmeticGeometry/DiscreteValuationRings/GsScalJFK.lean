import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsValGenHasVal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm

section FE

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem trF_fst (mu : D.toPre.X) :
    (DegPre.trF D.toPre F mu).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left := by
  rw [← Over.comp_left]
  simp [DegPre.trF]

theorem trF_prB (mu : D.toPre.X) :
    (DegPre.trF D.toPre F mu).left ≫ (DegPre.prB D.toPre F).left =
      (DegPre.prB D.toPre F).left ≫ (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  simp only [DegPre.trF, CartesianMonoidalCategory.lift_snd, padd, CategoryTheory.Hom.mul_def, cQ,
    CartesianMonoidalCategory.comp_lift_assoc, Category.comp_id, SemiCartesianMonoidalCategory.comp_toUnit_assoc]

theorem gs_gF_zF (y : (TF (R := V) F).left) (ζ : F) :
    gs (DegPre.zF D.toPre F).left y ⊤ (gF D.toPre F ζ) = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by
  have h := gs_pull (DegPre.zF D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ (by simp)
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ)
  have e : (DegPre.zF D.toPre F).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left]
    simp [DegPre.zF]
  rw [e] at h
  rw [← h]
  rfl

theorem gs_scal_jFK (y : (TF (R := V) F).left) (c : FractionRing V) :
    gs (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y ⊤ (scal (𝟙 _) c) =
      gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (algebraMap (FractionRing V) F c)) := by
  have key : ((jFK (R := V) F).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (algebraMap (FractionRing V) F c) := by
    have := congrArg (fun φ => φ.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing V) F)))
    exact this.symm
  have h := gs_pull (𝟙 (TF (R := V) F).left) (jFK (R := V) F) y ⊤ (by simp)
    ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom c)
  have hs : scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom c := by
    simp [scal]
  erw [hs, ← h]
  exact congrArg (gs (𝟙 (TF (R := V) F).left) y ⊤) key

theorem fe_move (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : IsQ D.toPre ϖ Q) (hv : ValOver ϖ F v) (k : ℕ)
    (mu α : D.toPre.X) (s : Fam D.toPre F k) {r : ℚ} (hs : VGe D F v k α (s.s α) r) :
    VGe D F v k (α + k • mu) (s.s (α + k • mu)) (r + ((k * Q mu + bOf D.toPre Q mu α : ℤ) : ℚ)) := by
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
  have hrel := s.fe mu α u hu hcorr
  have hformB : FormEq (Sum.elim (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i)
      (Sum.elim (D.toPre.famφB (α + k • mu)) (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i)))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) (D.toPre.famφB (α + k • mu)) (DegPre.famε k) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  refine vge_move (trF_fst mu) (trF_prB mu) u hrel eB heB hformB c (fun y J hJ => ?_) ?_ hs
  · rw [hval_u _ _ y J hJ, Category.id_comp]; exact mul_comm _ _
  · exact le_of_eq (hv c₀ _ hc₀).symm

end FE

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
