import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsAtScale
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RValuePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdScalB

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing

section HrelGen

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem hr_secScal_sval {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have hc : LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k))
      (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e
  have e := H _ _ hc
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  refine ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans ?_)
  exact (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top hm _) (gs_res r z _ hm _))

theorem hr_gs_zero (f : Z ⟶ Y) (z : Z) (U : Y.Opens) : gs f z U 0 = 0 := by
  unfold gs
  split_ifs <;> simp

end HrelGen

section HrelInj

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))

theorem hr_prB_app_injective (W : D.toPre.P.A.left.Opens) :
    Function.Injective ((DegPre.prB D.toPre (FractionRing V)).left.app W).hom := by
  have : IsDominant (DegPre.jFR (R := V) (FractionRing V)) := GC.isDominant_jFR _
  have : IsSchemeTheoreticallyDominant (DegPre.jFR (R := V) (FractionRing V)) := .of_isDominant _
  have : Smooth D.toPre.P.A.hom := D.toPre.P.isAb.smooth
  have hfst : Function.Injective ((pullback.fst D.toPre.P.A.hom (DegPre.jFR (R := V) (FractionRing V))).app W).hom :=
    Scheme.Hom.app_injective _ W
  have e : (DegPre.prB D.toPre (FractionRing V)).left =
      (pullbackSymmetry (DegPre.jFR (R := V) (FractionRing V)) D.toPre.P.A.hom).hom ≫
        pullback.fst D.toPre.P.A.hom (DegPre.jFR (R := V) (FractionRing V)) :=
    (pullbackSymmetry_hom_comp_fst _ _).symm
  rw [e, Scheme.Hom.comp_app]
  have : IsIso ((pullbackSymmetry (DegPre.jFR (R := V) (FractionRing V)) D.toPre.P.A.hom).hom.app
      ((pullback.fst D.toPre.P.A.hom (DegPre.jFR (R := V) (FractionRing V))) ⁻¹ᵁ W)) := inferInstance
  have hiso := (ConcreteCategory.bijective_of_isIso ((pullbackSymmetry (DegPre.jFR (R := V) (FractionRing V))
    D.toPre.P.A.hom).hom.app ((pullback.fst D.toPre.P.A.hom (DegPre.jFR (R := V) (FractionRing V))) ⁻¹ᵁ W))).1
  exact hiso.comp hfst

end HrelInj

section HrelForm

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem hr_form (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X) :
    FormEq (Sum.elim ![𝟙 D.toPre.P.A.left, (oa.onB.act a).left]
        (fun m => (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left ≫
          rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a) m))
      (Sum.elim ![((k * N : ℕ) : ℤ), -(k : ℤ)] rosatiε)
      (Sum.elim (D.toPre.famφB (star a • χ)) (fun i => (oa.onB.act a).left ≫ D.toPre.famφB χ i)) (pullε k N) := by
  intro U _ h
  set p : D.toPre.P.A ⟶ D.toPre.P.A := toUnit D.toPre.P.A ≫ D.toPre.c χ with hp
  set f := oa.onB.act (star a) with hf
  set g := oa.onB.act a with hg
  have hcl : SectionScalarValuation.cQ D.toPre D.toPre.P.A (star a • χ) = p ≫ f := by
    simp only [SectionScalarValuation.cQ, oa.c_lin, hp, hf, Category.assoc]
  have p₃ := SectionScalarValuation.prod_famB D.toPre (𝟙 _) (star a • χ) (k * N) h
  have p₄ := SectionScalarValuation.prod_famB D.toPre g χ k h
  have e₃ : ∀ i, Over.Hom.left (𝟙 D.toPre.P.A) ≫ D.toPre.famφB (star a • χ) i = D.toPre.famφB (star a • χ) i :=
    fun i => by simp
  simp only [e₃] at p₃
  rw [hcl, Over.id_left] at p₃
  have hcq : SectionScalarValuation.cQ D.toPre D.toPre.P.A χ = p := rfl
  rw [hcq] at p₄
  have i0 : (lift p (𝟙 D.toPre.P.A)).left ≫ (padd D.toPre.P.A (fst D.toPre.P.A D.toPre.P.A ≫ f) (snd _ _)).left =
      ((p ≫ f) * 𝟙 D.toPre.P.A).left := by
    rw [← Over.comp_left]; congr 1
    simp only [padd, comp_lift_assoc, lift_fst_assoc, lift_snd]; rfl
  have i1 : (lift p (𝟙 D.toPre.P.A)).left ≫ (fst D.toPre.P.A D.toPre.P.A ≫ f).left = (p ≫ f).left := by
    rw [← Over.comp_left, lift_fst_assoc]
  have i2 : (lift p (𝟙 D.toPre.P.A)).left ≫ (snd D.toPre.P.A D.toPre.P.A).left = 𝟙 D.toPre.P.A.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have i3 : (lift p (𝟙 D.toPre.P.A)).left ≫ (padd D.toPre.P.A (fst D.toPre.P.A D.toPre.P.A) (snd _ _ ≫ g)).left =
      (p * g).left := by
    rw [← Over.comp_left]; congr 1
    simp only [padd, comp_lift_assoc, lift_fst, lift_snd_assoc, Category.id_comp]; rfl
  have i4 : (lift p (𝟙 D.toPre.P.A)).left ≫ (fst D.toPre.P.A D.toPre.P.A).left = p.left := by
    rw [← Over.comp_left, lift_fst]
  have i5 : (lift p (𝟙 D.toPre.P.A)).left ≫ (snd D.toPre.P.A D.toPre.P.A ≫ g).left = g.left := by
    rw [← Over.comp_left, lift_snd_assoc, Category.id_comp]
  have q₁ : 𝟙 D.toPre.P.A * (p ≫ f) = (p ≫ f) * 𝟙 D.toPre.P.A := mul_comm _ _
  have q₂ : g * p = p * g := mul_comm _ _
  rw [q₁] at p₃
  rw [q₂] at p₄
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, pullε]
  rw [p₃, SectionScalarValuation.prod_neg' _ _ p₄]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, rosatiφ, rosatiε,
    Matrix.cons_val_one, Matrix.head_cons, i0, i1, i2, i3, i4, i5]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
  push_cast
  module

end HrelForm

section HrelMain

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable (D : DegData V (maximalIdeal V)) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem hrel_integral_pf (hGF : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (N : ℕ) (hN : a * star a = (N : O))
    (hN1 : 1 ≤ N) (k : ℕ)
    (X : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, (oa.onB.act a).left]
      ![((k * N : ℕ) : ℤ), -(k : ℤ)])) (hX : X.IsGen)
    (hXn : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (eSec D.toPre.P.A))
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (k * (N - 1))))
    (uR : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (huR : uR.IsGen)
    (huR0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uR (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (F : Fam D.toPre (FractionRing V) k) (F'' : Fam D.toPre (FractionRing V) (k * N))
    (hPA : PullAl D (FractionRing V) oa a k N F F'') (lam : V)
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (f'' : ∀ α : D.toPre.X, D.toPre.SecB (k * N) α)
    (hf : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) (F.s α)
      (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing V)).left
      (scal (DegPre.BF D.toPre (FractionRing V)).hom lam))
    (hf'' : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε (k * N)) (F''.s α)
      (D.toPre.famφB α) (DegPre.famε (k * N)) (f'' α) (DegPre.prB D.toPre (FractionRing V)).left
      (scal (DegPre.BF D.toPre (FractionRing V)).hom lam)) :
    (∀ χ, ∃ u : LB.Gen (LB.LinComb D.toPre.P.L
        (Sum.elim (D.toPre.famφB (star a • χ)) (fun i => (oa.onB.act a).left ≫ D.toPre.famφB χ i)) (pullε k N)),
      u.IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ u (LB.mulGen D.toPre.P.L _ _ _ _ X
        (LB.pullGen D.toPre.P.L _ _ uR (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left)) ∧
      GeneratorPullback.SecRel D.toPre.P.L (D.toPre.famφB (star a • χ)) (DegPre.famε (k * N))
        (f'' (star a • χ)) (D.toPre.famφB χ) (DegPre.famε k) (f χ) (oa.onB.act a).left
        (Sum.elim (D.toPre.famφB (star a • χ)) (fun i => (oa.onB.act a).left ≫ D.toPre.famφB χ i)) (pullε k N) u) ∧
    ∀ β, (∀ χ, β ≠ star a • χ) → ∀ j, (f'' β).f j = 0 := by
  classical
  have hL := D.toPre.P.isLB

  have hΛ : ∀ {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D.toPre (FractionRing V)).left) (g : (DegPre.BF D.toPre (FractionRing V)).left ⟶ (DegPre.BF D.toPre (FractionRing V)).left),
      g ≫ (DegPre.BF D.toPre (FractionRing V)).hom = (DegPre.BF D.toPre (FractionRing V)).hom → ∀ z : Z,
      gs (r ≫ g) z ⊤ (scal (DegPre.BF D.toPre (FractionRing V)).hom lam) =
        gs r z ⊤ (scal (DegPre.BF D.toPre (FractionRing V)).hom lam) := fun r g hg z => by
    rw [ps_gs_scal (DegPre.BF D.toPre (FractionRing V)).hom (r ≫ g) z lam,
      ps_gs_scal (DegPre.BF D.toPre (FractionRing V)).hom r z lam, Category.assoc, hg]
  have haF : (aF D (FractionRing V) oa a).left ≫ (DegPre.BF D.toPre (FractionRing V)).hom =
      (DegPre.BF D.toPre (FractionRing V)).hom := Over.w _
  have haFB : (aF D (FractionRing V) oa a).left ≫ (DegPre.prB D.toPre (FractionRing V)).left =
      (DegPre.prB D.toPre (FractionRing V)).left ≫ (oa.onB.act a).left := by
    rw [← Over.comp_left, aF_prB, Over.comp_left]

  have hext : ∀ {β : D.toPre.X} {m : ℕ} (s s' : D.toPre.SecB m β),
      (∀ (y : (DegPre.BF D.toPre (FractionRing V)).left) (J : ((DegPre.BF D.toPre (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
        Good D.toPre.P.L y J → sval s (DegPre.prB D.toPre (FractionRing V)).left y J =
          sval s' (DegPre.prB D.toPre (FractionRing V)).left y J) → ∀ j, s.f j = s'.f j := by
    intro β m s s' hs j
    apply hr_prB_app_injective D
    refine fn_ext fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre (FractionRing V)).left ⟶ D.toPre.P.A.left => Geo.Tor.exists_chart hL (ψ y)
    have hIy : Good D.toPre.P.L y I := hI
    have hm : (DegPre.prB D.toPre (FractionRing V)).left y ∈ LB.wchart D.toPre.P.L (D.toPre.famφB β) j := hy
    have m2 := hIy.mem (D.toPre.famφB β) (DegPre.prB D.toPre (FractionRing V)).left
    have e1 := gs_pull (𝟙 _) (DegPre.prB D.toPre (FractionRing V)).left y _ hm (s.f j)
    have e2 := gs_pull (𝟙 _) (DegPre.prB D.toPre (FractionRing V)).left y _ hm (s'.f j)
    rw [Category.id_comp] at e1 e2
    exact e1.trans ((sec_trans s _ y hm m2).trans ((congrArg _ (hs y I hIy)).trans
      ((sec_trans s' _ y hm m2).symm.trans e2.symm)))
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, vu⟩ := exists_gen hL (hr_form oa a k N χ)
      (LB.mulGen D.toPre.P.L _ _ _ _ X (LB.pullGen D.toPre.P.L _ _ uR
        (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left))
      (mulGen_isGen _ _ _ _ _ _ _ hX (pullGen_isGen _ _ _ _ huR _))
    refine ⟨u, hu, corr_of_val hL fun y J hJ => vu _ (𝟙 _) y J hJ, ?_⟩
    obtain ⟨uF, huF, hnF, hrelF⟩ := hPA.1 χ
    have hformK : FormEq (fun m => (DegPre.prB D.toPre (FractionRing V)).left ≫
        Sum.elim (D.toPre.famφB (star a • χ)) (fun i => (oa.onB.act a).left ≫ D.toPre.famφB χ i) m) (pullε k N)
        (pullφ D (FractionRing V) oa a χ) (pullε k N) := fun U _ h =>
      Finset.prod_congr rfl fun m _ => by
        rcases m with i | i
        · simp only [Sum.elim_inl, pullφ, GC.famφ_eq]
        · have hm : (aF D (FractionRing V) oa a).left ≫ ((DegPre.prB D.toPre (FractionRing V)).left ≫ D.toPre.famφB χ i) =
              (DegPre.prB D.toPre (FractionRing V)).left ≫ ((oa.onB.act a).left ≫ D.toPre.famφB χ i) := by
            rw [← Category.assoc, haFB, Category.assoc]
          simp only [Sum.elim_inr, pullφ, GC.famφ_eq, hm]
    obtain ⟨u', hu', vu'⟩ := exists_gen hL hformK
      (LB.pullGen D.toPre.P.L _ _ u (DegPre.prB D.toPre (FractionRing V)).left) (pullGen_isGen _ _ _ _ hu _)
    have hliftB : (lift (cPB D (FractionRing V) χ) (DegPre.prB D.toPre (FractionRing V))).left =
        (DegPre.prB D.toPre (FractionRing V)).left ≫ (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
    have huF_eq := gen_unique hL (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left (DegPre.zF D.toPre (FractionRing V)).left
      GC.zF_fst (surj_appTop D.toPre (FractionRing V) hGF) huF hu' (fun y J hJ => by
        have a1 := val_corr hJ hnF (𝟙 _)
        rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at a1
        rw [a1, vu' _ _ y J hJ, val_pull hJ, vu _ _ y J hJ, val_mul hJ, val_pull hJ]
        have a2 := val_corr hJ (rFac_zero_pf (F := FractionRing V) oa a uR huR huR0 χ) (𝟙 _)
        rw [val_pull hJ, val_one, Category.id_comp] at a2
        unfold rFac at a2
        rw [val_pull hJ, hliftB, ← Category.assoc] at a2
        rw [a2]
        refine Eq.trans ?_ (_root_.mul_one _).symm
        have a3 := val_corr hJ hXn (DegPre.jFR (R := V) (FractionRing V))
        rw [val_pull hJ] at a3
        have a4 : val X ((DegPre.zF D.toPre (FractionRing V)).left ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J =
            val X (DegPre.jFR (R := V) (FractionRing V) ≫ eSec D.toPre.P.A) y J :=
          congrArg (fun r => val X r y J) (GC.zF_prB D.toPre (FractionRing V))
        rw [a4, a3]
        refine (map_pow _ _ _).trans ((congrArg (· ^ _) ?_).trans (map_pow _ _ _).symm)
        show val D.toPre.rigK (jFK (R := V) (FractionRing V)) y J = val D.toPre.rig (DegPre.jFR (R := V) (FractionRing V)) y J
        rw [DegPre.rigK, val_pull hJ, GC.toUnit_TK_left])
    have hcanc : FormEq (Sum.elim (fun i => (oa.onB.act a).left ≫ D.toPre.famφB χ i)
        (Sum.elim (D.toPre.famφB (star a • χ)) (fun i => (oa.onB.act a).left ≫ D.toPre.famφB χ i)))
        (Sum.elim (DegPre.famε k) (pullε k N)) (D.toPre.famφB (star a • χ)) (DegPre.famε (k * N)) := fun U _ h => by
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, pullε, zpow_neg, Finset.prod_inv_distrib]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
    obtain ⟨S2, hS2⟩ := exists_sec hL hcanc (pullMulSec (f χ) (oa.onB.act a).left u hu)
    have hΛaF : ∀ y : (DegPre.BF D.toPre (FractionRing V)).left,
        gs (aF D (FractionRing V) oa a).left y ⊤ (scal (DegPre.BF D.toPre (FractionRing V)).hom lam) =
        gs (𝟙 _) y ⊤ (scal (DegPre.BF D.toPre (FractionRing V)).hom lam) := fun y => by
      have e := hΛ (𝟙 _) _ haF y
      rwa [Category.id_comp] at e
    have hS : ∀ j, (f'' (star a • χ)).f j = S2.f j := hext _ _ fun y J hJ => by
      have e1 := hr_secScal_sval (hf'' (star a • χ)) (𝟙 _) y hJ
      have e2 := hr_secScal_sval (hf χ) (aF D (FractionRing V) oa a).left y hJ
      have e3 := (secRel_iff hL _ _ _ _ _ _ _ _ _ uF).1 hrelF _ (𝟙 _) y J hJ
      have e4 := hS2 _ (DegPre.prB D.toPre (FractionRing V)).left y J hJ
      rw [sval_pullMulSec _ _ _ hu _ y hJ, ← haFB, e2, hΛaF] at e4
      have e5 := congrArg Units.val (huF_eq _ (𝟙 _) y J hJ)
      have e6 := vu' _ (𝟙 _) y J hJ
      rw [val_pull hJ, Category.id_comp] at e6
      rw [Category.id_comp] at e1 e3
      rw [e1, e3, e4, e5, e6]
      ring
    refine (secRel_iff hL _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
    have e := hS2 _ (𝟙 _) y J hJ
    rw [sval_pullMulSec _ _ _ hu _ y hJ] at e
    exact (congrArg (gs (𝟙 _) y _) (hS _)).trans e
  · have h0 : ∀ j', ((F''.s β).f j') = 0 := hPA.2 β hβ
    apply hr_prB_app_injective D
    rw [map_zero]
    refine fn_ext fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre (FractionRing V)).left ⟶ D.toPre.P.A.left => Geo.Tor.exists_chart hL (ψ y)
    have hIy : Good D.toPre.P.L y I := hI
    have hm : (DegPre.prB D.toPre (FractionRing V)).left y ∈ LB.wchart D.toPre.P.L (D.toPre.famφB β) j := hy
    have m2 := hIy.mem (D.toPre.famφB β) (DegPre.prB D.toPre (FractionRing V)).left
    have e1 := gs_pull (𝟙 _) (DegPre.prB D.toPre (FractionRing V)).left y _ hm ((f'' β).f j)
    rw [Category.id_comp] at e1
    have e := hr_secScal_sval (hf'' β) (𝟙 _) y hIy
    rw [Category.id_comp] at e
    have hz : sval (F''.s β) (𝟙 _) y I = 0 :=
      (congrArg (gs (𝟙 _) y _) (h0 _)).trans (hr_gs_zero _ _ _)
    refine e1.trans ((sec_trans (f'' β) _ y hm m2).trans ?_)
    show _ * sval (f'' β) (DegPre.prB D.toPre (FractionRing V)).left y I = _
    rw [e, hz, mul_zero, mul_zero]
    exact (hr_gs_zero _ _ _).symm

end HrelMain

end ReciprocityTheory.ChartRestriction.G.DVR
