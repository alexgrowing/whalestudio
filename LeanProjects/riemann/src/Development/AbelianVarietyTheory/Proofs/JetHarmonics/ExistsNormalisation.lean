import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftFrobenius

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPull

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem trPt_aF (oa : D.toPre.OAct O) (a : O) (b b' : TF (R := V) F ⟶ D.toPre.P.A)
    (hb : b' = b ≫ oa.onB.act a) :
    DegPre.trPt D.toPre F b ≫ aF D F oa a = aF D F oa a ≫ DegPre.trPt D.toPre F b' := by
  have := oa.onB.hom a
  have ap : aF D F oa a ≫ DegPre.prB D.toPre F = DegPre.prB D.toPre F ≫ oa.onB.act a := by
    simp [aF, DegPre.prB]
  have af : aF D F oa a ≫ fst (TF (R := V) F) D.toPre.P.A = fst _ _ := lift_fst _ _
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, af, tr_fst, Category.assoc, tr_fst, af]
  · show (DegPre.trPt D.toPre F b ≫ aF D F oa a) ≫ DegPre.prB D.toPre F =
      (aF D F oa a ≫ DegPre.trPt D.toPre F b') ≫ DegPre.prB D.toPre F
    rw [Category.assoc, ap, ← Category.assoc, tr_pr, MonObj.mul_comp, Category.assoc, ← hb,
      Category.assoc, tr_pr, MonObj.comp_mul, ap, ← Category.assoc, af]

theorem gen_eq_of_origin (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (p' : QkPt D.toPre F k)
    (p₁ : QkPt D.toPre F (k * N)) (hy : p₁.y = star a • p'.y) (hb : p'.g.b = p₁.g.b ≫ oa.onB.act a)
    (χ : D.toPre.X)
    (uχ : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))) (huχ : uχ.IsGen)
    (uχz : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a (χ + p'.y)) (pullε k N))) (huχz : uχz.IsGen)
    (Ψ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p'.y χ p'.g.b) (DegPre.deltaε k))) (hΨ : Ψ.IsGen)
    (Φ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p₁.y (star a • χ) p₁.g.b) (DegPre.deltaε (k * N))))
    (hΦ : Φ.IsGen)
    (horig : ∀ y J, Good D.toPre.P.L y J →
      val (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.trPt D.toPre F p₁.g.b).left) Φ)
          (DegPre.zF D.toPre F).left y J =
        val (LB.mulGen D.toPre.P.L _ _ _ _ uχz (LB.pullGen D.toPre.P.L _ _ Ψ (aF D F oa a).left))
          (DegPre.zF D.toPre F).left y J)
    (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z' : Z) (J) (hJ : Good D.toPre.P.L z' J) :
    val uχ (ρ ≫ (DegPre.trPt D.toPre F p₁.g.b).left) z' J * val Φ ρ z' J =
      val uχz ρ z' J * val Ψ (ρ ≫ (aF D F oa a).left) z' J := by
  have e1 : ∀ i, (DegPre.trPt D.toPre F p₁.g.b).left ≫ (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ i =
      (aF D F oa a ≫ DegPre.trPt D.toPre F p'.g.b).left ≫ DegPre.famφ D.toPre F χ i := fun i => by
    rw [← Category.assoc, ← Over.comp_left, trPt_aF oa a p₁.g.b p'.g.b hb]
  have e2 : ∀ i, (aF D F oa a).left ≫ (DegPre.trPt D.toPre F p'.g.b).left ≫ DegPre.famφ D.toPre F χ i =
      (aF D F oa a ≫ DegPre.trPt D.toPre F p'.g.b).left ≫ DegPre.famφ D.toPre F χ i := fun i => by
    rw [← Category.assoc, ← Over.comp_left]
  have e3 : star a • χ + p₁.y = star a • (χ + p'.y) := by rw [hy, smul_add]
  have hF : FormEq (Sum.elim (pullφ D F oa a (χ + p'.y))
      (fun i => (aF D F oa a).left ≫ DegPre.phiφ D.toPre F p'.y χ p'.g.b i)) (Sum.elim (pullε k N) (DegPre.deltaε k))
      (Sum.elim (fun i => (DegPre.trPt D.toPre F p₁.g.b).left ≫ pullφ D F oa a χ i)
        (DegPre.phiφ D.toPre F p₁.y (star a • χ) p₁.g.b)) (Sum.elim (pullε k N) (DegPre.deltaε (k * N))) :=
    fun U _ h => by
      simp only [pullφ, pullε, DegPre.phiφ, DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl,
        Sum.elim_inr, e1, e2, e3]
      simp only [Fin.prod_univ_four]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module
  have key := gen_unique' D.toPre.P.isLB hF (fst (TF (R := V) F) D.toPre.P.A).left (DegPre.zF D.toPre F).left
    (GC.zF_fst (D := D) (F := F)) (surj_appTop D.toPre F hG)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ huχ _) hΦ)
    (mulGen_isGen _ _ _ _ _ _ _ huχz (pullGen_isGen _ _ _ _ hΨ _)) horig Z ρ z' J hJ
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ] at key
  exact key

theorem exists_normalisation (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (hN : 1 ≤ N)
    (b b' : TF (R := V) F ⟶ D.toPre.P.A) (hb : b' = b ≫ oa.onB.act a)
    (w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F b') (DegPre.lineε k))) (hw' : w'.IsGen)
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε k N))) (hu0 : u0.IsGen) :
    ∃ w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F b) (DegPre.lineε (k * N))), w.IsGen ∧
      ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val w' (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left y J)⁻¹ := by
  have := oa.onB.hom a
  have h1 : (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ DegPre.prB D.toPre F = b :=
    CanonicalLiftTraces.zF_tr_pr b
  have h2 : ((DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ aF D F oa a) ≫ DegPre.prB D.toPre F = b' := by
    rw [Category.assoc, show aF D F oa a ≫ DegPre.prB D.toPre F = DegPre.prB D.toPre F ≫ oa.onB.act a by
      simp [aF, DegPre.prB], ← Category.assoc, h1, hb]
  have e2 : ∀ i, (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left ≫ (aF D F oa a).left ≫
      DegPre.famφ D.toPre F 0 i = ((DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b) ≫ aF D F oa a).left ≫
      DegPre.famφ D.toPre F 0 i := fun i => by rw [← Category.assoc, ← Over.comp_left]
  have c0 : cP D.toPre (TF (R := V) F) 0 = 1 := cPoint_zero _
  have p0 : (DegPre.zeroF D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := rfl
  have p1 : jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left :=
    (Category.assoc _ _ _).symm
  have hN' : ((k * (N - 1) : ℕ) : ℤ) = ((k * N : ℕ) : ℤ) - k := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hN]; push_cast; ring
  obtain ⟨w, hw, hv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F b) (ε' := DegPre.lineε (k * N))
    (fun U _ h => by
      simp only [pullφ, pullε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, e2, p1]
      simp only [CanonicalLiftTraces.comp_famφ, h1, h2, Fin.prod_univ_four, Fin.prod_univ_two, Matrix.cons_val,
        DegPre.famε, smul_zero, c0, _root_.mul_one, DegPre.lineφ, DegPre.lineε, p0, hN']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      push_cast
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) w')
      (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F b).left)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (pullGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) _) _) hw')
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hu0 _)))
  refine ⟨w, hw, fun y J hJ => ?_⟩
  rw [hv _ _ y J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ u0, Category.id_comp]

theorem gen_eq_at_origin (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (p' : QkPt D.toPre F k)
    (p₁ : QkPt D.toPre F (k * N)) (hgt : GtAct oa a p₁.g p'.g)
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε k N))) (hu0 : u0.IsGen)
    (hc0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p'.g.b) (DegPre.lineε k)))
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε (k * N))))
    (hwv : ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val w' (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F p₁.g.b).left y J)⁻¹)
    (χ ξ : D.toPre.X)
    (uχ : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))) (huχ : uχ.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (uχz : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a ξ) (pullε k N)))
    (hcz : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχz (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (Ψ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p'.y χ p'.g.b) (DegPre.deltaε k)))
    (hcΨ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ Ψ (DegPre.zF D.toPre F).left)
      (LB.mulGen D.toPre.P.L _ _ _ _ (p'.g.s χ) w'))
    (Φ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p₁.y (star a • χ) p₁.g.b) (DegPre.deltaε (k * N))))
    (hcΦ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ Φ (DegPre.zF D.toPre F).left)
      (LB.mulGen D.toPre.P.L _ _ _ _ (p₁.g.s (star a • χ)) w))
    (y : (TF (R := V) F).left) (J) (hJ : Good D.toPre.P.L y J) :
    val (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.trPt D.toPre F p₁.g.b).left) Φ)
        (DegPre.zF D.toPre F).left y J =
      val (LB.mulGen D.toPre.P.L _ _ _ _ uχz (LB.pullGen D.toPre.P.L _ _ Ψ (aF D F oa a).left))
        (DegPre.zF D.toPre F).left y J := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hros := oa.onB.rosati (star a)
  rw [star_star] at hros
  obtain ⟨r, hr, hr0⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hros
  have hl : ((DegPre.zF D.toPre F).left ≫ (DegPre.trPt D.toPre F p₁.g.b).left) ≫
      (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left = (lift (DegPre.cF D.toPre F χ) p₁.g.b).left := by
    rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_cP, CanonicalLiftTraces.zF_tr_pr]
    rfl
  have e1 := val_corr hJ hcz (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at e1
  have e2 := val_corr hJ hcΨ (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_mul hJ] at e2
  have e3 := val_corr hJ hcΦ (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_mul hJ] at e3
  have e5 := hwv y J hJ
  rw [Over.comp_left] at e5
  have e6 := val_corr hJ (hgt.2 r hr hr0 χ) (𝟙 _)
  rw [val_mul hJ, val_pull hJ, Category.id_comp] at e6
  have e7 : val Ψ ((DegPre.zF D.toPre F).left ≫ (aF D F oa a).left) y J = val Ψ (DegPre.zF D.toPre F).left y J := by
    rw [← Over.comp_left, CanonicalLiftTraces.zF_aF]
  rw [val_mul hJ, val_pull hJ, val_mul hJ, val_pull hJ, e3,
    CanonicalLiftValuation.pull_val_chi hG oa a k N χ uχ huχ hc u0 hu0 hc0 r hr hr0 _ _ y J hJ, val_pull hJ, hl,
    e5, e7, e1, e2, ← e6]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem phiRel_pullAl : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) → ∀ (p' : QkPt D.toPre F k) (p₁ : QkPt D.toPre F (k * N)), GtAct oa a p₁.g p'.g → p₁.y = star a • p'.y → ∀ w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p'.g.b) (DegPre.lineε k)), w'.IsGen → ∃ w₁ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε (k * N))), w₁.IsGen ∧ ∀ (s t : Fam D.toPre F k) (s' t' : Fam D.toPre F (k * N)), PhiRel D.toPre F k p' w' s t → PullAl D F oa a k N s s' → PullAl D F oa a k N t t' → PhiRel D.toPre F (k * N) p₁ w₁ s' t' := by
  intro hL V _ _ _ D F _ _ O _ _ _ oa w0 hw0 a N k hN _ haa p' p₁ hgt hy w' hw'
  have hG := hL.globalFns
  obtain ⟨uΨ, huΨ, -⟩ := hw0
  obtain ⟨u0, hu0, hc0⟩ := exists_pullGen D F D.toPre.P.isLB oa w0 uΨ huΨ a N haa hN k 0
  obtain ⟨w, hw, hwv⟩ := exists_normalisation oa a k N hN p₁.g.b p'.g.b hgt.1 w' hw' u0 hu0
  refine ⟨w, hw, fun s t s' t' hst hs' ht' => ?_⟩
  rw [phiRel_iff hG p₁ w hw s' t']
  intro a' β hβ T ρ z' J hJ
  by_cases ha : ∃ χ, a' = star a • χ
  · obtain ⟨χ, rfl⟩ := ha
    subst hβ
    have e3 : star a • χ + p₁.y = star a • (χ + p'.y) := by rw [hy, smul_add]
    rw [e3]
    obtain ⟨uχz, huχz, hcz, hsz⟩ := ht'.1 (χ + p'.y)
    obtain ⟨uχ, huχ, hc, hs⟩ := hs'.1 χ
    obtain ⟨⟨Ψ, hΨ, hcΨ⟩, -⟩ := gen_phi hG p' w' hw' χ
    obtain ⟨⟨Φ, hΦ, hcΦ⟩, hΦv⟩ := gen_phi hG p₁ w hw (star a • χ)
    have s1 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ uχz).1 hsz _ ρ.left z' J hJ
    have s2 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ Ψ).1 (hst χ Ψ hΨ hcΨ) _
      (ρ.left ≫ (aF D F oa a).left) z' J hJ
    have s3 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ uχ).1 hs _ (ρ ≫ DegPre.trPt D.toPre F p₁.g.b).left z' J hJ
    have pt : (ρ ≫ DegPre.trPt D.toPre F p₁.g.b).left ≫ (aF D F oa a).left =
        (ρ.left ≫ (aF D F oa a).left) ≫ (DegPre.trPt D.toPre F p'.g.b).left := by
      rw [← Over.comp_left, Category.assoc, trPt_aF oa a p₁.g.b p'.g.b hgt.1, ← Category.assoc, Over.comp_left,
        Over.comp_left]
    have eig := gen_eq_of_origin hG oa a k N p' p₁ hy hgt.1 χ uχ huχ uχz huχz Ψ hΨ Φ hΦ
      (fun y J hJ => gen_eq_at_origin hG oa a k N p' p₁ hgt u0 hu0 hc0 w' w hwv χ _ uχ huχ hc uχz hcz Ψ hcΨ
        Φ hcΦ y J hJ) _ ρ.left z' J hJ
    have hΦρ := hΦv Φ hΦ hcΦ T ρ z' J hJ
    have eig' : (val Ψ (ρ.left ≫ (aF D F oa a).left) z' J).val * (val uχz ρ.left z' J).val =
        (val uχ (ρ ≫ DegPre.trPt D.toPre F p₁.g.b).left z' J).val * (val Φ ρ.left z' J).val := by
      rw [← Units.val_mul, ← Units.val_mul, _root_.mul_comm]
      exact congrArg Units.val eig.symm
    rw [s1, s2, s3, pt, ← hΦρ, _root_.mul_assoc, _root_.mul_assoc, eig']
  · have hβn : ∀ χ, β ≠ star a • χ := by
      intro χ h
      apply ha
      refine ⟨χ - p'.y, ?_⟩
      rw [smul_sub, ← h, ← hβ, hy]
      abel
    rw [CanonicalLiftFrobenius.sval_zero _ (ht'.2 β hβn), CanonicalLiftFrobenius.sval_zero _ (hs'.2 a' (fun χ h => ha ⟨χ, h⟩)),
      MulZeroClass.zero_mul]

end GlobalTheory.ThetaPull
