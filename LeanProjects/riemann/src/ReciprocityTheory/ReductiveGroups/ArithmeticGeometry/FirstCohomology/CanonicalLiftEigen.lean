import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftValuation

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftEigen

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem tr_aF (oa : D.toPre.OAct O) (a : O) (b : TF (R := V) F ⟶ D.toPre.P.A) (z : D.toPre.X)
    (hb : b ≫ oa.onB.act a = cP D.toPre _ (-z)) :
    DegPre.trPt D.toPre F b ≫ aF D F oa a = aF D F oa a ≫ DegPre.trF D.toPre F (-z) := by
  have hmh : IsMonHom (oa.onB.act a) := oa.onB.hom a
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.trPt, aF, DegPre.trF]
  · simp only [DegPre.trPt, aF, DegPre.trF, DegPre.prB, padd, Category.assoc,
      CartesianMonoidalCategory.lift_snd, CartesianMonoidalCategory.comp_lift_assoc,
      CartesianMonoidalCategory.lift_snd_assoc]
    rw [IsMonHom.mul_hom, CartesianMonoidalCategory.lift_map_assoc, Category.assoc, hb]
    unfold cP
    congr 2
    all_goals first | rfl | (apply SemiCartesianMonoidalCategory.toUnit_unique) | simp

theorem eigen_of_origin (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (N : ℕ) (p : QkPt D.toPre F (1 * N))
    (z : D.toPre.X) (hy : p.y = -(star a • z)) (hb : p.g.b ≫ oa.onB.act a = cP D.toPre _ (-z)) (χ : D.toPre.X)
    (uχ : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε 1 N))) (huχ : uχ.IsGen)
    (uχz : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a (χ - z)) (pullε 1 N))) (huχz : uχz.IsGen)
    (fe : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.deltaφ D.toPre F 1 χ (-z)) (DegPre.deltaε 1))) (hfe : fe.IsGen)
    (Φ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p.y (star a • χ) p.g.b) (DegPre.deltaε (1 * N))))
    (hΦ : Φ.IsGen)
    (horig : ∀ y J, Good D.toPre.P.L y J →
      val (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.trPt D.toPre F p.g.b).left) Φ)
          (DegPre.zF D.toPre F).left y J =
        val (LB.mulGen D.toPre.P.L _ _ _ _ uχz (LB.pullGen D.toPre.P.L _ _ fe (aF D F oa a).left))
          (DegPre.zF D.toPre F).left y J)
    (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z' : Z) (J) (hJ : Good D.toPre.P.L z' J) :
    val uχ (ρ ≫ (DegPre.trPt D.toPre F p.g.b).left) z' J * val Φ ρ z' J =
      val uχz ρ z' J * val fe (ρ ≫ (aF D F oa a).left) z' J := by
  have e1 : ∀ i, (DegPre.trPt D.toPre F p.g.b).left ≫ (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ i =
      (aF D F oa a ≫ DegPre.trF D.toPre F (-z)).left ≫ DegPre.famφ D.toPre F χ i := fun i => by
    rw [← Category.assoc, ← Over.comp_left, tr_aF oa a p.g.b z hb]
  have e2 : ∀ i, (aF D F oa a).left ≫ (DegPre.trF D.toPre F (-z)).left ≫ DegPre.famφ D.toPre F χ i =
      (aF D F oa a ≫ DegPre.trF D.toPre F (-z)).left ≫ DegPre.famφ D.toPre F χ i := fun i => by
    rw [← Category.assoc, ← Over.comp_left]
  have e3 : star a • χ + p.y = star a • (χ - z) := by rw [hy, smul_sub, sub_eq_add_neg]
  have e4 : χ + 1 • -z = χ - z := by rw [one_smul, sub_eq_add_neg]
  have hF : FormEq (Sum.elim (pullφ D F oa a (χ - z))
      (fun i => (aF D F oa a).left ≫ DegPre.deltaφ D.toPre F 1 χ (-z) i)) (Sum.elim (pullε 1 N) (DegPre.deltaε 1))
      (Sum.elim (fun i => (DegPre.trPt D.toPre F p.g.b).left ≫ pullφ D F oa a χ i)
        (DegPre.phiφ D.toPre F p.y (star a • χ) p.g.b)) (Sum.elim (pullε 1 N) (DegPre.deltaε (1 * N))) :=
    fun U _ h => by
      simp only [pullφ, pullε, DegPre.phiφ, DegPre.deltaφ, DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl,
        Sum.elim_inr, e1, e2, e3, e4]
      simp only [Fin.prod_univ_four]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module
  have key := gen_unique' D.toPre.P.isLB hF (fst (TF (R := V) F) D.toPre.P.A).left (DegPre.zF D.toPre F).left
    (GC.zF_fst (D := D) (F := F)) (surj_appTop D.toPre F hG)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ huχ _) hΦ)
    (mulGen_isGen _ _ _ _ _ _ _ huχz (pullGen_isGen _ _ _ _ hfe _)) horig Z ρ z' J hJ
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ] at key
  exact key
