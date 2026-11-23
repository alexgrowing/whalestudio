import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftOrigin

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFrobenius

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    sval s r z J = 0 := by
  unfold sval
  erw [hs (fun k => J (r ≫ φ k))]
  unfold gs
  split_ifs
  · erw [map_zero, map_zero]
  · rfl

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem phi_fixes (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (N : ℕ) (p : QkPt D.toPre F (1 * N))
    (z : D.toPre.X) (hy : p.y = -(star a • z)) (hb : p.g.b ≫ oa.onB.act a = cP D.toPre _ (-z))
    (r : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (hr : r.IsGen)
    (hr0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ r (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (hrel : ∀ (χ : D.toPre.X) (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J →
        val (p.g.s (star a • χ)) (𝟙 _) y J * val r (lift (DegPre.cF D.toPre F χ) p.g.b).left y J =
          val (D.toPre.tau (-z) χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J)
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε 1 N))) (hu0 : u0.IsGen)
    (hc0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F)))
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε (1 * N)))) (hw : w.IsGen)
    (hwv : ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val (LB.pullGen D.toPre.P.L _ _ (LB.mulGen D.toPre.P.L _ _ _ _
            (GeneratorPullback.powGen D.toPre.P.L _ _ (D.toPre.psi (-z)) 1) (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK 1))
              (jFK (R := V) F)) (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F p.g.b).left y J)⁻¹)
    (θ : Fam D.toPre F 1) (θα : Fam D.toPre F (1 * N)) (hpull : PullAl D F oa a 1 N θ θα) :
    PhiRel D.toPre F (1 * N) p w θα θα := by
  rw [phiRel_iff hG p w hw θα θα]
  intro a' β hβ T ρ z' J hJ
  by_cases ha : ∃ χ, a' = star a • χ
  · obtain ⟨χ, rfl⟩ := ha
    subst hβ
    have e3 : star a • χ + p.y = star a • (χ - z) := by rw [hy, smul_sub, sub_eq_add_neg]
    have e4 : χ + 1 • -z = χ - z := by rw [one_smul, sub_eq_add_neg]
    rw [e3]
    obtain ⟨uχz, huχz, hcz, hsz⟩ := hpull.1 (χ - z)
    obtain ⟨uχ, huχ, hc, hs⟩ := hpull.1 χ
    obtain ⟨⟨fe, hfe, hcfe⟩, -⟩ := gen_fe (D := D.toPre) (F := F) hG 1 (-z) χ
    obtain ⟨⟨Φ, hΦ, hcΦ⟩, hΦv⟩ := gen_phi hG p w hw (star a • χ)
    have s1 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ uχz).1 hsz _ ρ.left z' J hJ
    have s2 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ fe).1 (θ.fe (-z) χ fe hfe hcfe) _
      (ρ.left ≫ (aF D F oa a).left) z' J hJ
    rw [e4] at s2
    have s3 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ uχ).1 hs _ (ρ ≫ DegPre.trPt D.toPre F p.g.b).left z' J hJ
    have pt : (ρ ≫ DegPre.trPt D.toPre F p.g.b).left ≫ (aF D F oa a).left =
        (ρ.left ≫ (aF D F oa a).left) ≫ (DegPre.trF D.toPre F (-z)).left := by
      rw [← Over.comp_left, Category.assoc, CanonicalLiftEigen.tr_aF oa a p.g.b z hb, ← Category.assoc, Over.comp_left,
        Over.comp_left]
    have eig := CanonicalLiftEigen.eigen_of_origin hG oa a N p z hy hb χ uχ huχ uχz huχz fe hfe Φ hΦ
      (fun y J hJ => CanonicalLiftOrigin.origin hG oa a N p z r hr hr0 hrel u0 hu0 hc0 w hw hwv χ uχ huχ hc uχz hcz fe hcfe
        Φ hΦ hcΦ y J hJ) _ ρ.left z' J hJ
    have hΦρ := hΦv Φ hΦ hcΦ T ρ z' J hJ
    have eig' : (val fe (ρ.left ≫ (aF D F oa a).left) z' J).val * (val uχz ρ.left z' J).val =
        (val uχ (ρ ≫ DegPre.trPt D.toPre F p.g.b).left z' J).val * (val Φ ρ.left z' J).val := by
      rw [← Units.val_mul, ← Units.val_mul, _root_.mul_comm]
      exact congrArg Units.val eig.symm
    rw [s1, s2, s3, pt, ← hΦρ, _root_.mul_assoc, _root_.mul_assoc, eig']
  · have hβn : ∀ χ, β ≠ star a • χ := by
      intro χ h
      apply ha
      refine ⟨χ + z, ?_⟩
      rw [smul_add, ← h, ← hβ, hy]
      abel
    rw [sval_zero _ (hpull.2 β hβn), sval_zero _ (hpull.2 a' (fun χ h => ha ⟨χ, h⟩)), MulZeroClass.zero_mul]

end ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFrobenius
