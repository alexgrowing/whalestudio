import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetPointZeroEqOne

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem val_rigPow {Z : Scheme.{0}} (k : ℤ) (r : Z ⟶ (𝟙_ (Over Xo.X)).left) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) :
    val (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig k) r z J = val Xo.univ.t.PP.rig r z J ^ k := by
  unfold rigPow val
  exact map_zpow _ _ _

theorem eSec_act (c : 𝓞 E) : eSec Xo.univ.t.G ≫ (Xo.univ.t.act.act c).left = eSec Xo.univ.t.G := by
  haveI := Xo.univ.t.act.2 c
  unfold eSec
  rw [← Over.comp_left, IsMonHom.one_hom]

theorem eSec_toUnit : eSec Xo.univ.t.G ≫ (toUnit Xo.univ.t.G).left = 𝟙 _ := by
  unfold eSec
  rw [← Over.comp_left]
  simp

theorem exists_beta (wP : PrimTy H Xo) (hwP : IsPrim wP) (a : 𝓞 E) (hbb : H.bar (H.bar a) = a)
    (wLa : ExpGC.AdTy Xo a) (hwa : wLa.IsGen) (wLb : ExpGC.AdTy Xo (H.bar a)) (hwb : wLb.IsGen) :
    ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
        (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J → val β r z J = val (ExpGC.Bq wP a wLa wLb) r z J *
          (val (ExpGC.Bq wP a wLa wLb) (r ≫ (toUnit Xo.univ.t.G).left ≫ eSec Xo.univ.t.G) z J *
            val Xo.univ.t.PP.rig (r ≫ (toUnit Xo.univ.t.G).left) z J ^ (3 : ℤ))⁻¹ := by
  have hL := Xo.univ.t.PP.isLB
  have hrig := Xo.univ.t.PP.rigGen
  obtain ⟨β0, hβ0, hv0⟩ := ExpGC.exists_betaRaw wP hwP.1 a hbb wLa hwa wLb hwb
  have hg := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ β0 hβ0 (eSec Xo.univ.t.G))
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _ hrig
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _ hrig hrig))
  obtain ⟨g0, hg0, hv1⟩ := exists_gen hL (φ' := (PEmpty.elim : PEmpty.{1} → ((𝟙_ (Over Xo.X)).left ⟶ Xo.univ.t.G.left)))
    (ε' := PEmpty.elim) (by
      intro U _ hU
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, betaφ, betaε,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, eSec_act, Category.comp_id, Finset.univ_unique, Finset.prod_singleton,
        Finset.univ_eq_empty, Finset.prod_empty]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      abel) _ hg
  have hB := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen Xo.univ.t.PP.L _ _ _ _ _ _ hβ0
    (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen Xo.univ.t.PP.L _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ g0 hg0 (toUnit Xo.univ.t.G).left))
  obtain ⟨β, hβ, hv2⟩ := exists_gen hL (φ' := betaφ (Xo := Xo) a) (ε' := betaε) (by
      intro U _ hU
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_eq_empty, Finset.prod_empty,
        _root_.mul_one]) _ hB
  have hval : ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
      Good Xo.univ.t.PP.L z J → val β r z J = val (ExpGC.Bq wP a wLa wLb) r z J *
        (val (ExpGC.Bq wP a wLa wLb) (r ≫ (toUnit Xo.univ.t.G).left ≫ eSec Xo.univ.t.G) z J *
          val Xo.univ.t.PP.rig (r ≫ (toUnit Xo.univ.t.G).left) z J ^ (3 : ℤ))⁻¹ := by
    intro Z r z J hJ
    rw [hv2 Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, hv1 Z _ z J hJ, val_mul hJ, val_pull hJ, val_mul hJ,
      val_mul hJ, hv0 Z r z J hJ, hv0 Z _ z J hJ, ← Category.assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  refine ⟨β, hβ, corr_of_val hL fun z J hJ => ?_, hval⟩
  rw [val_pull hJ, hval _ _ z J hJ, val_rigPow]
  simp only [Category.id_comp]
  rw [← Category.assoc (eSec Xo.univ.t.G), eSec_toUnit, Category.id_comp]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGE
