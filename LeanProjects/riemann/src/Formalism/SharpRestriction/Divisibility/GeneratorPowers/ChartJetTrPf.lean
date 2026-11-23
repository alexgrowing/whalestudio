import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrD

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

set_option maxHeartbeats 1000000 in
theorem chartJetTr_of (hTan : ChartJetTanSt Xo c) (hBas : ChartJetBasisSt Xo c) : ChartJetTrSt Xo c := by
  intro T io y I d FT actT tgT uvecT xT hbas hch hdir
  letI := io.toAlgebra
  refine ⟨xU I xT, xP I xT, ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m a => ?_,
    hTan T io y I d FT actT tgT uvecT xT hbas hch hdir, hBas T io y I d FT actT tgT uvecT xT hbas hch hdir⟩,
    fun m => xL_fst I xT m, fun m => rfl⟩
  ·
    apply Over.OverMorphism.ext
    show spMap _ ≫ xL I xT m ≫ I.m1.φ = (spMap (algebraMap T.Fr T.Fr) ≫ y.1.x) ≫ η[Xo.univ.t.G].left
    rw [← Category.assoc, xL_zero I xT hch.zero m, unit_push I.m1.cart, spMap_alg_self, Category.id_comp]
  ·
    apply Over.OverMorphism.ext
    show spMap _ ≫ xL I xT (m + 1) ≫ I.m1.φ = xL I xT m ≫ I.m1.φ
    rw [← Category.assoc, xL_trunc I xT hch.trunc m]
  ·
    simp only [psTrunc_map]
    let W : (jO y.1 d m 2) ⟶ Over.mk ((jOG (𝟙 (Sp T.Fr)) d m 2).hom ≫ y.1.x) :=
      Over.homMk (𝟙 _) (by
        show 𝟙 _ ≫ (spMap _ ≫ 𝟙 _) ≫ y.1.x = spMap _ ≫ y.1.x
        simp)
    have hj : ∀ i : Fin 2, jpt y.1 d (xU I xT) m i =
        W ≫ pushHom I.m1.cart _ (jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m i) := fun i =>
      Over.OverMorphism.ext (by
        show spMap _ ≫ xL I xT m ≫ I.m1.φ = 𝟙 _ ≫ (spMap _ ≫ xL I xT m) ≫ I.m1.φ
        simp)
    rw [hj 0, hj 1, ← MonObj.comp_mul, ← map_mul, ← xP_law I xT FT m (hch.law m)]
    apply Over.OverMorphism.ext
    show spMap _ ≫ xL I xT m ≫ I.m1.φ = 𝟙 _ ≫ (spMap _ ≫ xL I xT m) ≫ I.m1.φ
    simp
  ·
    simp only [psTrunc_map]
    apply Over.OverMorphism.ext
    show (xL I xT m ≫ I.m1.φ) ≫ (Xo.univ.t.act.act a).left = spMap _ ≫ xL I xT m ≫ I.m1.φ
    rw [Category.assoc, ← I.m1.act a, ← Category.assoc, xL_act I xT (actT a) a m (hch.act m a), Category.assoc]

end Formalism.MainNotions.ModuliIntegralCharts.H1
