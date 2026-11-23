import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CocycleProductThree

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

attribute [local instance] Over.cartesianMonoidalCategory

theorem jet_zero_hom_ext {S : Type} [CommRing S] {κ κ' : Type} (f g : Jet S κ 0 →ₐ[S] Jet S κ' 0) : f = g := by
  apply jet_hom_ext
  intro i
  have h0 : (Ideal.Quotient.mk (orig S κ ^ (0 + 1)) (MvPolynomial.X i) : Jet S κ 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact X_mem_orig i)
  rw [h0, map_zero, map_zero]

theorem comp_one' {X0 : Scheme.{0}} {G : Over X0} [GrpObj G] {T T' : Over X0} (f : T' ⟶ T) :
    f ≫ (1 : T ⟶ G) = 1 := by
  show f ≫ (toUnit T ≫ η[G]) = toUnit T' ≫ η[G]
  rw [← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem val_scale' {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (hJ : Good Xo.univ.t.PP.L z J) :
    val (scaleGen φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  GermB.val_scale Xo.univ.t φ ε u g r z J hJ

theorem chart_at_zero_eq_one (C : ChartAt Xo c y) : C.x 0 = 1 := by
  have hz := C.chart.zero 0
  have hid : homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)) ≫
      homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S) = 𝟙 _ := by
    rw [homAt_comp, jet_zero_hom_ext ((Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)).comp jetAug) (AlgHom.id S _), homAt_id]
  calc C.x 0 = 𝟙 _ ≫ C.x 0 := (Category.id_comp _).symm
    _ = (homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)) ≫
          homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)) ≫ C.x 0 := by rw [hid]
    _ = homAt y.x (Algebra.ofId S (Jet S (Fin 1 × Fin C.d) 0)) ≫ 1 := by rw [Category.assoc, hz]
    _ = 1 := comp_one' _

theorem jet_point_zero_eq_one (C : ChartAt Xo c y) {n : ℕ} (i : Fin n) : jpt y C.d C.x 0 i = 1 := by
  unfold jpt
  rw [chart_at_zero_eq_one C]
  exact comp_one' _

theorem const_ad (C : ChartAt Xo c y) (a : 𝓞 E) : MvPowerSeries.constantCoeff (C.B.ad a) = 1 := by
  have e := Formalism.MainNotions.ModuliIntegralCharts.H1.Sym.const_ev (n := 1) ![0, Germ.pt S (n := 1) C.d 0]
    (by intro p q; fin_cases p <;> simp [Germ.pt]) (C.B.ad a)
  rw [C.B.adjoint_zero_fst a, map_one] at e
  exact e.symm

def AdRel (C : ChartAt Xo c y) (a : 𝓞 E) (wL : ExpGC.AdTy Xo a) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ, (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (C.B.ad a) ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (jpt y C.d C.x m (0 : Fin 2)) (jpt y C.d C.x m (1 : Fin 2))).left)
        (pe y C.d C.x C.e m ![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
      (scaleGen _ _ (unitΓ u)
        (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)]))

theorem exists_adRel (C : ChartAt Xo c y) (a : 𝓞 E) : ∃ wL : ExpGC.AdTy Xo a, wL.IsGen ∧ AdRel C a wL :=
  C.frame.ad a

theorem wL_zero (C : ChartAt Xo c y) (a : 𝓞 E) (wL : ExpGC.AdTy Xo a) (hrel : AdRel C a wL) {Z : Scheme.{0}}
    (r : Z ⟶ (overAt y.x S).left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι)
    (hJ : Good Xo.univ.t.PP.L z J) :
    val wL (r ≫ (lift (1 : overAt y.x S ⟶ Xo.univ.t.G) (1 : overAt y.x S ⟶ Xo.univ.t.G)).left) z J = 1 := by
  obtain ⟨u, hu, hc⟩ := hrel 0
  have hu1 : u = 1 := Units.ext (hu.trans (ExpGB.psJet_zero_of _ (const_ad C a)))
  have hι : homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S) ≫
      lift (jpt y C.d C.x 0 (0 : Fin 2)) (jpt y C.d C.x 0 (1 : Fin 2)) =
        lift (1 : overAt y.x S ⟶ Xo.univ.t.G) (1 : overAt y.x S ⟶ Xo.univ.t.G) := by
    rw [jet_point_zero_eq_one C, jet_point_zero_eq_one C, comp_lift]
    exact congrArg₂ (fun p q => lift p q) (comp_one' _) (comp_one' _)
  have h1 := val_corr hJ hc (r ≫ (homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S)).left)
  rw [val_mul hJ, val_pull hJ, val_scale' _ _ _ _ _ z J hJ, hu1,
    show unitΓ (1 : (Jet S (Fin 2 × Fin C.d) 0)ˣ) = 1 by unfold unitΓ; exact map_one _, map_one,
    _root_.one_mul] at h1
  have hpe : val (pe y C.d C.x C.e 0 ![fun j => psIn C.d 0 ![0] (C.B.A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
      (r ≫ (homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S)).left) z J =
      val (pe y C.d C.x C.e 0 ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d 0 ![1] (C.B.A.act (H.bar a) j)])
        (r ≫ (homAt y.x (jetAug : Jet S (Fin 2 × Fin C.d) 0 →ₐ[S] S)).left) z J := by
    have hm : (homAt y.x (jetSubstP 0 fun p : Fin 2 × Fin C.d =>
        (![fun j => psIn C.d 0 ![0] (C.B.A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2)).left =
        (homAt y.x (jetSubstP 0 fun p : Fin 2 × Fin C.d =>
          (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d 0 ![1] (C.B.A.act (H.bar a) j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2)).left := by
      rw [jet_zero_hom_ext (jetSubstP 0 _) (jetSubstP 0 fun p : Fin 2 × Fin C.d =>
        (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d 0 ![1] (C.B.A.act (H.bar a) j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2)]
    unfold pe
    rw [hm]
  rw [hpe, mul_eq_right] at h1
  rw [Category.assoc, ← Over.comp_left, hι] at h1
  exact h1

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
