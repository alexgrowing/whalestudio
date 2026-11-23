import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartFrameTrA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory

theorem linComb_gen_eq_of_eSec (hGF : GlobalFnsSt) {S X : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (A.left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((𝟙_ (Over S)).left ⟶ X)} {ε' : K' → ℤ}
    {a b : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (hb : b.IsGen) {r : LB.Gen (LB.LinComb L φ' ε')}
    (har : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε a (eSec A)) r)
    (hbr : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε b (eSec A)) r) : a = b := by
  have hcov : ∀ x : A.left, ∃ i, x ∈ (LB.LinComb L φ ε).U i := fun x => by
    choose I hI using fun k => exists_chart hL (φ k x)
    exact ⟨I, Set.mem_iInter.2 hI⟩
  obtain ⟨u, hu⟩ := ChartFrameTrA.exists_ratio_gen hcov ha hb
  suffices hu1 : u = 1 by
    cases a
    cases b
    congr 1
    funext p
    exact (hu p).trans (by rw [hu1, map_one, _root_.one_mul])
  apply ChartFrameTrA.unit_eq_one_of_eSec hGF A hA u
  have key : pullU (eSec A) ⊤ u = 1 := by
    refine unit_ext fun z hz => ?_
    choose J hJ using fun χ : (𝟙_ (Over S)).left ⟶ X => exists_chart hL (χ z)
    have hJ' : Good L z J := hJ
    have e1 := (val_pull hJ' a (eSec A) (𝟙 _)).symm.trans ((val_corr hJ' har (𝟙 _)).trans
      ((val_corr hJ' hbr (𝟙 _)).symm.trans (val_pull hJ' b (eSec A) (𝟙 _))))
    have hm := hJ'.mem φ (𝟙 _ ≫ eSec A)
    have e2 : val a (𝟙 _ ≫ eSec A) z J = gm (𝟙 _ ≫ eSec A) z ⊤ u * val b (𝟙 _ ≫ eSec A) z J :=
      (congrArg (gm _ z _) (hu _)).trans ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (gm_res _ z _ hm _) rfl))
    have e3 : gm (𝟙 _ ≫ eSec A) z ⊤ u = 1 := mul_eq_right.1 (e2.symm.trans e1)
    exact (gm_pull (𝟙 _) (eSec A) z ⊤ trivial u).trans (e3.trans (map_one _).symm)
  exact congrArg Units.val key

theorem isPrimG_unique : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X0 : Scheme.{0}) (t : SAB H X0), IsAbelianScheme t.G → ∀ wP wP' : PrimTyG t,
    IsPrimG t wP → IsPrimG t wP' → wP = wP' :=
  fun hGF _ _ _ _ _ _ t hA _ _ h h' =>
    linComb_gen_eq_of_eSec hGF t.G hA t.PP.isLB h.1 h'.1 h.2 h'.2

end GlobalTheory
