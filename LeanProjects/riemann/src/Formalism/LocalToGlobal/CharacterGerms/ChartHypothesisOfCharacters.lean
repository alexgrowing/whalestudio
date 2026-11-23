import Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffPderivUncurry
import Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ChG

open VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem integralSeries_uncurry_one {χ : PS C 1 dd} (h : IntS V χ) : IntS V (un1 χ) := by
  intro μ
  exact h _

def lin {Y : FBChart C V O dd} (p : PairData Y d I) (g : Fin 2) (i : Fin dd) : MvPowerSeries (I g) C :=
  ∑ c', p.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)

theorem cc_lin {Y : FBChart C V O dd} (p : PairData Y d I) (g : Fin 2) (i : Fin dd) :
    MvPowerSeries.constantCoeff (lin p g i) = 0 := by
  unfold lin
  simp

theorem subst_lin_linF {Y : FBChart C V O dd} (p : PairData Y d I) (g : Fin 2) (χ : PS C 1 dd) :
    MvPowerSeries.subst (lin p g) (linF (dlogC χ)) =
      ∑ x : I g, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries (I g) C) := by
  unfold linF
  rw [subst_sum (cc_lin p g)]
  have h1 : ∀ i : Fin dd, MvPowerSeries.subst (lin p g) (dlogC χ i • (MvPowerSeries.X i : MvPowerSeries (Fin dd) C)) =
      ∑ x : I g, (dlogC χ i * p.u g x i) • (MvPowerSeries.X x : MvPowerSeries (I g) C) := by
    intro i
    rw [subst_smul (cc_lin p g), subst_X (cc_lin p g)]
    unfold lin
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold PairData.yOf
  rw [Finset.sum_smul]

end ChG

open ChG VP in
theorem charGerm_holds : CharGermSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p Hc χ hχ g S t ht
  obtain ⟨P, hP0, hPI, -, hPt⟩ := FormalGermZero.sys_P Y p (Hc g) (S g)
  have ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0 := fun g c => (ht g).1 c
  have hI : IntS V (MvPowerSeries.subst P (un1 χ)) := IntS.subst hP0 hPI (integralSeries_uncurry_one hχ.1)
  have key : MvPowerSeries.subst (t g) (MvPowerSeries.subst P (un1 χ)) =
      mvExp (∑ x : I g, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries (I g) C)) := by
    rw [subst_subst hP0 (ht0 g)]
    have h1 : (fun j => MvPowerSeries.subst (t g) (P j)) = fun j => MvPowerSeries.subst (lin p g) (e Y j) := by
      funext j
      exact hPt (t g) (ht g) j
    rw [h1, ← subst_subst (cc_e Y) (cc_lin p g)]
    show MvPowerSeries.subst (lin p g) (Psi Y χ) = _
    rw [chi_exp Y hχ, subst_exp (cc_lin p g) (constantCoeff_linF _), subst_lin_linF]
  refine ⟨upG g (MvPowerSeries.subst P (un1 χ)), ?_, ?_⟩
  · exact IntS.subst (fun _ => cc_X _) (fun _ => IntS_X _) hI
  · rw [AbstractGermZero.upG_subst t ht0 g, key]

section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

theorem chart_hypothesis_of_characters (h : CharacterHypothesisCharts Xo c) : CharacterHypothesisAllCharts Xo c :=
  chart_hypothesis_of_character Xo c charGerm_holds h

end Chart

end Formalism.L2.FormalSeriesBounds
