import Mathlib
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalToGlobal.NormalizedHeckeFactors.UCardChoose
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GeoProdPow

namespace ConditionalKappaBounds.G2

open Formalism.BasicNotions Formalism.MainNotions

def UCard (D : D7) : Prop :=
  (Nat.card D.nexp.U : ℝ) = ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ^ (D.R.f * (D.R.r * (D.R.r - 1) / 2))

theorem geometric_generic_of_hypothesis (hc : GaussianProductPowerBound) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (hU : UCard D) : ThetaNormsAndLinks.admG2 D := by
  obtain ⟨Y, hY8, -, -, hYg⟩ := P.g_Y
  have hf1 : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hb : 2 ≤ L.sc.b := by
    unfold Scale.b Scale.L
    have h1 : 1 < L.sc.x ^ L.sc.eps := Real.one_lt_rpow L.sc.one_lt_alt L.sc.eps_pos
    have h2 : Real.exp 1 < Real.exp (L.sc.x ^ L.sc.eps) := Real.exp_lt_exp.mpr h1
    have h3 := Real.exp_one_gt_d9
    linarith
  have h := hc D.R.f D.R.k D.R.r L.sc.b (D.host.g 0) (D.host.g 1) hf1 hfk hb
    (hY8.trans (hYg 0).1) (hY8.trans (hYg 1).1)
  unfold ThetaNormsAndLinks.admG2 ThetaNormsAndLinks.eSh LiftErrorLocal.delq
  rw [hU]
  exact h

theorem uCard_of_tied (D : D7) (T : Formalism.L2.NExpTied D) : UCard D := by
  unfold UCard
  rw [Formalism.L2.NExpTied.uCard T]
  push_cast
  ring

theorem geometric_generic_of_layer_two (hc : GaussianProductPowerBound) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : Formalism.L2.NExpTied D) :
    ThetaNormsAndLinks.admG2 D :=
  geometric_generic_of_hypothesis hc D L P (uCard_of_tied D T)

end ConditionalKappaBounds.G2

namespace Formalism.MainNotions.DIV.GeometricGenericity

open Formalism.BasicNotions Formalism.MainNotions

theorem geometric_generic_of_layer_two (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : Formalism.L2.NExpTied D) : ThetaNormsAndLinks.admG2 D :=
  ConditionalKappaBounds.G2.geometric_generic_of_layer_two geometric_product_power D L P T

end Formalism.MainNotions.DIV.GeometricGenericity
