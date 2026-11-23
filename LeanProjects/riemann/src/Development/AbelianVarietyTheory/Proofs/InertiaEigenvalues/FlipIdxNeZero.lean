import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LevelSeries

def flipElt {D : D7} (e : AE D) (m : ℕ) : AE D :=
  e * (m : AE D) + cA D e * incA D ((m : D.host.E)⁻¹) + (1 - e - cA D e)

theorem flipIdx_ne_zero {D : D7} (V W : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) {m : ℕ} (hm : m ≠ 0) :
    flipIdx V W T m ≠ 0 := by
  unfold flipIdx
  rw [Finset.prod_ne_zero_iff]
  intro PP _
  refine pow_ne_zero _ ?_
  rw [Ne, Ideal.absNorm_eq_zero_iff, HeightOneSpectrum.maxPowDividing]
  exact pow_ne_zero _ PP.ne_bot

end GlobalTheory.LevelSeries

end
