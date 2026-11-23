import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
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

variable {D : D7}

def flipIdx (V W : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) : ℕ :=
  ∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((m : ℕ) : 𝓞 D.host.E)})) ^ (V.rank * W.rank)

def flipScal (χW : (AE D)ˣ →* Circle) (V W : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (x : (AE D)ˣ) : ℂ :=
  ((χW x : Circle) : ℂ)⁻¹ * ((Real.sqrt (flipIdx V W T m : ℝ) : ℝ) : ℂ)⁻¹

def IsFlipDet (V : HSp D) (e : AE D) (m : ℕ) (x : (AE D)ˣ) : Prop :=
  (x : AE D) * (e * (m : AE D) ^ V.rank + (1 - e)) = 1

end GlobalTheory.LevelSeries

end
