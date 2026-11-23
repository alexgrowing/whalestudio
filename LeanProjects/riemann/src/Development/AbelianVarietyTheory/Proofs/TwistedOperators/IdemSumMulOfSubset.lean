import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.Tow

namespace GlobalTheory.Tow

theorem idemAt_orth {D : D7} {P Q : Formalism.L2.DIV.Pl D.host.E} {a b : AE D} (ha : Formalism.L2.NTheta.IsIdemAt a P)
    (hb : Formalism.L2.NTheta.IsIdemAt b Q) (h : P ≠ Q) : a * b = 0 := by

  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have ha0 := GlobalTheory.PlaceModelSum.infPart_split ha.1
  have hda := (GlobalTheory.IdemSupport.tie_iff hΦ ha.1.1 ha0 P).mp ha.2
  have hdb := (GlobalTheory.IdemSupport.tie_iff hΦ hb.1.1 (GlobalTheory.PlaceModelSum.infPart_split hb.1) Q).mp hb.2
  apply hΦ.ext'
  · rw [map_mul, ha0, zero_mul, map_zero]
  · intro R
    rw [GlobalTheory.IdemSupport.ev_mul, GlobalTheory.IdemSupport.ev_zero]
    by_cases hR : R = P
    · rw [hR, hdb.2.2 P h, mul_zero]
    · rw [hda.2.2 R hR, zero_mul]

theorem idemAt_unique {D : D7} {P : Formalism.L2.DIV.Pl D.host.E} {a b : AE D} (ha : Formalism.L2.NTheta.IsIdemAt a P)
    (hb : Formalism.L2.NTheta.IsIdemAt b P) : a = b := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  exact GlobalTheory.IdemSupport.delta_unique hΦ
    ((GlobalTheory.IdemSupport.tie_iff hΦ ha.1.1 (GlobalTheory.PlaceModelSum.infPart_split ha.1) P).mp ha.2)
    ((GlobalTheory.IdemSupport.tie_iff hΦ hb.1.1 (GlobalTheory.PlaceModelSum.infPart_split hb.1) P).mp hb.2)

theorem idemSum_mul_of_subset {D : D7} {e e₂ : AE D} {P P₂ : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsIdemSum e P) (h₂ : IsIdemSum e₂ P₂) (hP : P ⊆ P₂) : e₂ * e = e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨fs, hfs, rfl⟩, -⟩ := h₂
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R hR => ?_

  rw [Finset.sum_mul, Finset.sum_eq_single_of_mem R (hP hR)]
  · rw [idemAt_unique (hfs R (hP hR)) (hes R hR)]
    exact (hes R hR).1.1
  · intro Q hQ hQR
    exact idemAt_orth (hfs Q hQ) (hes R hR) hQR

end GlobalTheory.Tow
