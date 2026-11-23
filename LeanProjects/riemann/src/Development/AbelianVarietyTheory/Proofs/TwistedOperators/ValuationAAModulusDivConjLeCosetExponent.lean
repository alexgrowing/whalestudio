import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.ShiftVal

open scoped Pointwise

theorem valuation_le_of_mem {K : Type} [Field K] [NumberField K] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {I : FractionalIdeal (𝓞 K)⁰ K} {b : K} (hb : b ∈ I) :
    w.valuation K b ≤ WithZero.exp (-FractionalIdeal.count K w I) := by
  by_cases hb0 : b = 0
  · rw [hb0, map_zero]; exact zero_le'
  have h1 : FractionalIdeal.count K w I ≤ FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ b) :=
    FractionalIdeal.count_mono K w (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hb0)
      ((FractionalIdeal.spanSingleton_le_iff_mem).mpr hb)
  rw [ReciprocityTheory.Neutral.Bridge.HCFR.count_spanSingleton K w hb0] at h1
  have hv : w.valuation K b ≠ 0 := (map_ne_zero _).mpr hb0
  rw [← WithZero.exp_log hv, WithZero.exp_le_exp]
  omega

theorem val_le_cosExp : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts}
    (G : GridData L sc), ∀ w ∈ G.pl.W0, ∀ b ∈ D.host.AA * shiftId G,
      Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  intro D hq T L μ0 hL sc G w hw b hb
  classical
  have hM : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact G.pl.modul_ne_bot sc
  have hMb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    unfold Places.modulBar
    intro h
    apply G.pl.modul_ne_bot sc
    have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
    simpa [smul_smul] using this
  have hwl : w ∈ locPl G μ0 := by unfold locPl; exact Finset.mem_union_left _ hw
  have hc : FractionalIdeal.count D.host.E w (shiftId G) = cosExp G w := by
    show FractionalIdeal.count D.host.E w
      (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹) = _
    rw [FractionalIdeal.count_mul _ _ hM (inv_ne_zero hMb), FractionalIdeal.count_inv,
      count_modul, count_modulBar G hwl, neg_zero, add_zero]
  rw [Good.valued_alg]
  refine FractionalIdeal.mul_induction_on hb ?_ ?_
  · intro a ha s hs
    rw [map_mul]
    have h1 := GlobalTheory.DepthFix.aa_int hL hq G hw a ha
    rw [Good.valued_alg] at h1
    have h2 := valuation_le_of_mem w hs
    rw [hc] at h2
    calc _ ≤ 1 * WithZero.exp (-(cosExp G w : ℤ)) := mul_le_mul' h1 h2
      _ = _ := one_mul _
  · intro x y hx hy
    exact Valuation.map_add_le _ hx hy

end GlobalTheory.AscFin.ShiftVal
