import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemThPsiOfMemSpan
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedSeriesSpecialisedUniversalDatumMemSpanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

theorem thetaLatticeCondition_of_seriesComparison_universalChar {D : D7} {ρ : Setup D.ntw} {hρ : ρ.Good} {rd : Rds D.nexp ρ} (T : Comparison₂ hρ rd)
    (hY : GlobalTheory.UnivChar.IsUnivChar D.nexp) (hR : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatTwist hρ (rd i j b)) :
    Formalism.MainNotions.IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp := by
  intro i hi j hj b k Q M χ hψ a hQa
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj1
  let j' : Fin D.R.m := ⟨n, hj2⟩
  have T := T i j' b
  by_cases hoff : InRange D.ntw i Q ∧ ∀ a', ρ.xi i j' b D.nexp Q M (T.cls a) (T.coef a) a' ∈ Set.range (rd i j' b)
  · choose x hx using hoff.2
    rw [T.thU_eq Q M a hoff.1 x hx]
    obtain ⟨z, hz, hzr⟩ := exists_mem_thPsi_of_mem_span T (hR i hi j' b) hψ hoff.1.2.1 a
      (f := specXi ρ D.nexp i j' b k Q M χ (T.cls a) (T.coef a))
      (by
        rw [GlobalTheory.T.specialised_universal_series_eq_twisted_thetaSeries ρ hρ D.nexp hY i j' b k Q M χ hψ]
        exact GlobalTheory.T.twistedSeries_specialisedUniversalDatum_mem_span ρ hρ D.nexp hY i j' b k Q M χ hψ hoff.1 _ _ _ (T.dat a)
          fun v hv h => Finset.disjoint_left.1 hQa hv ((T.lev_iff a v).2 h))
    have e : z = Formalism.MainNotions.IntegralHeckeForms.specU D.nexp i ((j' : ℕ) + 1) b Q M k χ (grpSum D.nexp (ρ.ch i) Q M x) := by
      refine T.injective_rdK k (hzr.trans ?_)
      rw [rdK_specU_grpSum hρ (rd i j' b) k Q M χ x, specXi]
      exact Finset.sum_congr rfl fun a' _ => by rw [hx a']
    rw [← e]
    exact hz
  · rw [T.thU_off Q M a hoff, map_zero]
    exact zero_mem _

theorem thetaLatticeCondition_of_fullSeriesComparison : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd →
    GlobalTheory.TwInputs.Laws hρ rd → Formalism.MainNotions.IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp :=
  fun _ _ _ _ F L => thetaLatticeCondition_of_seriesComparison_universalChar F.tie F.univ fun i hi j b => (L.rat i hi j b).2.1

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

end GlobalTheory.SeriesTie
