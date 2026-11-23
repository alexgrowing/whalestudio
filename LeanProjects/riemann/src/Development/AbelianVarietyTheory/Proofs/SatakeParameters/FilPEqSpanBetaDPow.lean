import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem filtration_eq_span_pow : ∀ (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  ∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n} := by
  intro l _ Co ϖ hb n
  have he := core_isEps l Co
  obtain ⟨hfil, -, -, -⟩ := filtration_eq_xi_pow l Co.ε he
  obtain ⟨-, -, -, -, hdom, -, hk⟩ := thetaP_facts l
  haveI := hdom
  have hass : Associated (algebraMap (Per.Ainf l) (Per.AinfP l) (xi Co.ε)) (beta ϖ) :=
    Ideal.span_singleton_eq_span_singleton.1 ((hk Co.ε he).symm.trans hb)
  have hD : Associated (aDp l (xi Co.ε) ^ n) (betaD ϖ ^ n) :=
    (hass.map (algebraMap (Per.AinfP l) (Per.BdRp l))).pow_pow
  ext y
  rw [hfil, Ideal.mem_span_singleton]
  exact hD.dvd_iff_dvd_left

end GlobalTheory.Pst.StLat
