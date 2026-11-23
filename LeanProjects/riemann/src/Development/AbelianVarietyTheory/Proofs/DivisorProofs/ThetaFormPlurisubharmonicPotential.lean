import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPshPotentialFundamentalWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalWeightPotentialChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPshFormPshStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory Set GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ProjVar Formalism.L2.Pj Formalism.L2.Geo GlobalTheory

namespace GlobalTheory.FundExtPsh

theorem extends_psh : Hypotheses2 → HypothesesH → OnCore fun D O x _ => ∀ c (σ : D.what₂.LL →+* ℂ) τ (i : Fin O.N), (i : ℕ) + 1 < O.N → ∃ v : Pts (O.var c) σ → EReal, GlobalTheory.Published.IsFormPsh (AnRead.all (O.var c).str σ (O.var c).dim) (thW (refMet x O.Φ) c σ (fund τ i)) v ∧ ∀ y ∈ offBd O.Φ c σ, (v y).toReal = psi O x c σ τ i y := by
  intro hP hH D O x P hc hN hR c σ τ i hi
  obtain ⟨A, T, H, ⟨R⟩⟩ := hR
  obtain ⟨a, rfl⟩ := (R.man c).ε.surjective σ
  obtain ⟨v, hv, hvZ⟩ := GlobalTheory.T.quasi_psh_potential_fundamental_weight hP hH D O ⟨x, P, hc⟩ hN A T H R c a τ i hi
  refine ⟨v ∘ ((R.man c).pt a).symm, ?_, ?_⟩
  · have h3 := GlobalTheory.T.fundamental_weight_potential_chart D O A T H R c a (fund τ i)
    rw [hc.h0_eq] at h3
    exact GlobalTheory.T.quasi_psh_form_psh _ (O.var c) _ (T.M c) (R.man c) (O.dim_eq c) a _ _ v (T.th_pot c _ a) h3 hv
  · intro y hy
    have hz : ((R.man c).pt a).symm y ∉ (T.M c).Z a := by
      rw [(R.an c).Z]
      simpa [offBd] using hy
    have e1 := (R.an c).ph (fund τ i) a _ hz
    simp only [Function.comp_apply]
    rw [hvZ _ hz, EReal.toReal_coe]
    erw [e1]
    rw [Homeomorph.apply_symm_apply, hc.two_mul_chg]

end GlobalTheory.FundExtPsh
