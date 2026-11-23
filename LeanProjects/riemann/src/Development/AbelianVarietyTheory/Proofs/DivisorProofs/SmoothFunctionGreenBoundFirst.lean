import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsUnitRescaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOnPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledMetricSmoothOnFlagPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverNormsRationalSectionDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionDivDetUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenFunctionPullbackEquality
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ShFam.Pad GlobalTheory.FlatSecCover

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.FlatSecCover.exists_ratSec_vertical_constNorm : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) →
    ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H) (B : ℝ), 2 ≤ B → ∀ (τ : D.what₂.Tau) (c : O.s.Comp)
    (g : (T.M c).Fun), (T.M c).Smooth g →
    (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) →
    ∀ (ε : (𝓞 D.what₂.LL →+* ℂ) → Fin ((T.M c).n + 1))
      (π : ∀ σ, GlobalTheory.CxPts (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p σ → (T.M c).X (ε σ)),
    (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.IsDown (h.man c) ε π →
    ∀ (hu : ∀ σ y, GlobalTheory.CxPts.CInfAt ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ) y)
      (hc : ∀ σ σ', (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ)).IsConj
        (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ'))),
    letI : IsLocallyNoetherian (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.X := (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.ar.isLocallyNoetherian
    ∃ (r : (comb (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))) hu hc)
      ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (1 : ℤ) fun o' => o'.elim 0 fun x => if x.1 = τ then (-1 : ℤ) else 0)).B.ι → (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.X.functionFieldˣ) (hr : GlobalTheory.Cartier.IsRatSec (comb (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))) hu hc)
      ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (1 : ℤ) fun o' => o'.elim 0 fun x => if x.1 = τ then (-1 : ℤ) else 0)).B r),
      (∀ z, ((comb (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))) hu hc)
      ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (1 : ℤ) fun o' => o'.elim 0 fun x => if x.1 = τ then (-1 : ℤ) else 0)).div hr).mult z ≠ 0 → ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p z).asIdeal ≠ ⊥) ∧
      ∀ σ, ∃ a : ℝ, ∀ y ∈ GlobalTheory.Cartier.offSupp (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p σ ((comb (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))) hu hc)
      ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (1 : ℤ) fun o' => o'.elim 0 fun x => if x.1 = τ then (-1 : ℤ) else 0)).div hr), GlobalTheory.Cartier.logNorm ((comb (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))) hu hc)
      ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (1 : ℤ) fun o' => o'.elim 0 fun x => if x.1 = τ then (-1 : ℤ) else 0)).φ σ) r y = a := by
  intro P2 PH SW D O hO hf A T H h B hB τ c g hg hgz ε π hπ hu hc
  obtain ⟨gY, hgY⟩ := exists_onPts (h.man c) g
  obtain ⟨l, hN⟩ := GlobalTheory.T.pulled_metric_smooth_on_flag_points D O A T H h B τ c g ε π hπ hu hc gY hgY
  have hU := GlobalTheory.T.flat_section_div_det_unit D O c B τ
  have hN2 := GlobalTheory.CoverNorm.norms_mul_unit _ _ _ _ _ _ _ (fun z => flatSec O.s O.Φ c τ / detFn O c B τ z) hU hN
  have hne : ∀ z, detFn O c B τ z ≠ 0 := fun z e => (hU z).ne_zero (by rw [e, div_zero])
  have hN3 := hN2.congr (f' := fun _ => flatSec O.s O.Φ c τ) (fun z => div_mul_cancel₀ _ (hne z))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
  refine GlobalTheory.T.cover_norms_rational_section_divisor _ _ _ _ _ _ _ hN3 fun σ => ?_
  obtain ⟨C, hC⟩ := GlobalTheory.T.green_function_pullback_equality D O hO A T H h B τ c g hg hgz gY hgY σ
  exact ⟨C + O.Y.htDetT B c τ, fun y => by rw [← hC y]; ring⟩

end
