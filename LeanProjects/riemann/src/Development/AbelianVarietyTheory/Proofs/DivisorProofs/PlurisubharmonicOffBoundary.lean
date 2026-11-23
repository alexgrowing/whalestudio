import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorGeneratorRootExpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorGeneratorDominantRootStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam

theorem GlobalTheory.HodgeWeightPos.pshOff_th_ph : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c u, GlobalTheory.FlagPoly.Dom u → ∀ σ, PshOff ((T.M c).A σ) ((T.M c).Z σ) ((T.F c).th u σ + ReciprocityTheory.AnForm.M.LocPot.ofFun ((T.F c).ph u σ)) := by
  intro hP hH D O hO hN A T H h c u hu a j y hy hZ w
  obtain ⟨f, hf, hC⟩ := GlobalTheory.T.divisor_generator_root_exp hP hH D O hO hN A T H h c a j y hy hZ u
  rw [hC w]
  obtain ⟨T', _, p, q, ι, _, U, ψ, a', b', Y', π, AW, Aω, lam, hψ, ha, hb, hAW, hAω, hlam, hyY, hF2, hF0, hL⟩ :=
    GlobalTheory.T.divisor_generator_dominant_root hP hH D O hO hN A T H h c a j y hy hZ u hu f hf
  rw [hL w]
  set F := GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq (fun τ x => (a' τ : ℂ) • GlobalTheory.HermFrame.quotGram (ψ τ x)) (fun τ x => (b' τ : ℂ) • -GlobalTheory.HermFrame.subGram (ψ τ x)) π AW Aω lam with hFdef
  have hpos := (((GlobalTheory.T.good_reduction_statement_holds.2.2 (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) ι T' p q U ψ a' b' Y' π AW Aω hψ ha hb hAW hAω lam y hyY).1
    hlam) w)
  have hlog : ContDiffAt ℝ 2 (fun x => Real.log (F x)) y := hF2.log hF0.ne'
  have e1 : GlobalTheory.HermFrame.diagVal (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.lineChern F y) w =
      -(ReciprocityTheory.AnForm.levi (fun x => Real.log (F x)) y w / (2 * Real.pi)) := by
    rw [← GlobalTheory.HermFrame.diagVal_ddc hlog w]
    simp only [GlobalTheory.HermFrame.diagVal, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.lineChern]
    rw [GlobalTheory.HermFrame.chernOne_line (f := F) hF2 hF0.ne' (Filter.Eventually.of_forall fun x => rfl)]
    simp
  have e0 : GlobalTheory.HermFrame.diagVal (fun _ _ : Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ => (0 : ℂ)) w = 0 := by
    simp [GlobalTheory.HermFrame.diagVal]
  have h1 := hpos
  rw [e0, e1] at h1
  have hπ := Real.pi_pos
  have h2 : ReciprocityTheory.AnForm.levi (fun x => Real.log (F x)) y w ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < ReciprocityTheory.AnForm.levi (fun x => Real.log (F x)) y w / (2 * Real.pi) := div_pos hc (by positivity)
    linarith
  linarith
