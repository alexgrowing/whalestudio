import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjInvGradedReferenceLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualVolumeOnObjectsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeAndArithmeticCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitFamilyRelabelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSizeAndRangeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalBoundOnObjectsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsSumToVolumeProportionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBoundAndFlatLimitValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagHeightOfHhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeComparisonOnPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPolynomialBoundInDirectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOnObjectsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwiceDifferentiableOfPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtSubConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HtCmpOfTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AgreementOfPolynomialFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitFamilyAndPolynomialsExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizePositiveHeightsOfTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqueezeOfTieAr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedBasePt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

theorem GlobalTheory.CovHt.inputsSt_of_scholzeWeinstein : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → Known₂ → GlobalTheory.Published.ScholzeWeinsteinB → InputsSt := by
  intro hX hP hH hQ hSW
  obtain ⟨r, hT⟩ := hQ.test
  obtain ⟨Cf, hFl⟩ := GlobalTheory.T.flat_bound_and_flat_limit_values hX hP hH hSW
  refine ⟨r, Cf, fun D O hC hf hFew => ?_⟩
  obtain ⟨A₀, T, H, ⟨h₀⟩, -⟩ := GlobalTheory.Mean4O.ReadsEx.main hP.p4 D O hC

  have hSR := GlobalTheory.T.fibre_size_and_range_bound hP hH D O hC hf A₀ T H h₀
  have hQP := GlobalTheory.T.quasi_polynomial_bound_in_direction hP hH D O hC hf A₀ T H h₀
  have hFamR : ∀ c, (T.F c).FamR O.Y.j := fun c =>
    GlobalTheory.Mean4O.InterpFam.famR_of_inR D O.Y T c (fun σ => ((hQP c) σ).1) (hSR c).1 (hSR c).2
  obtain ⟨hΦ, hPs⟩ := GlobalTheory.T.limit_family_and_polynomials_exist D O.Y T hFamR
  obtain ⟨Ps, hTiePs⟩ := hPs A₀
  set A : SlopeTestRemainingChoices O.Y := { A₀ with Ps := Ps }
  have h : O.Reads A T H := h₀.withPs Ps
  obtain ⟨hTD, hTM, hTA⟩ := GlobalTheory.T.degree_and_arithmetic_compatibility hP hH D O hC hf A T H h
  obtain ⟨Φ, hLim⟩ := hΦ hTD
  obtain ⟨⟨hh, hIs⟩, hFH⟩ := GlobalTheory.T.flag_height_of_hh hP D.what₂.Tau O.Y.N
  refine ⟨A, Φ, hh, ?_⟩
  have hQPA : ∀ c, (T.F c).QPolBd A.dir := GlobalTheory.T.quasi_polynomial_bound_in_direction hP hH D O hC hf A T H h
  have hSRA := GlobalTheory.T.fibre_size_and_range_bound hP hH D O hC hf A T H h
  have hInS : ∀ c, (T.F c).InS := hQ.reg D O hC hf A T H h
  have hNS := fun c => GlobalTheory.Mean4O.RegFam.nefAn_and_famS D O.Y T c (hInS c)
  have hFamS : ∀ c, (T.F c).FamS := fun c => (hNS c).2 A.dir (hQPA c) (hSRA c).1
  have hNefAn : ∀ c, (T.F c).NefAn := fun c => (hNS c).1
  obtain ⟨hP4, hvol, -⟩ := GlobalTheory.T.weights_sum_to_volume_proportional hP hH D O hC hf A T H h
  have hTie := GlobalTheory.Mean4O.htTie_of_reads D O A T H h hC.mbIs
  have hLat := GlobalTheory.T.lattice_comparison_on_points hP hH D O hC hf A T H h
  have hCmp := GlobalTheory.Mean4O.htCmp_of_tie D O.Y T A H h.pts hFamS hTie hLat
  obtain ⟨hFB, hFV⟩ := hFl D O hC hf A T H h hFew
  obtain ⟨hPS, -, hHt⟩ := GlobalTheory.Mean4O.size_positive_heights_of_tie
  refine ⟨hLim, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hFB, ?_⟩
  · exact hPS D O.Y T A Φ hTD hTiePs hLim (GlobalTheory.T.vertical_bound_on_objects hP hH D O hC hf A T H h)
  · exact GlobalTheory.T.agreement_of_polynomial_families D O.Y T A hFamR hFamS hTiePs hTM
  · exact NefAt.positive (GlobalTheory.T.nef_on_objects hX hP hH D O hC hf A T H h) (semiposAt_of_famS hFamS hTM)
  · exact GlobalTheory.Mean4O.squeeze_of_tieAr hP.p3 hP.p2 hP.p4 D O.Y A hTA
  · exact hHt D O.Y A H hCmp (hQ.int D O hC hf A T H h) (hQ.bd D O hC hf A T H h) (hQ.up D O hC hf A T H h)
  · exact GlobalTheory.Mean4O.Deg.degrees D O.Y T A hFamS hNefAn (fun c => (hQPA c).qPol) hP4 hvol hTM
  · exact GlobalTheory.T.equal_volume_on_objects hP hH D O hC hf A T H h
  · exact hQ.anti D O hC hf A T H h hh hIs Φ hLim
  · exact hFH hh hIs
  · exact GlobalTheory.T.limit_family_relabel hP hH D O hC hf A T H h Φ hLim
  · exact hFV Φ hLim
  · exact hT D O hC hf A T H h hh hIs Φ hLim
