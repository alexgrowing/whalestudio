import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareFormStatementStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryDataToroidalSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositivePotentialCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialsBoundedByPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySectionDiagonalInteriorEmptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorNormContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySettingOfPositivePotentialStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PoinBase
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsAdmissibleConst)

theorem poincare_curvBound : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)], ∃ (α : LocPot (CxPts (genStr s.T.Z) σ)) (Λ : Fin x.m → LocPot (CxPts (genStr s.T.Z) σ)) (sg : Fin x.m → CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ → ℂ) (t C : ℝ), IsBoundarySetting (manifold s.T.Z σ).finAtlas α Λ sg t ∧ (∀ i y, normSec (Λ i) (sg i) y = x.nrm σ i y) ∧ (∀ i, Continuous (x.nrm σ i)) ∧ boundary sg = {y | ¬ Inner y} ∧ CurvBound x σ (poincarePot α Λ sg t) C := by
  intro D A N j S κ s x σ _
  have := isProper_genStr s.T.Z
  letI : MeasurableSpace (CxPts (genStr s.T.Z) σ) := borel _
  haveI : BorelSpace (CxPts (genStr s.T.Z) σ) := ⟨rfl⟩
  obtain ⟨Λ, sg, hB, hn⟩ := GlobalTheory.T.boundary_data_toroidal_section D A N j S κ s x σ
  obtain ⟨α, hα, hαp⟩ := GlobalTheory.T.exists_positive_potential_compact D A N j S κ s x σ
  obtain ⟨cs, hcs, -, hS, hall, hmod⟩ :=
    GlobalTheory.T.poincare_form_statement _ _ (manifold s.T.Z σ).finAtlas α hα hαp _ Λ sg _ hB
  obtain ⟨K, hK⟩ := GlobalTheory.T.potentials_bounded_by_positive _ _ (manifold s.T.Z σ).finAtlas α x.m Λ hα hαp (fun i => (hB i).1)
  have hKs : 0 ≤ ∑ i, K i := Finset.sum_nonneg fun i _ => (hK i).1
  set t := min cs (Real.exp 1 / (2 * (∑ i, K i + 1))) with ht
  have ht0 : 0 < t := lt_min hcs (by positivity)
  have htc : t ≤ cs := min_le_left _ _
  obtain ⟨hPot, hT, hG, -⟩ := hall t ht0 htc
  have hns : ∀ i y, normSec (Λ i) (sg i) y = x.nrm σ i y := fun i y => hn i y
  have hadm : t * ∑ i, K i ≤ Real.exp 1 / 2 := by
    have h1 : t ≤ Real.exp 1 / (2 * (∑ i, K i + 1)) := min_le_right _ _
    have h2 : t * ∑ i, K i ≤ Real.exp 1 / (2 * (∑ i, K i + 1)) * ∑ i, K i :=
      mul_le_mul_of_nonneg_right h1 hKs
    refine h2.trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.exp_pos 1]
  have hadm' : IsAdmissibleConst (manifold s.T.Z σ).finAtlas α Λ t := ⟨ht0, K, hK, hadm⟩
  have hset : IsBoundarySetting (manifold s.T.Z σ).finAtlas α Λ sg t :=
    ⟨hα, hαp, fun i => ⟨(hB i).1, (hB i).2.1, GlobalTheory.T.boundary_section_diagonal_interior_empty _ _ _ _ _ _ _ hB i, fun y => (hB i).2.2.2 y⟩, hadm'⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.boundary_setting_of_positive_potential D A N j S κ s x σ α Λ sg t hα hαp hB hn ht0 hS hPot hT hG fun ψ σ' h => by
    obtain ⟨ρ, h1, h2, h3, h4⟩ := hmod ψ σ' h
    exact ⟨ρ, h1, h2, h3, h4 t ht0 htc⟩
  refine ⟨α, Λ, sg, t, C, hset, hns, fun i => GlobalTheory.T.divisor_norm_continuous _ _ _ (x.nrm_div σ i), ?_, hC⟩
  ext y
  simp only [boundary, Set.mem_ofPred_eq, GlobalTheory.ShFam.Hor.Inner, not_not]
  change (∃ i, sg i y y = 0) ↔ LiesIn y (genBd s.T.Z)
  rw [x.liesIn_genBd_iff]
  refine exists_congr fun i => ?_
  have e := hns i y
  simp only [normSec] at e
  rw [← ((x.nrm_div σ i).pos_iff y).not_left, not_lt, ← e]
  constructor
  · intro h0; rw [h0]; simp
  · intro h0
    have h1 : ‖sg i y y‖ * Real.exp (-(Λ i).φ y y) = 0 :=
      le_antisymm h0 (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    rcases mul_eq_zero.1 h1 with h | h
    · exact norm_eq_zero.1 h
    · exact absurd h (Real.exp_pos _).ne'

end GlobalTheory.PoinBase
