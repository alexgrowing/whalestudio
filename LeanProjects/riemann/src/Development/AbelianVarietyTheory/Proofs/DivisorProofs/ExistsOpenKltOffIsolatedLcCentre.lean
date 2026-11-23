import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenKawamataLogTerminalLocusLogCanonicalLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenInterEqSingletonOfNoGenerisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopologicalKrullDimClosurePointLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem GlobalTheory.PairStep.exists_open_lc_klt_off_point :
    GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ : X → ℚ) (m : ℕ) (G : CartierDiv X) (x : X), 0 < m → IsLogCanonicalMultiple p n Γ m G → IsClosed ({x} : Set X) → LcCut p n Γ x 0 → ∃ U : X.Opens, x ∈ U ∧ (∀ y ∈ U, LcAt p n Γ y) ∧ (∀ y ∈ U, y ≠ x → KltAt p n Γ y) := by
  intro hPr X _ _ _ p n hp hdim Γ m G x hm hlc hx hcut
  obtain ⟨hlcx, hnk, hdimz⟩ := hcut
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  have hopen := (GlobalTheory.T.isOpen_kawamataLogTerminalLocus_logCanonicalLocus hPr ℂ X p n hp hdim Γ m G hm hlc).1
  set T : Set X := {y | ¬ KltAt p n Γ y} with hT
  have hTc : IsClosed T := by
    rw [← isOpen_compl_iff]
    convert hopen using 1
    ext y; simp [T]
  have hgen : ∀ z ∈ T, z ⤳ x → z = x := by
    intro z hzT hzx
    by_contra hne
    have h0 := hdimz z hzx hzT
    obtain ⟨e, _, he, h1⟩ := GlobalTheory.closure_point_topologicalKrullDim X n z hdim
    have h1' := h1 x hzx (Ne.symm hne)
    rw [he] at h0
    have : (e : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h0
    have : e ≤ 0 := by exact_mod_cast this
    omega
  obtain ⟨U, hxU, hU⟩ :=
    GlobalTheory.exists_open_inter_eq_singleton_of_no_generisation X T x hTc hx hnk hgen
  refine ⟨U, hxU, ?_, ?_⟩
  · intro y hy
    by_cases hyx : y = x
    · subst hyx; exact hlcx
    · have : y ∉ T := fun h => hyx ((hU y hy).1 h)
      have : KltAt p n Γ y := by simpa [T] using this
      exact this.lcAt
  · intro y hy hyx
    have : y ∉ T := fun h => hyx ((hU y hy).1 h)
    simpa [T] using this
