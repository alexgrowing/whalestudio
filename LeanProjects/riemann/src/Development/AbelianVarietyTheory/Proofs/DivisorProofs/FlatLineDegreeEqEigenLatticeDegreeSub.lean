import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationWeightedLogNormSum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegOfLatRankEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineDegreeInvariantFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionNeZeroAtNumberFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostIntegerCharacterCompConjEqConjEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameCoordsBasisEigenLatticeSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionConstValuationEigenLatticeAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthFlatSectionEqFrameNormComplexEmbeddinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDeterminantLineTwoHermitianLatticesStatement

noncomputable section

namespace GlobalTheory.PtDeg

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem lineDeg_eq_deg_eigLat_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)), Nonempty (SABMap t₀ Xo.univ.t y.x) → Nonempty (SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) → ∀ (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ t : 𝓞 E →+* 𝓞 K, (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → (Function.support ρ).Finite ∧ lineDeg s.cInf ρ = ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act t) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act (t.comp (H.bar : 𝓞 E →+* 𝓞 E))) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s ρ hρ K _ _ _ y hy B t₀ hm1 hm2 F h hh t ht
  obtain ⟨m1⟩ := hm1
  obtain ⟨m2⟩ := hm2
  obtain ⟨π, ε, hπ, -⟩ := GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm c.F K (algebraMap c.F K)
  have ht' := GlobalTheory.T.hostIntegerCharacter_comp_conj_eq_conjEmbedding E H Dw l Xo c τ K t ht
  obtain ⟨u, hu, hui, hus⟩ := GlobalTheory.T.exists_frameCoords_basis_eigenLattice_span E H Dw l Xo c K y B t₀ m1 m2 F τ.1 t ht
  obtain ⟨u', hu', hui', hus'⟩ := GlobalTheory.T.exists_frameCoords_basis_eigenLattice_span E H Dw l Xo c K y B t₀ m1 m2 F (conjEmb τ.1) _ ht'
  have hfin := GlobalTheory.T.flatSection_constValuation_eigenLattice_at_prime E H Dw l Xo c r U x hL Z τ s ρ hρ K y hy B t₀ m1 m2 F t ht π ε hπ u u' hu hu'
  have hlat := GlobalTheory.T.degree_determinant_line_two_hermitianLattices K h _ _ (GlobalTheory.CM.DegBound.eigLat_fg F _ _) (GlobalTheory.CM.DegBound.eigLat_fg F _ _) u u' hui hus hui'
    hus' _ (GlobalTheory.T.flatSection_ne_zero_at_numberField_point E H Dw l Xo c r U x hL Z τ s K y hy) (fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)) hfin
  have harch := GlobalTheory.T.constLengthFlatSection_eq_frameNorm_complexEmbedding E H Dw l Xo c r U x hL Z τ s K y hy B t₀ m1 m2 F h hh u u' hu hu'
  obtain ⟨hf, hd⟩ := GlobalTheory.T.adelicLine_degree_invariant_finite_extension c.F K π ε hπ s.cInf ρ hlat.1
  refine ⟨hf, hd.trans ?_⟩
  rw [← hlat.2]
  congr 1
  funext σ
  exact harch σ

end GlobalTheory.PtDeg
