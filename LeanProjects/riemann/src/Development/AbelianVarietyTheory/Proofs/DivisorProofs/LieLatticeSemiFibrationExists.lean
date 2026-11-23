import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeNumberFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeFieldUniformBaseStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.HeightParts

namespace GlobalTheory.HeightParts

theorem lieLat_torusExt_at_boundary : Hypotheses2 → HypothesesH → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated → OnObj fun D O _ _ H _ => ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
  ∀ y : Pt O.s, y ∉ H.int → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K))
    (h : HermFam K (Fin (D.R.f * O.N) → K)), IsLieAt O y K L h ∧
    ∃ (F : SemiFib K) (h' : HermFam K (Fin F.P₀.g → K)) (r : ℕ) (ε : Fin r → Fin (D.R.f * O.N) → K)
      (q : (Fin (D.R.f * O.N) → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h' ∧ TorusExt h L ε q h' F.lieLat C := by
  intro p2 pH ts D O hc hN A T H hr
  obtain ⟨x, P, hxP⟩ := id hc
  obtain ⟨C₀, h₀⟩ := GlobalTheory.T.lie_lattice_field_uniform_base p2 pH ts D O hc hN A T H hr x P hxP
  refine ⟨C₀, fun C hC y hy => ?_⟩
  obtain ⟨K₀, i1, i2, io₀, hK⟩ := h₀ y hy
  obtain ⟨K, i3, i4, io, j, L, h, hj, hL⟩ := GlobalTheory.T.lie_lattice_number_field_extension p2 pH D O x P hxP y K₀ io₀
  obtain ⟨F, h', r, ε, q, hF, hE⟩ := hK K io j hj L h hL
  exact ⟨K, i3, i4, L, h, hL.isLieAt, F, h', r, ε, q, hF, torusExt_mono hE hC⟩

end GlobalTheory.HeightParts
