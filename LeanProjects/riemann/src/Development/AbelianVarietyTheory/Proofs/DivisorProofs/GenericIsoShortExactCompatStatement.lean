import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoShortExactCompat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoDivisorClassIsoInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsFrame Chart det)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_iso_short_exact_compat : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : GlobalTheory.Vert.Model O} {S S' : ShortComplex Z.X.Modules} (hS : S.ShortExact) (hS' : S'.ShortExact) {r s : ℕ} [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] [S'.X₁.IsQuasicoherent] [S'.X₂.IsQuasicoherent] [S'.X₃.IsQuasicoherent] (g₁ : Z.GenIso S.X₁ S'.X₁) (g₂ : Z.GenIso S.X₂ S'.X₂) (g₃ : Z.GenIso S.X₃ S'.X₃), g₁.hom ≫ Z.genRes.map S'.f = Z.genRes.map S.f ≫ g₂.hom → g₂.hom ≫ Z.genRes.map S'.g = Z.genRes.map S.g ≫ g₃.hom → ∀ (a : GlobalTheory.VBExt.AdaptedChart S r s) (a' : GlobalTheory.VBExt.AdaptedChart S' r s) {T : Z.gen.toScheme.Opens} (h : T ≤ Z.gen.ι ⁻¹ᵁ (a.U ⊓ a'.U)), g₂.detUnit (a.mid hS) (a'.mid hS') h = g₁.detUnit a.sub a'.sub h * g₃.detUnit a.quot a'.quot h := by
  first | exact @GlobalTheory.VBExt.genIso_detUnit_mid | exact GlobalTheory.VBExt.genIso_detUnit_mid | (intros; apply GlobalTheory.VBExt.genIso_detUnit_mid <;> assumption)
