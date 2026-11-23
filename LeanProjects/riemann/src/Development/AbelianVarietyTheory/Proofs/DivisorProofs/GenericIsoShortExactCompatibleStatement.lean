import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoShortExactCompatible
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_iso_short_exact_compatible : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (Z : GlobalTheory.Vert.Model O) (E₁ E₂ E₃ E₁' E₂' E₃' : Z.X.Modules) (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (a' : E₁' ⟶ E₂') (b' : E₂' ⟶ E₃') (h : a ≫ b = 0) (h' : a' ≫ b' = 0), (ShortComplex.mk a b h).ShortExact → (ShortComplex.mk a' b' h').ShortExact → ∀ (ψ₁ : E₁' ⟶ E₁) (ψ₂ : E₂' ⟶ E₂) (ψ₃ : E₃' ⟶ E₃), ψ₁ ≫ a = a' ≫ ψ₂ → ψ₂ ≫ b = b' ≫ ψ₃ → ∀ (φ₁ : Z.GenIso E₁ E₁') (φ₂ : Z.GenIso E₂ E₂') (φ₃ : Z.GenIso E₃ E₃'), φ₁.inv = Z.genRes.map ψ₁ → φ₂.inv = Z.genRes.map ψ₂ → φ₃.inv = Z.genRes.map ψ₃ → ∀ (r₁ r₂ r₃ : ℕ), r₂ = r₁ + r₃ → ∀ (F₁ : GlobalTheory.Vert.Model.FlagPair φ₁ r₁) (F₃ : GlobalTheory.Vert.Model.FlagPair φ₃ r₃), ∃ F₂ : GlobalTheory.Vert.Model.FlagPair φ₂ r₂, ∀ (k : ℕ) (Q : PicSym Z.X), ck (F₂.toFPair p) k Q = ck (F₁.toFPair p) k Q + ck (F₃.toFPair p) k Q := by
  first | exact @GlobalTheory.Concat.exists_flagPair_ck_add | exact GlobalTheory.Concat.exists_flagPair_ck_add | (intros; apply GlobalTheory.Concat.exists_flagPair_ck_add <;> assumption)
