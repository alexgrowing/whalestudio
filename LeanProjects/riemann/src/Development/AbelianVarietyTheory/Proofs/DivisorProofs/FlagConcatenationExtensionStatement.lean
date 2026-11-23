import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagConcatenationExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_concatenation_extension : ∀ (X : Scheme.{0}) (E₁ E₂ E₃ : X.Modules) (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃)
    (h : a ≫ b = 0), (ShortComplex.mk a b h).ShortExact → ∀ (r₁ r₃ : ℕ)
    (fl₁ : GlobalTheory.Vert.Flag E₁ r₁) (fl₃ : GlobalTheory.Vert.Flag E₃ r₃), ∃ fl₂ : GlobalTheory.Vert.Flag E₂ (r₁ + r₃),
    (∀ (k : Fin (r₁ + r₃ + 1)) (i : Fin (r₁ + 1)), (k : ℕ) = i →
      ∃ e : fl₂.F k ≅ fl₁.F i, fl₂.ι k = e.hom ≫ fl₁.ι i ≫ a) ∧
    (∀ (k : Fin (r₁ + r₃ + 1)) (j : Fin (r₃ + 1)), (k : ℕ) = r₁ + j →
      ∃ hz : fl₂.ι k ≫ b ≫ cokernel.π (fl₃.ι j) = 0,
        (ShortComplex.mk (fl₂.ι k) (b ≫ cokernel.π (fl₃.ι j)) hz).ShortExact) ∧
    (∀ (k : Fin (r₁ + r₃)) (i : Fin r₁), (k : ℕ) = i →
      ∃ (e : fl₂.F k.succ ≅ fl₁.F i.succ) (u : fl₂.gr k ≅ fl₁.gr i),
        fl₂.ι k.succ = e.hom ≫ fl₁.ι i.succ ≫ a ∧ fl₂.π k ≫ u.hom = e.hom ≫ fl₁.π i) ∧
    (∀ (k : Fin (r₁ + r₃)) (j : Fin r₃), (k : ℕ) = r₁ + j →
      ∃ (m : fl₂.F k.succ ⟶ fl₃.F j.succ) (u : fl₂.gr k ≅ fl₃.gr j),
        m ≫ fl₃.ι j.succ = fl₂.ι k.succ ≫ b ∧ fl₂.π k ≫ u.hom = m ≫ fl₃.π j) := by
  first | exact @GlobalTheory.Vert.Flag.concat_spec | exact GlobalTheory.Vert.Flag.concat_spec | (intros; apply GlobalTheory.Vert.Flag.concat_spec <;> assumption)
