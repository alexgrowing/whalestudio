import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationEmbeddingHeightsPlace
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteTwistingNotIsGenerator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticMixedVolumeParameterMaxTwo
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

theorem _root_.GlobalTheory.T.valuation_embedding_heights_place : GlobalTheory.Published.RegularAlteration → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    UnramE D p → p ∉ O.Y.lev → ∀ (W : Formalism.L2.Geo.PlL D p → ValuationSubring ℂ) (hW : ∀ la, (p : ℂ) ∈ (W la).nonunits)
    (jc : Formalism.L2.Geo.PlL D p → (KW p →+* ℂ)), (∀ la, Pin (W la) (jc la)) →
    (∀ la (x : D.what₂.LL), D.what₂.embLL x ∈ W la ↔ IsDedekindDomain.HeightOneSpectrum.valuation D.what₂.LL la.1 x ≤ 1) →
    ∀ (z : ∀ la, AdmAt O.S O.κ (Fact.out : p.Prime) (hW la)) (Sx : Finset ℕ) (R : ℝ), 2 ≤ R →
    ∀ (τ0 : D.what₂.Tau) (τ' : Formalism.L2.Geo.PlL D p → Emb D p), (∀ la, (jc la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin (rkOf (PsiOf D (jc la)) O.Y.N O.Y.j (τ' la))) (i' : Fin O.Y.N), (∀ la, (i' : ℕ) = i la) →
    ∀ G : MvPolynomial (Vm D.what₂.Tau O.Y.N) ℚ, G.IsWeightedHomogeneous (wt D.what₂.Tau O.Y.N) (dimFl D.what₂.Tau O.Y.N) →
      O.Y.arMix Sx R p (dRt D.what₂.Tau O.Y.N (τ0, i') * toR G) = Real.log p * (letI := Formalism.L2.Geo.finPl D p;
        ∑ la, Formalism.L2.Geo.wtL D p la * ((((mdlOf (z la) (jc la)).Z.capDeg (((mdlOf (z la) (jc la)).lie (τ' la)).Dv (i la))
          (evC (mdlOf (z la) (jc la)) (rootOf (z la) (jc la)) G) : ℚ) : ℝ) / ((mdlOf (z la) (jc la)).cov : ℝ))) := by
  first | exact @GlobalTheory.VertTerm.arMix_dRt_lie | exact GlobalTheory.VertTerm.arMix_dRt_lie | (intros; apply GlobalTheory.VertTerm.arMix_dRt_lie <;> assumption)
