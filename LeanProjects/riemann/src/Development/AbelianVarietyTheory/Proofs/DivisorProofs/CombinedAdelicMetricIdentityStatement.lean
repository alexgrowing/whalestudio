import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedAdelicMetricIdentity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeightSmoothNormalizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsUnitRescalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.combined_adelic_metric_identity : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (M : Adl (cxSt F) Y) (ι : Type) [Fintype ι] (ρ : ι → Adl (cxSt F) Y) (g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (q : ℕ) (b : ι → ℤ), 0 < q → q • M.D = ∑ i, b i • (ρ i).D → (∀ σ z, PosAt (M.m σ) z ∧ q * lnAdl M σ z = Real.log ‖ratVal (genAt M.D (under z) ^ q / ∏ i, genAt (ρ i).D (under z) ^ b i) z‖ + ∑ i, b i * lnAdl (ρ i) σ z - q * (M.n : ℕ) * g σ z) → (∀ v e y, q * M.lg v e y = Real.log (e.w (valAt y.1 (genAt M.D (below y.1) ^ q / ∏ i, genAt (ρ i).D (below y.1) ^ b i))) + ∑ i, b i * (ρ i).lg v e y) → ∀ (K : ℕ) (e : ι → ℤ) (n : ι → ℤ), (∀ i, n i * e i = K * b i) → ∀ (L : ι → HermLB V.p), (∀ i, Norms V (L i) (fun x => genAt (ρ i).D x ^ e i) (fun σ y => e i * lnAdl (ρ i) σ y) (fun v e' y => e i * (ρ i).lg v e' y)) → ∀ (u : ∀ σ : 𝓞 F →+* ℂ, CxPts V.p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y) (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))), (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F))), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → u _ y' = 2 * g σ y) → Norms V (ArInt.comb (fun o : Option ι => o.elim (ArInt.fnB u hu hc) L) (fun o => o.elim (((K * q * (M.n : ℕ) : ℕ) : ℤ)) n)) (fun x => genAt M.D x ^ (K * q)) (fun σ y => ((K * q : ℕ) : ℝ) * lnAdl M σ y) (fun v e y => ((K * q : ℕ) : ℝ) * M.lg v e y) := by
  first | exact @GlobalTheory.CoverComb.approx | exact GlobalTheory.CoverComb.approx | (intros; apply GlobalTheory.CoverComb.approx <;> assumption)
