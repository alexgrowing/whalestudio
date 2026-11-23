import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverNormsPullbackPower
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_norms_pullback_power : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → ∀ (V : Cover Y) (b : V.X ⟶ M.X) (hb : b ≫ M.p = V.p), V.j ≫ b = V.π ≫ M.j → Norms V (L.pull b hb) (fun x => genAt A.D x ^ (k : ℕ)) (fun σ y => ((k : ℕ) : ℝ) * lnAdl A σ y) (fun v e y => ((k : ℕ) : ℝ) * A.lg v e y + ((k : ℕ) : ℝ) * ((A.n : ℕ) : ℝ) * cf v) := by
  first | exact @GlobalTheory.CoverNorm.norms_pull_of_induced | exact GlobalTheory.CoverNorm.norms_pull_of_induced | (intros; apply GlobalTheory.CoverNorm.norms_pull_of_induced <;> assumption)
