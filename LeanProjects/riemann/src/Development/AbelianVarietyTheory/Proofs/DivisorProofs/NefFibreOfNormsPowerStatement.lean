import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefFibreOfNormsPower
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_fibre_of_norms_power : Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (A : Adl (cxSt F) Y), A.NefFib → ∀ (V : Cover Y) (L : HermLB V.p) (k : ℕ), 0 < k → Norms V L (fun x => genAt A.D x ^ k) (fun σ y => k * lnAdl A σ y) (fun v e y => k * A.lg v e y) → NefFib L := by
  first | exact @GlobalTheory.CoverNef.nefFib_of_norms_adl | exact GlobalTheory.CoverNef.nefFib_of_norms_adl | (intros; apply GlobalTheory.CoverNef.nefFib_of_norms_adl <;> assumption)
