import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAdelicMetricDivisorRelation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_adelic_metric_divisor_relation : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (ι : Type) [Fintype ι] (Mb : Adl (cxSt F) Y) (ρ : ι → Adl (cxSt F) Y) (q : ℕ) (b : ι → ℤ) (σ : F →+* ℂ) (z : Pts Y σ) (gz : ℝ) (fM : Y.Fn) (f : ι → Y.Fn), PosAt (Mb.m σ) z → (∀ i, PosAt ((ρ i).m σ) z) → (q : ℝ) * lnAdl Mb σ z = Real.log ‖ratVal (genAt Mb.D (under z) ^ q / ∏ i, genAt (ρ i).D (under z) ^ b i) z‖ + ∑ i, (b i : ℝ) * lnAdl (ρ i) σ z - q * ((Mb.n : ℕ) : ℝ) * gz → Mb.D.GeneratesAt (under z) fM → (∀ i, (ρ i).D.GeneratesAt (under z) (f i)) → UnitAt (under z) (genAt Mb.D (under z) ^ q / ∏ i, genAt (ρ i).D (under z) ^ b i) → UnitAt (under z) (fM ^ q / ∏ i, f i ^ b i) → (q : ℝ) * lnN (Mb.m σ) fM z = Real.log ‖ratVal (fM ^ q / ∏ i, f i ^ b i) z‖ + ∑ i, (b i : ℝ) * lnN ((ρ i).m σ) (f i) z - q * ((Mb.n : ℕ) : ℝ) * gz + ((q : ℝ) * ((Mb.n : ℕ) : ℝ) * Mb.ci (InfinitePlace.mk σ) - ∑ i, (b i : ℝ) * (((ρ i).n : ℕ) : ℝ) * (ρ i).ci (InfinitePlace.mk σ)) := by
  first | exact @GlobalTheory.Mean4O.CombGen.lnAdl_comb_change | exact GlobalTheory.Mean4O.CombGen.lnAdl_comb_change | (intros; apply GlobalTheory.Mean4O.CombGen.lnAdl_comb_change <;> assumption)
