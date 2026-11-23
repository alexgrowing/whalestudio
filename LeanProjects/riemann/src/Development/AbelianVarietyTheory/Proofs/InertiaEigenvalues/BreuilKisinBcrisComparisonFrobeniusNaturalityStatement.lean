import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturality
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), (∃ jB, IsCrisCmp I jB) ∧ ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → (∀ (m m' : P.MMl), m'.1 = P.phi m.1 → jB (toBcris t ϖ P m') = TWmap (frobOB l O) T (jB (toBcris t ϖ P m))) ∧ (∀ w b b', IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ P jB w b' → b = b') ∧ (∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ P jB (phiW t ϖ P w) (TWmap (frobOB l O) T b)) ∧ (∀ x : ↥T.L.T, IsCrisVal t ϖ P jB (I.ofT x) ((1 : OB l O) ⊗ₜ[O] x)) ∧ (∀ g : Gl l, (∀ v ∈ LA t ϖ P, I.act (sQ l g) g v ∈ LA t ϖ P) → ∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ P jB (I.act (sQ l g) g w) (actB (sQ l) T g b)) := by
  first | exact @GlobalTheory.CrisComparison.main | exact GlobalTheory.CrisComparison.main | (intros; apply GlobalTheory.CrisComparison.main <;> assumption)
