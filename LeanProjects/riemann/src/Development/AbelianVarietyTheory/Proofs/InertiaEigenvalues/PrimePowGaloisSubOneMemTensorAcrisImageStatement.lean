import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowGaloisSubOneMemTensorAcrisImage
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_galois_sub_one_mem_tensorAcris_image : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (c : ℕ), (l : K) ^ c • D.conn σ.1 ∈ D.MM → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ z : ι → OCr l O, (l : O) ^ c • (actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) - R.jB (toBcris t ϖ D.toPhiMod σ)) = R.jB fun i => toOB l O (z i) := by
  first | exact @GlobalTheory.GalTaylor.lpow_galDiff_eq_jB_toOB | exact GlobalTheory.GalTaylor.lpow_galDiff_eq_jB_toOB | (intros; apply GlobalTheory.GalTaylor.lpow_galDiff_eq_jB_toOB <;> assumption)
