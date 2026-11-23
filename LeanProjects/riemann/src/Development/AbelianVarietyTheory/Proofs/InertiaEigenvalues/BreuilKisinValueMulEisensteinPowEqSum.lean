import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

namespace GlobalTheory.BKGal.HatVal

theorem value_mul_E_pow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod) (b₂ : TW (OB l O) T), IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∀ Y : ι → ZMod a → A O K, (∀ j τ, (Y j τ : K⟦X⟧) = E K l e ^ η * y τ j) → toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • b₂ = ∑ j, toB l O (ϖ.iTot t K (Y j)) • R.jB (fun i => toB l O (c j i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hy b₂ hval c hc Y hY
  obtain ⟨m, c', hu, hmc, hmb⟩ := hval
  set E0 : OA l O := ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) with hE0
  have hEW : ϖ.iW t K (fun _ => EIn l e (invE l e (A O K))) = inclO l O E0 := by
    rw [hE0, ← ϖ.iTot_E t K, ← ϖ.iW_of_mem t K]
    rfl
  have hYi : ∀ i, inclO l O (ϖ.iTot t K (Y i)) = inclO l O E0 ^ η * toW t ϖ D.toPhiMod ⟨y, hy⟩ i := by
    intro i
    rw [← ϖ.iW_of_mem t K, toW_apply, ← hEW, ← map_pow, ← map_mul]
    congr 1
    funext τ
    apply Subtype.ext
    simp [hY, EIn]
  set S : ι → OA l O := fun i => ∑ j, ϖ.iTot t K (Y j) * c j i with hSdef
  have hS : inclL t ϖ D.toPhiMod S = inclO l O (E0 ^ (H + η)) • toW t ϖ D.toPhiMod ⟨y, hy⟩ := by
    have h1 : S = ∑ j, fun i => ϖ.iTot t K (Y j) * c j i := by
      funext i; simp [hSdef, Finset.sum_apply]
    rw [h1, map_sum]
    simp only [inclL_smul_coord, hc]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hYi i, pow_add]
    simp only [map_mul, map_pow]
    ring
  have hkey : (fun i => m * S i) = fun i => E0 ^ (H + η) * c' i := by
    apply inclL_injective t ϖ D.toPhiMod
    rw [inclL_smul_coord, inclL_smul_coord, hS, ← hmc, smul_smul, smul_smul, mul_comm]
  have h2 := congrArg (fun v : ι → OA l O => R.jB fun i => toB l O (v i)) hkey
  have hL : (fun i => toB l O (m * S i)) = toB l O m • ∑ j, toB l O (ϖ.iTot t K (Y j)) • fun i => toB l O (c j i) := by
    funext i
    simp [hSdef, Finset.sum_apply, Finset.mul_sum, map_sum]
  have hR : (fun i => toB l O (E0 ^ (H + η) * c' i)) = toB l O E0 ^ (H + η) • fun i => toB l O (c' i) := by
    funext i
    simp
  rw [hL, hR, map_smul, map_smul, ← hmb, map_sum] at h2
  simp only [map_smul] at h2
  rw [smul_smul, mul_comm, ← smul_smul] at h2
  exact (hu.smul_left_cancel).1 h2.symm

end GlobalTheory.BKGal.HatVal
