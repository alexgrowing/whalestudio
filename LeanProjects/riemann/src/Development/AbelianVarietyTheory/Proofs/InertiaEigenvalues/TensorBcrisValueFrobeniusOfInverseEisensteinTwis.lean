import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToBcrisPhi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitToBFrobEis

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.PhiVal

theorem isCrisVal_phi : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (hφ : D.phi y ∈ D.MMl), IsCrisVal t ϖ D.toPhiMod jB (phiW t ϖ D.toPhiMod (toW t ϖ D.toPhiMod ⟨y, hy⟩)) (jB (toBcris t ϖ D.toPhiMod ⟨D.phi y, hφ⟩)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T jB y hY hy hφ
  have hEM : ∀ τ i, E K l e ^ η * y τ i ∈ A O K := fun τ i => mem_tot.1 ((Descent.mem_invOf _).1 hY).1 τ i
  let g : ι → ZMod a → A O K := fun i τ => ⟨E K l e ^ η * y τ i, hEM τ i⟩
  let m : OA l O := frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ η
  refine ⟨m, fun i => frobOA l O (ϖ.iTot t K (g i)), ?_, ?_, ?_⟩
  · rw [map_pow]
    exact (FrobEis.isUnit_toB_frob_eis l a e O ϖ).pow η
  · let EW : ZMod a → invE l e (A O K) := fun _ => ⟨(EIn l e (A O K) : K⟦X⟧), le_away _ _ (EIn l e (A O K)).2⟩
    have h2 : ϖ.iW t K EW = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) :=
      (ϖ.iW_of_mem t K (fun _ => EIn l e (A O K))).trans (congrArg _ (ϖ.iTot_E t K))
    have hA : ∀ i, inclO l O m * frobOW l O (toW t ϖ D.toPhiMod ⟨y, hy⟩ i) =
        inclO l O (frobOA l O (ϖ.iTot t K (g i))) := by
      intro i
      have h1 : ϖ.iW t K (fun τ => ⟨(g i τ : K⟦X⟧), le_away _ _ (g i τ).2⟩) =
          ϖ.iW t K EW ^ η * ϖ.iW t K (fun τ => ⟨y τ i, mem_tot.1 hy τ i⟩) := by
        rw [← map_pow, ← map_mul]
        congr 1
      rw [← frobOW_inclO, ← ϖ.iW_of_mem t K, h1, map_mul, h2, toW_apply, map_pow (inclO l O), map_pow (frobOW l O),
        frobOW_inclO]
    rw [phiW_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    rw [Pi.smul_apply, smul_eq_mul, hA i]
  · rw [← LinearEquiv.map_smul]
    congr 1
    funext i
    rw [Pi.smul_apply, smul_eq_mul, toBcris_apply]
    let liftA : (ZMod a → A O K) → ZMod a → invL l (S O K e) :=
      fun F τ => ⟨F τ, le_away _ _ (A_le_S l e (F τ).2)⟩
    have key : liftA (frobAc l fun _ => EIn l e (A O K)) ^ η * coordL D.toPhiMod (invL l (S O K e)) ⟨D.phi y, hφ⟩ i =
        liftA (frobAc l (g i)) := by
      funext τ
      apply Subtype.ext
      have h1 : (coordL D.toPhiMod (invL l (S O K e)) ⟨D.phi y, hφ⟩ i τ : K⟦X⟧) = frob K l (y (τ - 1) i) := by
        change (D.mxInv τ *ᵥ D.phi y τ) i = _
        rw [PhiMod.phi_apply, Matrix.mulVec_mulVec, PhiMod.mxInv_mul_mx, Matrix.one_mulVec, frobV_apply]
      simp only [liftA, Pi.mul_apply, Pi.pow_apply, Subalgebra.coe_mul, Subalgebra.coe_pow, h1, coe_frobAc,
        frobTot_apply, g, map_mul, map_pow]
      rfl
    have h3 := congrArg (ϖ.iB t K) key
    simp only [map_mul, map_pow, liftA, FrobCoord.iB_of_A, ϖ.iTot_frob t K, ϖ.iTot_E t K] at h3
    rw [← h3, map_pow]

end GlobalTheory.BKGal.PhiVal
