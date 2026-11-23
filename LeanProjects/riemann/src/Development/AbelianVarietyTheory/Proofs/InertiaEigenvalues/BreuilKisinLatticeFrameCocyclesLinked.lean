import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.LinkCocycle

theorem dvd_of_inclW {l : ℕ} [Fact l.Prime] (n : ℕ) : ∀ (a : Ainf l) (w : WCb l),
    inclW l a = (l : WCb l) ^ n * w → (l : Ainf l) ^ n ∣ a := by
  induction n with
  | zero => intro a w _; exact ⟨a, by simp⟩
  | succ n ih =>
    intro a w h
    obtain ⟨a₁, ha₁⟩ := GlobalTheory.HWL.TensorWitt.ainf_saturated_in_tiltWitt_prime a ((l : WCb l) ^ n * w) (by rw [h]; ring)
    obtain ⟨c, hc⟩ := ih a₁ w ha₁
    have h1 : a = (l : Ainf l) * a₁ := GlobalTheory.HWL.TensorWitt.inclW_injective (by
      rw [map_mul, map_natCast, ha₁, h]; ring)
    exact ⟨c, by rw [h1, hc]; ring⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N N' d d' n : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Frame bk N d ρ) (F' : Frame bk N' d' ρ') (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])) (R : Matrix (Fin d) (Fin d') (bk.S)), (∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j) → (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) → ∀ (g : ↥(GK K)) i j, (l : Ainf l) ^ n ∣ (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g) i j := by
  intro l _ K bk N N' d d' n ρ ρ' F F' Pi R hPi hR g i j
  classical
  choose M hM using hPi g
  choose D hD using hR
  set c : WCb l := (l : WCb l) ^ n with hc
  set σ : WCb l →+* WCb l := ((galW l (g : GQ l) : WCb l ≃ₐ[ℤ_[l]] WCb l) : WCb l →+* WCb l) with hσ
  set T := F.T
  set T' := F'.T
  set P := zW Pi
  set A := zW (ρ g)
  set A' := zW (ρ' g)
  set Rw := (R.map bk.ev).map (inclW l)
  set Rgw := ((R.map bk.ev).map (Per.σA (g : GQ l))).map (inclW l)
  set E := (F.ε g).map (inclW l)
  set E' := (F'.ε g).map (inclW l)
  set Ds : Matrix (Fin d) (Fin d') (WCb l) := Matrix.of D
  set Mw : Matrix (Fin d) (Fin d') (WCb l) := zW (Matrix.of M)
  have e1 : A * T.map σ = T * E := F.gal g
  have e2 : A' * T'.map σ = T' * E' := F'.gal g
  have e3 : P * T' - T * Rw = c • Ds := Matrix.ext fun i j => by
    simpa [Ds, Rw, BK.evW, Matrix.map_map] using hD i j
  have e4 : P * T'.map σ - T.map σ * Rgw = c • Ds.map σ := by
    have hP : P.map σ = P := Matrix.ext fun i j => by simp [P, zW, σ]
    have hRg : Rw.map σ = Rgw := Matrix.ext fun i j => by simp [Rw, Rgw, σ, galW_inclW]
    have : (P * T' - T * Rw).map σ = (c • Ds).map σ := by rw [e3]
    rw [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul] at this
    rw [hP, hRg] at this
    rw [this]; ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hc, map_pow, map_natCast]
  have e5 : P * A' - A * P = c • Mw := by
    have hM' : Pi * ρ' g - ρ g * Pi = ((l : ℤ_[l]) ^ n) • Matrix.of M := Matrix.ext fun i j => by simpa using hM i j
    have : (Pi * ρ' g - ρ g * Pi).map (algebraMap ℤ_[l] (WCb l)) = (((l : ℤ_[l]) ^ n) • Matrix.of M).map (algebraMap ℤ_[l] (WCb l)) := by rw [hM']
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul] at this
    rw [this]; ext i j; simp [Mw, zW, c]
  have key : T * (E * Rgw - Rw * E') = (c • Ds) * E' - (c • Mw) * T'.map σ - A * (c • Ds.map σ) := by
    rw [← e3, ← e4, ← e5]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T E, ← e1, ← e2]
    simp only [Matrix.mul_assoc]
    abel
  have key2 : T * (E * Rgw - Rw * E') = c • (Ds * E' - Mw * T'.map σ - A * Ds.map σ) := by
    rw [key, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_sub]
  have hT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp F.unit)
  have hX : E * Rgw - Rw * E' = c • (T⁻¹ * (Ds * E' - Mw * T'.map σ - A * Ds.map σ)) := by
    rw [← Matrix.mul_smul, ← key2, ← Matrix.mul_assoc, hT, Matrix.one_mul]
  have hY : (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g).map (inclW l) =
      E * Rgw - Rw * E' := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul]
  refine dvd_of_inclW n _ ((T⁻¹ * (Ds * E' - Mw * T'.map σ - A * Ds.map σ)) i j) ?_
  have := congrFun (congrFun (hY.trans hX) i) j
  simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hc] using this
end GlobalTheory.BKLim.LinkCocycle
