import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdaptedBasisThetaGaloisFixedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BKLim.Lower

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem evW_E_ne_zero (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) : bk.evW bk.E ≠ 0 := by
  intro h
  have h0 : bk.ev bk.E = 0 := inclW_injective (h.trans (map_zero _).symm)
  have hu := (GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1
  have h1 := hτ.1
  rw [h0, zero_mul] at h1
  have h2 := (hu.map (frobW l)).ne_zero
  rw [frobW_inclW, h1, map_zero] at h2
  exact h2 rfl

theorem map_smul' {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S) (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

def raise (bk : BK K) {N d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} (F : Frame bk N d ρ) (k : ℕ) :
    Frame bk (N + k) d ρ where
  T := F.T
  unit := F.unit
  A := bk.E ^ k • F.A
  A' := bk.E ^ k • F.A'
  A_mul := by
    rw [Matrix.smul_mul, Matrix.mul_smul, F.A_mul, smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2; ring
  φ := by
    rw [map_smul', Matrix.mul_smul, ← F.φ, smul_smul, ← map_pow, ← map_pow, ← map_mul, ← pow_add, add_comm]
  fix := F.fix
  ε := F.ε
  gal := F.gal

def lower (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {N₀ k d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    (F : Frame bk (N₀ + k) d ρ) (A₀ A₀' : Matrix (Fin d) (Fin d) bk.S) (hA : F.A = bk.E ^ k • A₀)
    (hA' : F.A' = bk.E ^ k • A₀') : Frame bk N₀ d ρ where
  T := F.T
  unit := F.unit
  A := A₀
  A' := A₀'
  A_mul := by
    have h := F.A_mul
    rw [hA, hA', Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h
    refine Matrix.ext fun i j => ?_
    have h2 := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at h2 ⊢
    have hE : bk.E ^ k * bk.E ^ k ≠ 0 := mul_ne_zero (pow_ne_zero _ bk.E_ne_zero) (pow_ne_zero _ bk.E_ne_zero)
    apply mul_left_cancel₀ hE
    rw [h2]; ring
  φ := by
    have h := F.φ
    rw [hA, map_smul', Matrix.mul_smul] at h
    refine Matrix.ext fun i j => ?_
    have h2 := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at h2 ⊢
    have hE : bk.evW (bk.E ^ k) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ (evW_E_ne_zero bk hτ)
    apply mul_left_cancel₀ hE
    rw [← h2, map_pow]; ring
  fix := F.fix
  ε := F.ε
  gal := F.gal

theorem exists_frame_of_jumps_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l), C.InvdR → ∀ (N N₀ d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ), F.IsDR → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, (∀ i, |(H.p i : ℤ) - H.q| ≤ N₀) → ∃ F₀ : Frame bk N₀ d ρ, F₀.T = F.T ∧ F₀.ε = F.ε := by
  intro l _ K bk τ hτ C hC N N₀ d ρ F hF H hH
  rcases le_total N N₀ with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact ⟨raise bk F k, rfl, rfl⟩
  · obtain ⟨Y, Y', hY, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d ρ F.toPre
    obtain ⟨hdA, hdA'⟩ := (GlobalTheory.T.adaptedBasis_theta_galoisFixed_poles l K bk τ hτ C hC N d ρ F Y hF hY H).2 N₀ h hH
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left] at hdA hdA'
    choose A₀ hA₀ using hdA
    choose A₀' hA₀' using hdA'
    refine ⟨lower bk hτ F (Matrix.of A₀) (Matrix.of A₀') ?_ ?_, rfl, rfl⟩
    · ext i j; simp [hA₀ i j]
    · ext i j; simp [hA₀' i j]

end GlobalTheory.BKLim.Lower
