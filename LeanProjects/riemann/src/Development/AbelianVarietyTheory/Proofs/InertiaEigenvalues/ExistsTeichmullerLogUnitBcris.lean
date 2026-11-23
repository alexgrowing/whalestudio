import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisEqZeroOfForallDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisLogOneAddStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAcrisLogOneAddAddOfMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUnitTeichmullerPrincipalUnitSplitStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LogU
open GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem isLogJ_pow {e : Per.Fl l} (hJ : InJ (Per.tm e - 1)) {y : Per.Acris l} (hy : IsLogJ (Per.tm e - 1) y) :
    ∀ m : ℕ, IsLogJ (Per.tm (e ^ m) - 1) ((m : Per.Acris l) * y)
  | 0 => by simpa using (isLogJ_zero : IsLogJ (l := l) 0 0)
  | m + 1 => by
    have h := GlobalTheory.T.isAcrisLogOneAdd_add_of_mul l _ _ _ _ (inJ_pow hJ m) hJ (isLogJ_pow hJ hy m) hy
    have e1 : Per.tm (e ^ (m + 1)) - 1 = (Per.tm (e ^ m) - 1) + (Per.tm e - 1) +
        (Per.tm (e ^ m) - 1) * (Per.tm e - 1) := by
      rw [pow_succ, show Per.tm (e ^ m * e) = Per.tm (e ^ m) * Per.tm e from
        map_mul (WittVector.teichmuller l) _ _]
      ring
    rw [e1]
    convert h using 1
    push_cast
    ring

theorem iter_mul (a b : Per.Fl l) (m : ℕ) : ((frobeniusEquiv (Per.Fl l) l).symm)^[m] (a * b) =
    ((frobeniusEquiv (Per.Fl l) l).symm)^[m] a * ((frobeniusEquiv (Per.Fl l) l).symm)^[m] b := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]

theorem iter_one (m : ℕ) : ((frobeniusEquiv (Per.Fl l) l).symm)^[m] 1 = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_one]

theorem rootT_mul (a b : Per.Fl l) (m : ℕ) : rootT (a * b) m = rootT a m * rootT b m := by
  simp only [rootT, iter_mul, map_mul]

theorem rootT_one (m : ℕ) : rootT (1 : Per.Fl l) m = 1 := by
  simp only [rootT, iter_one, map_one]

theorem exists_gal_log (C : Core l) (x : Per.Fl l) (hx : IsUnit x) (g : GQ l) (c : ℤ_[l])
    (H : ∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) :
    ∃ e : Per.Fl l, e.untilt = 1 ∧ Per.σF g x = x * e ∧
      IsLogA e (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c) * C.t) := by
  obtain ⟨v, hv⟩ := hx.exists_left_inv
  have hxe : Per.σF g x = x * (v * Per.σF g x) := by rw [← mul_assoc, mul_comm x v, hv, one_mul]
  have hre : ∀ m, rootT (v * Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val := by
    intro m
    have hu : IsUnit (rootT x m) := by
      have h1 := congrArg (fun z => rootT z m) hv
      simp only [rootT_mul, rootT_one] at h1
      exact ⟨⟨rootT x m, rootT v m, by rw [mul_comm]; exact h1, h1⟩, rfl⟩
    apply hu.mul_left_cancel
    rw [← rootT_mul, ← hxe, H m, mul_comm]
  have he1 : (v * Per.σF g x).untilt = 1 := by
    have := hre 0
    simp only [rootT, Function.iterate_zero, id] at this
    rw [this, TAct.eps_untilt C, one_pow]
  have hr : ∀ m, (rootT (v * Per.σF g x) m : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] (C.ζ m ^ (PadicInt.toZModPow m c).val) := by
    intro m
    rw [hre m, SubmonoidClass.coe_pow, C.ε_root m, map_pow]
  obtain ⟨y, hy⟩ := Model.exists_isLogA he1
  exact ⟨_, he1, hxe, GlobalTheory.Pst.NoLog.log_eq C _ c y hr hy ▸ hy⟩

theorem map_inv_units {R : Type} [CommRing R] (f : R →+* R) (u : Rˣ) (h : f u = u) :
    f (↑u⁻¹ : R) = ↑u⁻¹ := by
  have h1 := congrArg f (Units.inv_mul u)
  rw [map_mul, h, map_one] at h1
  calc f (↑u⁻¹ : R) = f ↑u⁻¹ * (↑u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = ↑u⁻¹ := by rw [← mul_assoc, h1, one_mul]

theorem exists_log_unit : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : OCb l), IsUnit x → ∃ b : Per.Bcris l, Per.φB l b = (l : Per.Bcris l) * b ∧ ∀ (g : GQ l) (c : ℤ_[l]), (∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) → Per.σB g b = b + Per.zB l c * C.tB := by
  intro l _ C x hx
  obtain ⟨ω, x₁, N, hxω, hJ, hω⟩ := GlobalTheory.T.tilt_unit_teichmuller_principal_unit_split l x hx
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_acris_log_one_add l _ hJ
  have hpow := isLogJ_pow hJ hy
  obtain ⟨u, hu⟩ := (isUnit_l_Bcris l).pow N
  have hωu : IsUnit ω := isUnit_of_mul_isUnit_left (hxω ▸ hx)
  refine ⟨↑u⁻¹ * algebraMap (Per.Acris l) (Per.Bcris l) y, ?_, fun g c H => ?_⟩
  · have h2 := isLogJ_extends (GlobalTheory.CrisMaps.phiA_extends l) hy
    have h3 : Per.φA l (Per.tm (x₁ ^ l ^ N) - 1) = Per.tm ((x₁ ^ l ^ N) ^ l) - 1 := by
      rw [map_sub, map_one, show Per.φA l (Per.tm (x₁ ^ l ^ N)) = Per.tm ((x₁ ^ l ^ N) ^ l) from
        GlobalTheory.RingIface.phiA_teich l _]
    rw [h3] at h2
    have h1 : GlobalTheory.MemLoc.phiA l y = (l : Per.Acris l) * y := isLogJ_unique h2 (hpow l)
    have hφY : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) y) =
        (l : Per.Bcris l) * algebraMap (Per.Acris l) (Per.Bcris l) y := by
      have : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) y) =
          algebraMap _ _ (GlobalTheory.MemLoc.phiA l y) :=
        GlobalTheory.CrisMaps.φB_phiA l y
      rw [this, h1, map_mul, map_natCast]
    have hφu : Per.φB l (↑u⁻¹ : Per.Bcris l) = ↑u⁻¹ :=
      map_inv_units _ u (by rw [hu, map_pow, map_natCast])
    rw [map_mul, hφu, hφY]
    ring
  · obtain ⟨e, he1, hgx, hle⟩ := exists_gal_log C x hx g c H
    have hgω : Per.σF g ω = ω := hω g e he1 hgx
    have hgx₁ : Per.σF g x₁ = x₁ * e := by
      apply hωu.mul_left_cancel
      rw [← mul_assoc, ← hxω, ← hgx, hxω, map_mul, hgω]
    have hge₁ : Per.σF g (x₁ ^ l ^ N) = x₁ ^ l ^ N * e ^ l ^ N := by rw [map_pow, hgx₁, mul_pow]
    have hle' := TAct.logA_pow C.j_cris he1 hle (l ^ N)
    have hsum := GlobalTheory.T.isAcrisLogOneAdd_add_of_mul l _ _ _ _ hJ (inJ_mu (e := e ^ l ^ N) (by rw [map_pow, he1, one_pow])) hy hle'
    have hσ := isLogJ_extends (GlobalTheory.CrisMaps.sigA_extends g) hy
    have hw : Per.σA g (Per.tm (x₁ ^ l ^ N) - 1) = (Per.tm (x₁ ^ l ^ N) - 1) + mu (e ^ l ^ N) +
        (Per.tm (x₁ ^ l ^ N) - 1) * mu (e ^ l ^ N) := by
      rw [map_sub, map_one, show Per.σA g (Per.tm (x₁ ^ l ^ N)) = Per.tm (Per.σF g (x₁ ^ l ^ N)) from
        GlobalTheory.RingIface.sigA_teich l g _, hge₁, mu,
        show Per.tm (x₁ ^ l ^ N * e ^ l ^ N) = Per.tm (x₁ ^ l ^ N) * Per.tm (e ^ l ^ N) from
        map_mul (WittVector.teichmuller l) _ _]
      ring
    rw [hw] at hσ
    have hy' := isLogJ_unique hσ hsum
    have hσY : Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) y) =
        algebraMap _ _ (GlobalTheory.MemLoc.sigA g y) :=
      GlobalTheory.CrisMaps.σB_sigA g y
    have hσu : Per.σB g (↑u⁻¹ : Per.Bcris l) = ↑u⁻¹ :=
      map_inv_units _ u (by rw [hu, map_pow, map_natCast])
    have hul : (↑u⁻¹ : Per.Bcris l) * ((l ^ N : ℕ) : Per.Bcris l) = 1 := by
      rw [Nat.cast_pow, ← hu, Units.inv_mul]
    rw [map_mul, hσu, hσY, hy', map_add, map_mul, map_mul, map_natCast]
    rw [GlobalTheory.RingIface.zB_eq_aB_zA l c, GlobalTheory.RingIface.aB_eq_alg l (Per.zA l c)]
    simp only [Core.tB]
    linear_combination (algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c)) *
      algebraMap (Per.Acris l) (Per.Bcris l) C.t) * hul

end GlobalTheory.LogU
