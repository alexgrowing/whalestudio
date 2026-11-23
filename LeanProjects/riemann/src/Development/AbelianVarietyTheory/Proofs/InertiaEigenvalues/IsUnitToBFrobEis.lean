import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.FrobEis

theorem factorial_pow_dvd (r : ℕ) : ∀ k : ℕ, r.factorial ^ k ∣ (k * r).factorial
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, add_mul, one_mul]
    exact (Nat.mul_dvd_mul_right (factorial_pow_dvd r k) _).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem factorial_pow_mul_dvd {l : ℕ} (hl : 1 ≤ l) : l.factorial ^ l * l ∣ (l * l).factorial := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have h1 : (k + 1) * (k + 1) = (k * (k + 1) + k) + 1 := by ring
  have h3 := (Nat.mul_dvd_mul_right (factorial_pow_dvd (k + 1) k) k.factorial).trans
    (Nat.factorial_mul_factorial_dvd_factorial_add (k * (k + 1)) k)
  have h4 : (k + 1).factorial ^ (k + 1) * (k + 1) =
      (k + 1).factorial ^ k * k.factorial * (k * (k + 1) + k + 1) := by
    rw [Nat.factorial_succ k, pow_succ]; ring
  rw [h1, Nat.factorial_succ (k * (k + 1) + k), h4, mul_comm (k * (k + 1) + k + 1)]
  exact Nat.mul_dvd_mul_right h3 _

variable {l : ℕ} [hl : Fact l.Prime]

theorem isUnit_one_add {y z : Per.Acris l} {n : ℕ} (h : y ^ n = (l : Per.Acris l) * z) : IsUnit (1 + y) := by
  have := (GlobalTheory.MemLoc.acris_torsionFree_complete l).2
  have hJ : -(-y) ^ n ∈ Ideal.jacobson (⊥ : Ideal (Per.Acris l)) := by
    refine IsAdicComplete.le_jacobson_bot (Ideal.span {((l : ℕ) : Per.Acris l)}) (Ideal.mem_span_singleton.2 ⟨-((-1) ^ n * z), ?_⟩)
    rw [neg_pow, h]; ring
  have h1 := Ideal.mem_jacobson_bot.1 hJ 1
  rw [mul_one, neg_add_eq_sub] at h1
  have h2 := mul_neg_geom_sum (-y) n
  rw [sub_neg_eq_add] at h2
  exact isUnit_of_mul_isUnit_left (h2 ▸ h1)

theorem isUnit_teich_pow_add {e : ℕ} (ϖ : PiSys l e) :
    IsUnit (acrisToBcris l (ainfToAcris l (ϖ.teich ^ (e * l) + l))) := by
  obtain ⟨d, hd⟩ := ϖ.exists_dpow_teich l
  obtain ⟨d₂, hd₂⟩ := ϖ.exists_dpow_teich (l * l)
  obtain ⟨m, hm⟩ := factorial_pow_mul_dvd hl.out.one_lt.le
  have hm' : ((l * l).factorial : Per.Acris l) = (l.factorial : Per.Acris l) ^ l * l * m := by
    rw [hm]; push_cast; ring
  have h3 : ((l.factorial : Per.Acris l) * d) ^ l = ainfToAcris l ϖ.teich ^ (e * (l * l)) := by
    rw [hd, ← pow_mul, mul_assoc]
  have hdl : d ^ l = l * (m * d₂) := by
    refine sub_eq_zero.1 (acris_nat_cancel (pow_ne_zero l l.factorial_ne_zero) ?_)
    push_cast
    linear_combination h3 - hd₂ + d₂ * hm'
  have hp : ((l.factorial : ℕ) : Per.Acris l) = l * ((l - 1).factorial : ℕ) := by
    rw [← Nat.mul_factorial_pred hl.out.ne_zero]; push_cast; ring
  have h1 : ainfToAcris l (ϖ.teich ^ (e * l) + l) = l * (1 + ((l - 1).factorial : Per.Acris l) * d) := by
    rw [map_add, map_pow, map_natCast, ← hd, hp]; ring
  have hy : (((l - 1).factorial : Per.Acris l) * d) ^ l =
      l * (((l - 1).factorial : Per.Acris l) ^ l * (m * d₂)) := by
    rw [mul_pow, hdl]; ring
  rw [h1, map_mul, map_natCast]
  exact (GlobalTheory.MemLoc.isUnit_l_Bcris l).mul ((isUnit_one_add hy).map _)

theorem isUnit_toB_frob_eis : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (ϖ : PiSys l e),
    IsUnit (toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)))) := by
  intro l _ a e _ _ O _ _ _ _ ϖ
  have hE : WittVector.frobenius (ϖ.ev a (eis l a e)) = ϖ.teich ^ (e * l) + l := by
    rw [← ϖ.ev_frobS a, eis, map_add, map_pow, frobS_X, map_natCast, map_add, map_pow, map_pow, PiSys.ev_X,
      map_natCast, ← pow_mul, mul_comm l e]
  have h : toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) =
      (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        (acrisToBcris l (ainfToAcris l (ϖ.teich ^ (e * l) + l))) := by
    rw [frobOA_tmul, hE]; rfl
  rw [h]
  exact (isUnit_teich_pow_add ϖ).map _

end GlobalTheory.BKGal.FrobEis
