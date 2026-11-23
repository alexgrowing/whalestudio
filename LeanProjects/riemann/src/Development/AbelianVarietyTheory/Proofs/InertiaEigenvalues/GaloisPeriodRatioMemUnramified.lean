import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedOfFrobeniusIterateFixedFilStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvMemDeRhamFilNegOfExactDegreeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.PeriodQuot

theorem iter_mul {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (f : A →ₐ[R] A)
    (j : ℕ) (a b : A) : f^[j] (a * b) = f^[j] a * f^[j] b := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem iter_one {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (f : A →ₐ[R] A)
    (j : ℕ) : f^[j] (1 : A) = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_one]

theorem iter_natCast_mul {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (f : A →ₐ[R] A)
    (j m q : ℕ) (a : A) : f^[j] ((m : A) ^ q * a) = (m : A) ^ q * f^[j] a := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

theorem galois_periodRatio_mem_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ g : ↥(GK K), ∃ a : ↥(K0 K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B a * x := by
  intro l _ P AI hT K x hx hn h1 h2 hj g
  obtain ⟨u, rfl⟩ := hx
  set n := finrank ℚ_[l] ↥(K0 K) with hn_def
  have npos : 0 < n := by
    haveI := (P.PD K).finK₀
    exact Module.finrank_pos
  set y : P.R.B := ((u⁻¹ : (P.R.B)ˣ) : P.R.B) with hy
  have huy : (u : P.R.B) * y = 1 := u.mul_inv
  set c : P.R.B := P.actQ (g : GQ l) u * y with hc
  have hcx : P.actQ (g : GQ l) u = c * u := by rw [hc, mul_assoc, u.inv_mul, mul_one]
  have hcomm : ∀ b, P.φB (P.actQ (g : GQ l) b) = P.actQ (g : GQ l) (P.φB b) := by
    intro b
    have := (P.PD K).φ_comm g b
    rwa [P.PD_φ, P.PD_actB, P.PD_actB, P.PD_φ] at this
  have hcommj : ∀ j b, (⇑P.φB)^[j] (P.actQ (g : GQ l) b) = P.actQ (g : GQ l) ((⇑P.φB)^[j] b) :=
    fun j b => (Function.Commute.iterate_left (f := ⇑P.φB) (g := ⇑(P.actQ (g : GQ l)))
      (fun b => hcomm b) j) b

  have hlB : IsUnit ((l : ℕ) : P.R.B) := by
    have h0 : ((l : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    have := (isUnit_iff_ne_zero.mpr h0).map (algebraMap ℚ_[l] P.R.B)
    simpa using this

  have hφc : (⇑P.φB)^[n] c = c := by
    have hu : IsUnit ((l : P.R.B) * u) := hlB.mul u.isUnit
    apply hu.mul_left_injective
    show (⇑P.φB)^[n] c * ((l : P.R.B) * u) = c * ((l : P.R.B) * u)
    rw [← hn, ← iter_mul, ← hcx, hcommj, hn, map_mul, map_natCast, hcx]
    ring

  have hpow : ∀ q : ℕ, (⇑P.φB)^[n * q] (u : P.R.B) = (l : P.R.B) ^ q * u := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, hn,
        show (l : P.R.B) * (u : P.R.B) = (l : P.R.B) ^ 1 * u by rw [pow_one],
        iter_natCast_mul, ih, ← mul_assoc, ← pow_add, add_comm 1 q]
  have hsmul : ∀ (q : ℕ) (z : P.R.B), P.ιB ((l : P.R.B) ^ q * z) =
      (((l : ↥K.1) ^ q : ↥K.1)) • P.ιB z := by
    intro q z
    rw [map_mul, map_pow, map_natCast, Algebra.smul_def, map_pow, map_natCast]
  have hne : ∀ q : ℕ, ((l : ↥K.1) ^ q : ↥K.1) ≠ 0 := fun q =>
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  have hdeg : ∀ j : ℕ, ∃ d : ℤ, P.ιB ((⇑P.φB)^[j] (u : P.R.B)) ∈ (P.PD K).Fil d ∧
      P.ιB ((⇑P.φB)^[j] (u : P.R.B)) ∉ (P.PD K).Fil (d + 1) := by
    intro j
    have hj_eq : j = j % n + n * (j / n) := (Nat.mod_add_div j n).symm
    have hw : (⇑P.φB)^[j] (u : P.R.B) = (l : P.R.B) ^ (j / n) * (⇑P.φB)^[j % n] u := by
      conv_lhs => rw [hj_eq]
      rw [Function.iterate_add_apply, hpow, iter_natCast_mul]
    rw [hw, hsmul]
    rcases Nat.eq_zero_or_pos (j % n) with h0 | hr
    · refine ⟨1, ?_, ?_⟩
      · rw [h0, Function.iterate_zero_apply]
        exact Submodule.smul_mem _ _ h1
      · rw [h0, Function.iterate_zero_apply, Submodule.smul_mem_iff _ (hne _)]
        simpa using h2
    · obtain ⟨ha, hb⟩ := hj (j % n) hr (Nat.mod_lt _ npos)
      refine ⟨0, Submodule.smul_mem _ _ ha, ?_⟩
      rw [Submodule.smul_mem_iff _ (hne _)]
      simpa using hb
  have hF : ∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD K).Fil 0 := by
    intro j
    obtain ⟨d, hd1, hd2⟩ := hdeg j
    have hinv : P.ιB ((⇑P.φB)^[j] (u : P.R.B)) * P.ιB ((⇑P.φB)^[j] y) = 1 := by
      rw [← map_mul, ← iter_mul, huy, iter_one, map_one]
    have hyF := GlobalTheory.T.inv_mem_deRhamFil_neg_of_exact_degree l P AI hT K d _ _ hinv hd1 hd2
    have hgF : P.ιB (P.actQ (g : GQ l) ((⇑P.φB)^[j] (u : P.R.B))) ∈ (P.PD K).Fil d := by
      have := (P.PD K).ι_comm g ((⇑P.φB)^[j] (u : P.R.B))
      rw [P.PD_ι, P.PD_actB, P.PD_ι] at this
      rw [this]
      exact (P.PD K).Fil_G g d _ hd1
    have := (P.PD K).Fil_mul d (-d) _ _ hgF hyF
    rw [add_neg_cancel] at this
    rw [hc, iter_mul, hcommj, map_mul]
    exact this
  obtain ⟨a, ha⟩ := GlobalTheory.T.mem_unramified_of_frobenius_iterate_fixed_fil l P AI hT K c hφc hF
  exact ⟨a, by rw [hcx, ha]⟩

end GlobalTheory.PeriodQuot
