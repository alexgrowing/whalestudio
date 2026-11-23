import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleEmbeddingFrobeniusGaloisCompatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEll

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl
section Gen
variable {O A R : Type} [CommRing O] [CommRing A] [CommRing R] [Algebra O R] {n : ℕ}

theorem letφ_smul_letE (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (o : O) (i : ZMod n) :
    letφ φ₀ (o • letE i : LetA O n) = o • letE (i + 1) := by
  rw [map_smul]
  congr 1
  funext k
  change φ₀ (letE i (k - 1)) = letE (i + 1) k
  by_cases hk : k = i + 1
  · subst hk
    simp [letE]
  · have : k - 1 ≠ i := fun h => hk (by rw [← h]; ring)
    simp [letE, hk, this]

theorem near_one_split [NeZero n] {ι : A →+* R} {p : ℕ} (j : LetA O n →ₐ[O] R)
    (hj : ∀ a, ∃ b, j a = ι b) (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (φR : R → R)
    (hφj : ∀ b, φR (j b) = j (letφ φ₀ b))
    (hφ : ∀ x, Near ι p (j letπ) 1 x → Near ι p (j letπ) 1 (φR x))
    (hO : ∀ o : O, Near ι p (j letπ) 1 (algebraMap O R o) → ∃ o' : O, o = (p : O) * o')
    (a : LetA O n) (ha : Near ι p (j letπ) 1 (j a)) :
    ∃ a1 a2 : LetA O n, a = letπ * a1 + (p : LetA O n) * a2 := by
  obtain ⟨a', ha'⟩ : ∃ a' : LetA O n,
      a = letπ * a' + fun i => PowerSeries.C (PowerSeries.constantCoeff (a i)) :=
    ⟨fun i => PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (a i),
      funext fun i => PowerSeries.eq_X_mul_shift_add_const (a i)⟩
  set c : LetA O n := fun i => PowerSeries.C (PowerSeries.constantCoeff (a i)) with hc
  have h1 : Near ι p (j letπ) 1 (j c) := by
    obtain ⟨b, hb⟩ := hj a'
    have h2 : j c = j a - j letπ ^ 1 * ι b := by
      rw [pow_one, ← hb, ← map_mul, ← map_sub]
      congr 1
      exact eq_sub_of_add_eq' ha'.symm
    rw [h2]
    exact ha.sub (Near.pow_mul 1 b)
  have h3 : ∀ i, ∃ o' : O, PowerSeries.constantCoeff (a i) = (p : O) * o' := by
    intro i
    set o := PowerSeries.constantCoeff (a i) with ho
    have h4 : Near ι p (j letπ) 1 (j (o • letE i)) := by
      obtain ⟨b, hb⟩ := hj (letE i)
      have h5 : (o • letE i : LetA O n) = letE i * c := by
        funext k
        by_cases hk : k = i
        · subst hk
          simp [letE, hc, ho, PowerSeries.smul_eq_C_mul]
        · simp [letE, hk]
      rw [h5, map_mul, hb]
      exact h1.mul_ι b
    have h6 : ∀ k : ℕ, Near ι p (j letπ) 1 (j (o • letE (i + (k : ZMod n)))) := by
      intro k
      induction k with
      | zero => simpa using h4
      | succ k ih =>
        have := hφ _ ih
        rwa [hφj, letφ_smul_letE, add_assoc, ← Nat.cast_succ] at this
    have h7 : ∀ k : ZMod n, Near ι p (j letπ) 1 (j (o • letE k)) := by
      intro k
      have := h6 (k - i).val
      rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this
    apply hO
    have h8 : ∑ k : ZMod n, (letE k : LetA O n) = 1 := by
      funext k
      simp [letE, Finset.sum_apply, Pi.single_apply]
    have h9 : algebraMap O R o = ∑ k : ZMod n, j (o • letE k) := by
      rw [← map_sum, ← Finset.smul_sum, h8, map_smul, map_one, Algebra.algebraMap_eq_smul_one]
    rw [h9]
    exact Near.sum _ fun k _ => h7 k
  choose o' ho' using h3
  refine ⟨a', fun i => PowerSeries.C (o' i), ha'.trans ?_⟩
  congr 1
  funext i
  simp [hc, ho']

theorem near_split [NeZero n] {ι : A →+* R} {p : ℕ} {t : R} (j : LetA O n →ₐ[O] R)
    (hj : ∀ a, ∃ b, j a = ι b) (ht : j letπ = t) (hu : IsUnit t)
    (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (φR : R → R)
    (hφj : ∀ b, φR (j b) = j (letφ φ₀ b))
    (hφ : ∀ x, Near ι p t 1 x → Near ι p t 1 (φR x))
    (hO : ∀ o : O, Near ι p t 1 (algebraMap O R o) → ∃ o' : O, o = (p : O) * o')
    (m : ℕ) (a : LetA O n) (ha : Near ι p t m (j a)) :
    ∃ a1 a2 : LetA O n, a = letπ ^ m * a1 + (p : LetA O n) * a2 := by
  subst ht
  induction m with
  | zero => exact ⟨a, 0, by simp⟩
  | succ m ih =>
    obtain ⟨τ, hτ⟩ := hj letπ
    obtain ⟨a1, a2, h⟩ := ih (ha.mono hτ.symm (Nat.le_succ m))
    have h1 : j letπ ^ m * j a1 = j a - (p : R) * j a2 := by
      rw [h, map_add, map_mul, map_mul, map_pow, map_natCast, add_sub_cancel_right]
    have h2 : Near ι p (j letπ) (m + 1) (j letπ ^ m * j a1) := by
      rw [h1]
      exact ha.sub (Near.of_mul _ _)
    obtain ⟨b1, b2, hb⟩ := near_one_split j hj φ₀ φR hφj hφ hO a1 (h2.cancel hu)
    exact ⟨b1, letπ ^ m * b2 + a2, by rw [h, hb]; ring⟩
end Gen

set_option maxHeartbeats 1000000 in

theorem mem_pow_pi_of_nearPi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (m : ℕ) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), NearPi AI LL s m (inclR LL (E.tie.io a)) → ∃ a1 a2 : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), a = letπ ^ m * a1 + (l : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) * a2 := by
  intro l _ P AI K s LL h W E m a ha
  obtain ⟨c1, -, c3, -⟩ := GlobalTheory.T.etaleEmbedding_frobenius_galois_compat l P AI K s LL h W E
  obtain ⟨-, -, p3, p4⟩ := GlobalTheory.DecomplFrob.frobenius_and_constants l P AI LL s
  have := (P.PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hu : IsUnit (piR AI LL s) := c3 ▸ W.EE_π.map E.tie.ioE
  refine near_split (ι := (inclR LL : RA LL →+* RW LL)) ((inclR LL).comp E.tie.io)
    (fun b => ⟨E.tie.io b, rfl⟩) ((E.tie.ioE_ext letπ).symm.trans c3) hu W.φ₀ (fun x => φRW LL x)
    (fun b => ?_) (p3 1) p4 m a ha
  have h1 := c1 (algebraMap _ W.EE b)
  exact (congrArg (fun x => φRW LL x) (E.tie.ioE_ext b)).symm.trans (h1.symm.trans
    ((congrArg (fun e => E.tie.ioE e) (W.φE_ext b)).trans (E.tie.ioE_ext _)))

end GlobalTheory.Decompl
