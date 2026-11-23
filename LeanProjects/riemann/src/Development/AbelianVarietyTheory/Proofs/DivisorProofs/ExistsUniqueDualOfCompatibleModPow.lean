import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem exists_unique_dual_of_compatible_mod_pow :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O)
      [IsAdicComplete (Ideal.span {a}) O] (u : ∀ n : ℕ, M →ₗ[O] O ⧸ Ideal.span {a ^ n}),
      (∀ n w (x : O), u (n + 1) w = Ideal.Quotient.mk _ x → u n w = Ideal.Quotient.mk _ x) →
      ∃! l : Module.Dual O M, ∀ n w, Ideal.Quotient.mk _ (l w) = u n w := by
  intro O M _ _ _ a _ u hu

  have sep : ∀ y : O, (∀ n : ℕ, y ∈ Ideal.span {a ^ n}) → y = 0 := by
    intro y hy
    refine IsHausdorff.haus' (I := Ideal.span {a}) y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact hy n
  have key : ∀ w : M, ∃! y : O, ∀ n, Ideal.Quotient.mk (Ideal.span {a ^ n}) y = u n w := by
    intro w
    choose x hx using fun n => Ideal.Quotient.mk_surjective (u n w)
    have step : ∀ n, x n - x (n + 1) ∈ Ideal.span {a ^ n} := by
      intro n
      exact Ideal.Quotient.eq.mp ((hx n).trans (hu n w (x (n + 1)) (hx (n + 1)).symm))
    have cauchy : ∀ m n, m ≤ n → x m - x n ∈ Ideal.span {a ^ m} := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ k hmk ih =>
        have h2 : x k - x (k + 1) ∈ Ideal.span {a ^ m} :=
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a hmk)) (step k)
        have := Ideal.add_mem _ ih h2
        simpa using this
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {a}) x (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
      exact cauchy m n hmn)
    refine ⟨L, fun n => ?_, fun y hy => ?_⟩
    · have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
      rw [← hx n]
      exact Ideal.Quotient.eq.mpr (by simpa using (Ideal.span {a ^ n}).neg_mem h)
    · refine sub_eq_zero.mp (sep _ fun n => ?_)
      have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
      exact Ideal.Quotient.eq.mp ((hy n).trans (hx n).symm) |> fun h' => by
        simpa using Ideal.add_mem _ h' h
  choose f hf huniq using key
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro w w'
    refine (huniq (w + w') _ fun n => ?_).symm
    rw [map_add, map_add, hf, hf]
  · intro c w
    refine (huniq (c • w) _ fun n => ?_).symm
    rw [RingHom.id_apply, smul_eq_mul, map_mul, map_smul, ← hf w n, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq]
  · exact fun n w => hf w n
  · intro l hl
    exact LinearMap.ext fun w => huniq w (l w) fun n => hl n w

end GlobalTheory.PDiv
