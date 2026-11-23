import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeHtE

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical

namespace GlobalTheory.CoefHeight

open Polynomial

theorem val_coeff_prod_X_sub_C_le {K : Type} [Field K] (w : Valuation K ℝ≥0) {M : ℝ≥0} (hM : 1 ≤ M)
    (s : Multiset K) (hs : ∀ z ∈ s, w z ≤ M) (j : ℕ) :
    w ((s.map fun a => X - C a).prod.coeff j) ≤ M ^ Multiset.card s := by
  induction s using Multiset.induction_on generalizing j with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero, coeff_one]
    split_ifs <;> simp
  | cons a s ih =>
    have ha : w a ≤ M := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ z ∈ s, w z ≤ M := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, sub_mul, coeff_sub, coeff_C_mul]
    refine (w.map_sub _ _).trans (max_le ?_ ?_)
    · cases j with
      | zero => rw [coeff_X_mul_zero, map_zero]; exact bot_le
      | succ i => rw [coeff_X_mul]; exact (ih hs' i).trans (pow_le_pow_right₀ hM (Nat.le_succ _))
    · rw [map_mul, pow_succ']
      exact mul_le_mul' ha (ih hs' j)

theorem nnnorm_coeff_minpoly_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : E) (v : HeightOneSpectrum (𝓞 F)) (j : ℕ) :
    ‖algebraMap F (v.adicCompletion F) ((minpoly F x).coeff j)‖₊ ≤
      max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) ^ Module.finrank F E := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set M := max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  set p := minpoly F x with hp
  set q := p.map (algebraMap F (FvBar F v)) with hqdef
  have hmon : q.Monic := (minpoly.monic hint).map _
  have hsplit : q.Splits := IsAlgClosed.splits q
  have hq : q = (q.roots.map fun a => X - C a).prod := hsplit.eq_prod_roots_of_monic hmon
  have hroots : ∀ z ∈ q.roots, valBar F v z ≤ M := by
    intro z hz
    have hq0 : q ≠ 0 := hmon.ne_zero
    have hz' : aeval z p = 0 := by
      rw [mem_roots hq0, IsRoot, hqdef, eval_map_algebraMap] at hz; exact hz
    obtain ⟨τ, hτ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
      (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) hz'
    have h1 : finEmb F v τ ((1 : v.adicCompletion F) ⊗ₜ[F] x) = z := by rw [finEmb_tmul, map_one, one_mul, hτ]
    show absBar F v z ≤ M
    rw [← h1]; exact (le_absFin F v τ _).trans (le_max_right _ _)
  have hcard : Multiset.card q.roots ≤ Module.finrank F E := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hqdef, natDegree_map]; exact minpoly.natDegree_le x
  have key := val_coeff_prod_X_sub_C_le (valBar F v) hM q.roots hroots j
  rw [← hq] at key
  have hc : valBar F v (q.coeff j) = ‖algebraMap F (v.adicCompletion F) (p.coeff j)‖₊ := by
    show absBar F v _ = _
    rw [hqdef, coeff_map, IsScalarTower.algebraMap_apply F (v.adicCompletion F) (FvBar F v), absBar_algebraMap]
  rw [← hc]
  exact key.trans (pow_le_pow_right₀ hM hcard)

end GlobalTheory.CoefHeight
