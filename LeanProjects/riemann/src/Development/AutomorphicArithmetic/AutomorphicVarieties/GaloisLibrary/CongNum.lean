import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AutCFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyScaledInverse

open Polynomial

namespace UpperTheory.V.CongNum

theorem exists_int_of_fixed {x : ℂ} (hx : IsIntegral ℤ x) (h : ∀ σ : ℂ ≃+* ℂ, σ x = x) : ∃ n : ℤ, (n : ℂ) = x := by
  have h1 : x ∈ (⊥ : IntermediateField ℚ ℂ) :=
    GroundTheory.Global.mem_bot_iff_forall_algEquiv_apply_eq.2 fun σ => h σ.toRingEquiv
  obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.1 h1
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).1 hx
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨n, by simp⟩

theorem exists_int_prod {S : Type} [Fintype S] (f : S → ℂ) (hi : ∀ s, IsIntegral ℤ (f s))
    (hc : ∀ σ : ℂ ≃+* ℂ, ∃ e : S ≃ S, ∀ s, f (e s) = σ (f s)) : ∃ n : ℤ, (n : ℂ) = ∏ s, f s := by
  refine exists_int_of_fixed (IsIntegral.prod _ fun s _ => hi s) fun σ => ?_
  obtain ⟨e, he⟩ := hc σ
  rw [map_prod, ← e.prod_comp f]
  exact Finset.prod_congr rfl fun s _ => (he s).symm

theorem log_abs_le {S : Type} [Fintype S] (f : S → ℂ) (n : ℤ) (hn : (n : ℂ) = ∏ s, f s) (h0 : ∀ s, f s ≠ 0)
    (R : ℝ) (hR : ∀ s, ‖f s‖ ≤ R) : n ≠ 0 ∧ Real.log |(n : ℝ)| ≤ Fintype.card S * Real.log R := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Finset.prod_ne_zero_iff.2 (fun s _ => h0 s) (by rw [← hn]; simp)
  refine ⟨hn0, ?_⟩
  have e : |(n : ℝ)| = ∏ s, ‖f s‖ := by rw [← norm_prod, ← hn, Complex.norm_intCast]
  rw [e, Real.log_prod (fun s _ => norm_ne_zero_iff.2 (h0 s))]
  calc ∑ s, Real.log ‖f s‖ ≤ ∑ _s : S, Real.log R :=
        Finset.sum_le_sum fun s _ => Real.log_le_log (norm_pos_iff.2 (h0 s)) (hR s)
    _ = _ := by simp

theorem norm_le_one {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {x : ℂ} (hx : IsIntegral ℤ x) : ‖ι.symm x‖ ≤ 1 := by
  have h0 : IsIntegral ℤ (ι.symm x) := by
    convert map_isIntegral_int (ι.symm : ℂ →+* PadicAlgCl l) hx using 1 <;> first | exact Subsingleton.elim _ _ | rfl
  have h1 : IsIntegral (NormedField.valuation (K := PadicAlgCl l)).integer (ι.symm x) := h0.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral h1
  have h3 : ‖ι.symm x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_le_prod {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {S : Type} [Fintype S] (f : S → ℂ)
    (hi : ∀ s, IsIntegral ℤ (f s)) (n : ℤ) (hn : (n : ℂ) = ∏ s, f s) {T : Type} [Fintype T] (j : T → S)
    (hj : Function.Injective j) : ‖(n : PadicAlgCl l)‖ ≤ ∏ t, ‖ι.symm (f (j t))‖ := by
  classical
  have e : (n : PadicAlgCl l) = ∏ s, ι.symm (f s) := by rw [← map_prod, ← hn, map_intCast]
  rw [e, norm_prod, ← Finset.prod_image (s := Finset.univ) (g := j) (f := fun s => ‖ι.symm (f s)‖) hj.injOn]
  exact Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ _) (fun _ _ => norm_nonneg _)
    fun s _ _ => norm_le_one ι (hi s)

theorem exists_unit_pow (k : ℕ) [NeZero k] (σ : ℂ ≃+* ℂ) :
    ∃ b : (ZMod k)ˣ, ∀ z : ℂ, z ^ k = 1 → σ z = z ^ (b : ZMod k).val := by
  refine ⟨modularCyclotomicCharacter ℂ (n := k) (by simpa using Complex.card_rootsOfUnity k) σ, fun z hz => ?_⟩
  exact modularCyclotomicCharacter.spec ℂ _ σ (rootsOfUnity.mkOfPowEq z hz).2

theorem pow_val_mul {k : ℕ} [NeZero k] {z : ℂ} (hz : z ^ k = 1) (a b : ZMod k) : z ^ (a * b).val = (z ^ a.val) ^ b.val := by
  rw [← pow_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hz]

theorem trace_eq_sum {K : Type} [Field K] (ι : K ≃+* ℂ) {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (B : Multiset ℂ)
    (h : g.charpoly.map ι.toRingHom = (B.map fun b => X - C b).prod) : g.trace = ι.symm B.sum := by
  rw [← Matrix.charpoly_map] at h
  have h1 := Matrix.trace_eq_sum_roots_charpoly (g.map ι.toRingHom)
  rw [h, roots_multiset_prod_X_sub_C] at h1
  rw [← h1, RingEquiv.eq_symm_apply]
  simp [Matrix.trace]

theorem trace_eq_sum_of_inv {K : Type} [Field K] (ι : K ≃+* ℂ) {n : ℕ} (g : GL (Fin n) K) (B : Multiset ℂ)
    (h : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.map ι.toRingHom = ((B.map (·⁻¹)).map fun b => X - C b).prod) :
    (g : Matrix (Fin n) (Fin n) K).trace = ι.symm B.sum := by
  refine trace_eq_sum ι _ B ?_
  rw [← Matrix.charpoly_map] at h ⊢
  have h1 := GlobalTheory.charpoly_smul_inv_of_charpoly_eq_prod n (Matrix.GeneralLinearGroup.map ι.toRingHom g⁻¹) 1 _ h
  rw [map_inv, inv_inv, one_smul, Multiset.map_map] at h1
  simpa using h1

end UpperTheory.V.CongNum
