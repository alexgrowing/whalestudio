import Mathlib
open Polynomial

namespace GlobalTheory

theorem noether_trick_monic {k : Type} [Field k] (f : Polynomial (Polynomial k)) (hf : f.Monic)
    (M : ℕ) (hM0 : M ≠ 0) (hM : ∀ i, (f.coeff i).natDegree < M) :
    (f.eval₂ (Polynomial.mapRingHom (Polynomial.C : k →+* Polynomial k))
      ((Polynomial.X : Polynomial (Polynomial k)) ^ M - Polynomial.C Polynomial.X)).Monic := by
  set r : Polynomial (Polynomial k) := X ^ M - C X with hr
  have hrm : r.Monic := monic_X_pow_sub_C _ hM0
  have hrd : r.natDegree = M := natDegree_X_pow_sub_C
  rw [eval₂_eq_sum_range, Finset.sum_range_succ]
  have hlead : f.coeff f.natDegree = 1 := hf
  rw [hlead, map_one, one_mul]
  apply Monic.add_of_right (hrm.pow _)
  rw [degree_eq_natDegree (hrm.pow _).ne_zero, hrm.natDegree_pow, hrd]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro i hi
  rw [Finset.mem_range] at hi
  refine lt_of_le_of_lt degree_le_natDegree ?_
  rw [Nat.cast_lt]
  have h1 : (mapRingHom (C : k →+* Polynomial k) (f.coeff i)).natDegree ≤ (f.coeff i).natDegree := by
    rw [coe_mapRingHom]; exact natDegree_map_le
  have h2 : (r ^ i).natDegree ≤ i * M := by
    rw [← hrd]; exact natDegree_pow_le
  have h3 := hM i
  have h4 : (i + 1) * M ≤ f.natDegree * M := Nat.mul_le_mul_right M hi
  calc _ ≤ _ := natDegree_mul_le
    _ ≤ (f.coeff i).natDegree + i * M := Nat.add_le_add h1 h2
    _ < f.natDegree * M := by nlinarith

theorem noether_trick : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (t a : A),
    (Polynomial.aeval (R := k) t).Finite → ∃ M : ℕ, (Polynomial.aeval (R := k) (t ^ M + a)).Finite := by
  intro k A _ _ _ t a ht
  have hint : (aeval (R := k) t).toRingHom.IsIntegral := RingHom.Finite.to_isIntegral ht
  obtain ⟨f, hfm, hf0⟩ := hint (-a)
  set M := 1 + ∑ i ∈ Finset.range (f.natDegree + 1), (f.coeff i).natDegree with hMdef
  have hM : ∀ i, (f.coeff i).natDegree < M := by
    intro i
    by_cases hi : i ≤ f.natDegree
    · have := Finset.single_le_sum (f := fun i => (f.coeff i).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      have h' : (f.coeff i).natDegree ≤ ∑ j ∈ Finset.range (f.natDegree + 1), (f.coeff j).natDegree := this
      omega
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp only [natDegree_zero]; omega
  refine ⟨M, ?_⟩
  set φ : Polynomial k →+* A := (aeval (R := k) (t ^ M + a)).toRingHom with hφ
  set q : Polynomial (Polynomial k) :=
    f.eval₂ (mapRingHom (C : k →+* Polynomial k)) (X ^ M - C X) with hqdef
  have hq : q.Monic := noether_trick_monic f hfm M (by omega) hM
  set ψ : Polynomial (Polynomial k) →+* A := eval₂RingHom φ t with hψ
  have hcomp : ψ.comp (mapRingHom C) = (aeval (R := k) t).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c; simp [ψ, φ]
    · simp [ψ, φ]
  have hψq : ψ q = 0 := by
    simp only [hqdef]
    rw [hom_eval₂, hcomp]
    have : ψ (X ^ M - C X) = -a := by simp [ψ, φ]
    rw [this]; exact hf0
  have hqt : q.eval₂ φ t = 0 := by simpa [ψ] using hψq
  let L : AdjoinRoot q →+* A := AdjoinRoot.lift φ t hqt
  have hL : L.comp (AdjoinRoot.mk q) = ψ := by
    ext g <;> simp [L, ψ, AdjoinRoot.lift_mk]
  have hψfin : ψ.Finite := by
    apply RingHom.Finite.of_comp_finite (f := mapRingHom (C : k →+* Polynomial k))
    rw [hcomp]; exact ht
  have hLfin : L.Finite := by
    apply RingHom.Finite.of_comp_finite (f := AdjoinRoot.mk q)
    rw [hL]; exact hψfin
  have hof : (AdjoinRoot.of q).Finite := by
    haveI : Module.Finite (Polynomial k) (AdjoinRoot q) := (AdjoinRoot.powerBasis' hq).finite
    exact RingHom.finite_algebraMap.mpr this
  have hφeq : L.comp (AdjoinRoot.of q) = φ := by
    ext c <;> simp [L, AdjoinRoot.lift_of]
  have : φ.Finite := by rw [← hφeq]; exact hLfin.comp hof
  exact this

end GlobalTheory
