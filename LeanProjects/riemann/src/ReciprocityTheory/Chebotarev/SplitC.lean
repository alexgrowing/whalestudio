import ReciprocityTheory.Chebotarev.SplitDef
import ReciprocityTheory.Chebotarev.SplitF
import ReciprocityTheory.Chebotarev.ChebyshevLambdaSubPsiBounded

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem splitC_nrm_pos {E : Type} [Field E] [NumberField E] (q : Prm E) : 0 < ((Nrm q : ℕ) : ℝ) := by
  have : Nrm q ≠ 0 := by
    unfold Nrm
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact q.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

theorem splitC_nrm_ge_one {E : Type} [Field E] [NumberField E] (q : Prm E) : 1 ≤ ((Nrm q : ℕ) : ℝ) := by
  have h := splitC_nrm_pos q
  have : 0 < Nrm q := by exact_mod_cast h
  exact_mod_cast this

theorem splitC_indicator_le {E : Type} [Field E] [NumberField E] (S : Set (Prm E)) (hS : S.Finite) (s : ℝ)
    (hs : 0 ≤ s) : ∑' q, S.indicator (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) q ≤ hS.toFinset.card := by
  rw [tsum_eq_sum (s := hS.toFinset)]
  · calc ∑ q ∈ hS.toFinset, S.indicator (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) q
        ≤ ∑ _q ∈ hS.toFinset, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Set.indicator_of_mem (hS.mem_toFinset.mp hq)]
          exact Real.rpow_le_one_of_one_le_of_nonpos (splitC_nrm_ge_one q) (by linarith)
      _ = hS.toFinset.card := by simp
  · intro q hq
    rw [Set.indicator_of_notMem]
    intro h'
    exact hq (hS.mem_toFinset.mpr h')

theorem splitC_bound (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (k : ℕ) (S : Set (Prm E)) (hS : S.Finite)
    (h : ∀ q ∉ S, k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard) (s : ℝ) (hs : 1 < s) :
    (k : ℝ) * PE E s ≤ PE E' s + k * hS.toFinset.card := by
  have key := fibre_sum_ge (under (E := E) (E' := E')) (fun P : Prm E' => ((Nrm P : ℕ) : ℝ) ^ (-s))
    (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) k (fun P => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (affine_proper_base_change.2.2 E' s hs) (fun q => Real.rpow_nonneg (Nat.cast_nonneg _) _) (affine_proper_base_change.2.2 E s hs) S hS
    (by
      intro q hq
      have hset : {P : Prm E' | under P = q ∧ ((Nrm P : ℕ) : ℝ) ^ (-s) = ((Nrm q : ℕ) : ℝ) ^ (-s)} =
          {P : Prm E' | under P = q ∧ Nrm P = Nrm q} := by
        ext P
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          have := (Real.rpow_left_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith : -s ≠ 0)).mp h2
          exact_mod_cast this
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by rw [h2]⟩
      rw [hset]
      exact h q hq)
  have hind := splitC_indicator_le S hS s (by linarith)
  unfold PE
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hind hk0]

theorem splitC_not_almost_split (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (k : ℕ) (hk : 2 ≤ k)
    (h : {q : Prm E | ¬ k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard}.Finite) : False := by
  set S := {q : Prm E | ¬ k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard} with hSdef
  have hfib : ∀ q ∉ S, k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard := by
    intro q hq
    by_contra hc
    exact hq hc
  obtain ⟨C1, hC1⟩ := chebyshev_log_bounded E
  obtain ⟨C2, hC2⟩ := chebyshev_log_bounded E'
  set N : ℝ := (h.toFinset.card : ℝ)
  set M : ℝ := max (C2 + k * (N + C1)) 0
  set s : ℝ := 1 + Real.exp (-(M + 1))
  have he : 0 < Real.exp (-(M + 1)) := Real.exp_pos _
  have he1 : Real.exp (-(M + 1)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ M := le_max_right _ _
    linarith)
  have hs1 : 1 < s := by simp only [s]; linarith
  have hs2 : s ∈ Set.Ioc 1 2 := ⟨hs1, by simp only [s]; linarith⟩
  have hlog : Real.log (1 / (s - 1)) = M + 1 := by
    simp only [s, add_sub_cancel_left, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hb := splitC_bound E E' k S h hfib s hs1
  have h1 := hC1 s hs2
  have h2 := hC2 s hs2
  rw [hlog] at h1 h2
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hM : C2 + k * (N + C1) ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := le_max_right _ _
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  have : (k : ℝ) * (M + 1 - C1) ≤ k * PE E s := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

end ReciprocityTheory.Cheb
