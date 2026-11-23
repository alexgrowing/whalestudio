import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem fact_le_log {l e t : ℕ} (hl : l.Prime) (he : e ≠ 0) (het : e < t) :
    (e.factorization l : ℝ) * Real.log 2 ≤ Real.log t := by
  have h2 : 2 ^ e.factorization l ≤ e :=
    le_trans (Nat.pow_le_pow_left hl.two_le _) (Nat.ordProj_le l he)
  rw [← Real.log_pow]
  apply Real.log_le_log (by positivity)
  exact_mod_cast h2.trans het.le

private theorem nu_sum (l N : ℕ) (hl : l.Prime) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, 2 ≤ t →
    ∑ e ∈ Finset.Ico 1 t, (LDataCardLeFinrank.nuBound l N e : ℝ) ≤ C * (t * Real.log t) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨((max (N.factorization l) (if l = 2 then 2 else 1) : ℕ) + 1 : ℝ) / Real.log 2,
    div_nonneg (by positivity) hlog2.le, ?_⟩
  intro t ht
  set M : ℕ := max (N.factorization l) (if l = 2 then 2 else 1) with hM
  have hlogt : Real.log 2 ≤ Real.log t :=
    Real.log_le_log (by norm_num) (by exact_mod_cast ht)
  have hterm : ∀ e ∈ Finset.Ico 1 t,
      (LDataCardLeFinrank.nuBound l N e : ℝ) ≤ ((M : ℝ) + 1) / Real.log 2 * Real.log t := by
    intro e he
    rw [Finset.mem_Ico] at he
    have hv := fact_le_log hl (by omega) he.2
    have hnbN : LDataCardLeFinrank.nuBound l N e ≤ M + e.factorization l := by
      unfold LDataCardLeFinrank.nuBound
      rw [hM]
      split_ifs <;> first | exact le_refl _ | exact Nat.zero_le _
    have hnb : (LDataCardLeFinrank.nuBound l N e : ℝ) ≤ (M : ℝ) + e.factorization l := by
      exact_mod_cast hnbN
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    calc (LDataCardLeFinrank.nuBound l N e : ℝ) * Real.log 2
        ≤ ((M : ℝ) + e.factorization l) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hnb hlog2.le
      _ = (M : ℝ) * Real.log 2 + (e.factorization l : ℝ) * Real.log 2 := by ring
      _ ≤ (M : ℝ) * Real.log t + Real.log t :=
          add_le_add (mul_le_mul_of_nonneg_left hlogt (by positivity)) hv
      _ = ((M : ℝ) + 1) * Real.log t := by ring
  have hC : 0 ≤ ((M : ℝ) + 1) / Real.log 2 * Real.log t :=
    mul_nonneg (div_nonneg (by positivity) hlog2.le) (hlog2.le.trans hlogt)
  calc ∑ e ∈ Finset.Ico 1 t, (LDataCardLeFinrank.nuBound l N e : ℝ)
      ≤ ∑ e ∈ Finset.Ico 1 t, ((M : ℝ) + 1) / Real.log 2 * Real.log t := Finset.sum_le_sum hterm
    _ = ((t - 1 : ℕ) : ℝ) * (((M : ℝ) + 1) / Real.log 2 * Real.log t) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ (t : ℝ) * (((M : ℝ) + 1) / Real.log 2 * Real.log t) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le t 1) hC
    _ = ((M : ℝ) + 1) / Real.log 2 * (t * Real.log t) := by ring

theorem UpperTheory.V.Chr.nuSum :
    (∀ l N : ℕ, l.Prime → ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, 2 ≤ t → ∑ e ∈ Finset.Ico 1 t, (LDataCardLeFinrank.nuBound l N e : ℝ) ≤ C * (t * Real.log t)) ∧
          ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (f a : ℕ → ℕ∞) (b : ℕ → ℕ) (t : ℕ) (B B' : ℝ), (∀ e, 0 < e → e < t → a e ≠ ⊤ ∧ f e ≤ a e * eO l O + (b e : ℕ∞) * eO l O) →
            ∑ e ∈ Finset.Ico 1 t, ((a e).toNat : ℝ) ≤ B → ∑ e ∈ Finset.Ico 1 t, (b e : ℝ) ≤ B' → SumLe l O f t (B + B') := by
  refine ⟨nu_sum, ?_⟩
  intro l _ O _ _ _ _ _ f a b t B B' h hB hB'
  obtain ⟨-, -, -, -, -, hne0, hle, -, -⟩ := dvrFacts l O
  have hfin : eO l O ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hn0 : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := by
      rintro rfl
      exact hne0 (by rw [← hn]; rfl)
    exact_mod_cast this
  apply SumLe.mono l (g := fun e => a e * eO l O + (b e : ℕ∞) * eO l O)
  · refine ⟨fun e h0 ht => ?_, ?_⟩
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (h e h0 ht).1
      show a e * eO l O + (b e : ℕ∞) * eO l O ≠ ⊤
      rw [← hm, ← hn]
      exact_mod_cast ENat.coe_ne_top (m * n + b e * n)
    · calc ∑ e ∈ Finset.Ico 1 t, nrm l O (a e * eO l O + (b e : ℕ∞) * eO l O)
          = ∑ e ∈ Finset.Ico 1 t, (((a e).toNat : ℝ) + (b e : ℝ)) := by
            apply Finset.sum_congr rfl
            intro e he
            rw [Finset.mem_Ico] at he
            obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (h e (by omega) he.2).1
            unfold nrm
            rw [← hm, ← hn]
            rw [show (m : ℕ∞) * (n : ℕ∞) + ((b e : ℕ) : ℕ∞) * (n : ℕ∞) = ((m * n + b e * n : ℕ) : ℕ∞) by
              push_cast; rfl]
            rw [ENat.toNat_coe, ENat.toNat_coe, ENat.toNat_coe]
            push_cast
            field_simp
        _ = ∑ e ∈ Finset.Ico 1 t, ((a e).toNat : ℝ) + ∑ e ∈ Finset.Ico 1 t, (b e : ℝ) :=
            Finset.sum_add_distrib
        _ ≤ B + B' := add_le_add hB hB'
  · intro e h0 ht
    exact (h e h0 ht).2
