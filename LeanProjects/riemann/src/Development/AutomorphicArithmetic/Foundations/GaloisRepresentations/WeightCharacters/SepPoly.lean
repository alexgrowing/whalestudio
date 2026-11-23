import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem mvEval_aeval_X_sub_C_eq_eval_sub {k : Type} [Field k] {σ : Type} (p : Polynomial k) (i : σ) (c : k)
    (z : σ → k) :
    MvPolynomial.eval z (Polynomial.aeval (MvPolynomial.X i - MvPolynomial.C c) p) =
      Polynomial.eval (z i - c) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

private theorem norm_prod_sub_one_le_of_norm_sub_one_le {k : Type} [NormedField k] [IsUltrametricDist k] {ι : Type}
    [DecidableEq ι] (s : Finset ι) (f : ι → k) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1)
    (h : ∀ j ∈ s, ‖f j - 1‖ ≤ c) : ‖∏ j ∈ s, f j - 1‖ ≤ c := by
  induction s using Finset.induction_on with
  | empty => simpa using hc0
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih (fun l hl => h l (Finset.mem_insert_of_mem hl))
    have hx : ‖f j‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (f j - 1) 1
      rw [sub_add_cancel, norm_one] at this
      exact this.trans (max_le (h1.trans hc) le_rfl)
    have e : f j * ∏ l ∈ s, f l - 1 = f j * (∏ l ∈ s, f l - 1) + (f j - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h1)
    rw [norm_mul]
    calc ‖f j‖ * ‖∏ l ∈ s, f l - 1‖ ≤ 1 * c := mul_le_mul hx h2 (norm_nonneg _) zero_le_one
      _ = c := one_mul c

private theorem norm_one_sub_le_one_of_norm_le_one {k : Type} [NormedField k] [IsUltrametricDist k] {x : k}
    (h : ‖x‖ ≤ 1) : ‖1 - x‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_one]
  · rw [norm_neg]
    exact h

theorem UpperTheory.Gal.Wt.sepPoly_of :
    UpperTheory.Gal.Wt.Kapl → UpperTheory.Gal.Wt.SepPoly := by
  intro hK k _ _ σ _ Z₁ Z₂ h₁ h₂ hd ε hε
  classical
  obtain ⟨D, hD, hDd⟩ := hd.exists_thickenings h₁ h₂.isClosed
  have he0 : 0 < min ε 1 := lt_min hε one_pos
  have he1 : min ε 1 ≤ 1 := min_le_right _ _
  have heε : min ε 1 ≤ ε := min_le_left _ _
  obtain ⟨T, hTsub, hTfin, hcov⟩ := h₁.finite_cover_balls (mul_pos hD he0)
  obtain ⟨Y, hY, hmemY⟩ : ∃ Y : Set k, IsCompact Y ∧
      ∀ i, ∀ a ∈ hTfin.toFinset, ∀ z ∈ Z₁ ∪ Z₂, z i - a i ∈ Y := by
    refine ⟨⋃ i : σ, ⋃ a ∈ hTfin.toFinset, (fun z : σ → k => z i - a i) '' (Z₁ ∪ Z₂), ?_, ?_⟩
    · exact isCompact_iUnion fun i => hTfin.toFinset.isCompact_biUnion fun a _ =>
        (h₁.union h₂).image (by fun_prop)
    · intro i a ha z hz
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion₂.2 ⟨a, ha, z, hz, rfl⟩⟩
  obtain ⟨p, hp1, hp2, hp3⟩ := hK k Y hY D (min ε 1) hD he0 he1
  obtain ⟨q, hq⟩ : ∃ q : (σ → k) → MvPolynomial σ k,
      ∀ a z, MvPolynomial.eval z (q a) = ∏ i, Polynomial.eval (z i - a i) p :=
    ⟨fun a => ∏ i, Polynomial.aeval (MvPolynomial.X i - MvPolynomial.C (a i)) p,
      fun a z => by simp only [map_prod, mvEval_aeval_X_sub_C_eq_eval_sub]⟩
  have hqle : ∀ a ∈ hTfin.toFinset, ∀ z ∈ Z₁ ∪ Z₂, ‖MvPolynomial.eval z (q a)‖ ≤ 1 := by
    intro a ha z hz
    rw [hq, norm_prod]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hp1 _ (hmemY i a ha z hz))
  refine ⟨1 - ∏ a ∈ hTfin.toFinset, (1 - q a), ?_, ?_⟩
  · intro z hz
    obtain ⟨a0, ha0T, hza⟩ := Set.mem_iUnion₂.1 (hcov hz)
    have ha0 : a0 ∈ hTfin.toFinset := hTfin.mem_toFinset.2 ha0T
    have hnear : ‖MvPolynomial.eval z (q a0) - 1‖ ≤ min ε 1 := by
      rw [hq]
      apply norm_prod_sub_one_le_of_norm_sub_one_le _ _ he0.le he1
      intro i _
      apply hp3
      have := norm_le_pi_norm (z - a0) i
      rw [Metric.mem_ball, dist_eq_norm] at hza
      simp only [Pi.sub_apply] at this
      linarith
    simp only [map_sub, map_one, map_prod]
    rw [show (1 : k) - ∏ a ∈ hTfin.toFinset, (1 - MvPolynomial.eval z (q a)) - 1 =
        -∏ a ∈ hTfin.toFinset, (1 - MvPolynomial.eval z (q a)) by ring, norm_neg, norm_prod,
      ← Finset.mul_prod_erase _ _ ha0]
    have hrest : ∏ a ∈ hTfin.toFinset.erase a0, ‖1 - MvPolynomial.eval z (q a)‖ ≤ 1 := by
      apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
      intro a ha
      exact norm_one_sub_le_one_of_norm_le_one (hqle a (Finset.mem_of_mem_erase ha) z (Or.inl hz))
    have h0 : ‖1 - MvPolynomial.eval z (q a0)‖ ≤ min ε 1 := by
      rw [norm_sub_rev]
      exact hnear
    calc ‖1 - MvPolynomial.eval z (q a0)‖ *
          ∏ a ∈ hTfin.toFinset.erase a0, ‖1 - MvPolynomial.eval z (q a)‖
        ≤ min ε 1 * 1 := mul_le_mul h0 hrest (Finset.prod_nonneg fun _ _ => norm_nonneg _) he0.le
      _ ≤ ε := by linarith
  · intro z hz
    have hfar : ∀ a ∈ hTfin.toFinset, ‖MvPolynomial.eval z (q a)‖ ≤ min ε 1 := by
      intro a ha
      have hdist : D ≤ ‖z - a‖ := by
        by_contra hlt
        push_neg at hlt
        apply Set.disjoint_left.1 hDd
          (Metric.self_subset_thickening hD _ (hTsub (hTfin.mem_toFinset.1 ha)))
        exact Metric.mem_thickening_iff.2 ⟨z, hz, by rw [dist_eq_norm, norm_sub_rev]; exact hlt⟩
      obtain ⟨i, hi⟩ : ∃ i, D ≤ ‖z i - a i‖ := by
        by_contra hno
        push_neg at hno
        have := (pi_norm_lt_iff (x := z - a) hD).2 (fun i => by simpa using hno i)
        linarith
      rw [hq, norm_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      have h0 := hp2 _ (hmemY i a ha z (Or.inr hz)) hi
      have hrest : ∏ j ∈ Finset.univ.erase i, ‖Polynomial.eval (z j - a j) p‖ ≤ 1 :=
        Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => hp1 _ (hmemY j a ha z (Or.inr hz)))
      calc _ ≤ min ε 1 * 1 :=
            mul_le_mul h0 hrest (Finset.prod_nonneg fun _ _ => norm_nonneg _) he0.le
        _ = min ε 1 := mul_one _
    simp only [map_sub, map_one, map_prod]
    have := norm_prod_sub_one_le_of_norm_sub_one_le hTfin.toFinset (fun a => 1 - MvPolynomial.eval z (q a)) he0.le he1
      (fun a ha => by
        rw [show (1 : k) - MvPolynomial.eval z (q a) - 1 = -MvPolynomial.eval z (q a) by ring,
          norm_neg]
        exact hfar a ha)
    rw [norm_sub_rev]
    linarith
