import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumberFieldAdjoinEq

open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField

namespace UpperTheory.V.RealGen

open Polynomial IntermediateField Filter Topology

private noncomputable def model (n : ℕ) : ℚ[X] :=
  ∏ i ∈ Finset.range n, (X - C ((i : ℚ) + 1 / 2))

end UpperTheory.V.RealGen

open Polynomial in
private theorem model_eval_mul_eval_succ_neg (n j : ℕ) (hj : j < n) :
    (UpperTheory.V.RealGen.model n).eval (j : ℚ) * (UpperTheory.V.RealGen.model n).eval ((j : ℚ) + 1) < 0 := by
  unfold UpperTheory.V.RealGen.model
  rw [eval_prod, eval_prod, ← Finset.prod_mul_distrib]
  have hmem : j ∈ Finset.range n := Finset.mem_range.mpr hj
  rw [← Finset.mul_prod_erase _ _ hmem]
  have hpos : 0 < ∏ i ∈ (Finset.range n).erase j,
      (eval (j : ℚ) (X - C ((i : ℚ) + 1 / 2)) * eval ((j : ℚ) + 1) (X - C ((i : ℚ) + 1 / 2))) := by
    apply Finset.prod_pos
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp only [eval_sub, eval_X, eval_C]
    have h1 : (1 : ℚ) ≤ ((j : ℚ) - i) ^ 2 := by
      rcases lt_or_gt_of_ne hij with h | h
      · have : (i : ℚ) + 1 ≤ j := by exact_mod_cast h
        nlinarith
      · have : (j : ℚ) + 1 ≤ i := by exact_mod_cast h
        nlinarith
    nlinarith
  have hneg : eval (j : ℚ) (X - C ((j : ℚ) + 1 / 2)) * eval ((j : ℚ) + 1) (X - C ((j : ℚ) + 1 / 2)) < 0 := by
    simp only [eval_sub, eval_X, eval_C]
    norm_num
  exact mul_neg_of_neg_of_pos hneg hpos

open Polynomial in
private theorem model_monic_natDegree (n : ℕ) :
    (UpperTheory.V.RealGen.model n).Monic ∧ (UpperTheory.V.RealGen.model n).natDegree = n := by
  unfold UpperTheory.V.RealGen.model
  refine ⟨monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _), ?_⟩
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

open Polynomial in
private theorem splits_real_of_sign_changing_at_integers (g : ℚ[X]) (n : ℕ) (hmon : g.Monic) (hdeg : g.natDegree = n)
    (halt : ∀ j < n, g.eval (j : ℚ) * g.eval ((j : ℚ) + 1) < 0) :
    (g.map (algebraMap ℚ ℝ)).Splits := by
  set G := g.map (algebraMap ℚ ℝ) with hGdef
  have hev : ∀ x : ℚ, G.eval (x : ℝ) = ((g.eval x : ℚ) : ℝ) := by
    intro x
    rw [hGdef, eval_map, show (x : ℝ) = algebraMap ℚ ℝ x from rfl, eval₂_at_apply]; rfl
  have hroot : ∀ j : Fin n, ∃ x ∈ Set.Ioo (((j : ℕ) : ℝ)) (((j : ℕ) : ℝ) + 1), G.eval x = 0 := by
    intro j
    have hj := halt j j.2
    have hcont : ContinuousOn (fun x => G.eval x) (Set.Icc (((j : ℕ) : ℝ)) (((j : ℕ) : ℝ) + 1)) :=
      G.continuous.continuousOn
    have h0 : (((j : ℕ) : ℝ)) ≤ ((j : ℕ) : ℝ) + 1 := by linarith
    have e1 : G.eval (((j : ℕ) : ℝ)) = ((g.eval ((j : ℕ) : ℚ) : ℚ) : ℝ) := by
      rw [← hev]; norm_cast
    have e2 : G.eval (((j : ℕ) : ℝ) + 1) = ((g.eval (((j : ℕ) : ℚ) + 1) : ℚ) : ℝ) := by
      rw [← hev]; push_cast; rfl
    rcases mul_neg_iff.mp hj with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' h0 hcont
        (show (0 : ℝ) ∈ Set.Ioo (G.eval (((j : ℕ) : ℝ) + 1)) (G.eval (((j : ℕ) : ℝ))) from
          ⟨by rw [e2]; exact_mod_cast hb, by rw [e1]; exact_mod_cast ha⟩)
      exact ⟨x, hx, hx0⟩
    · obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo h0 hcont
        (show (0 : ℝ) ∈ Set.Ioo (G.eval (((j : ℕ) : ℝ))) (G.eval (((j : ℕ) : ℝ) + 1)) from
          ⟨by rw [e1]; exact_mod_cast ha, by rw [e2]; exact_mod_cast hb⟩)
      exact ⟨x, hx, hx0⟩
  choose r hr hr0 using hroot
  have hinj : Function.Injective r := by
    intro a b hab
    have ha := hr a
    have hb := hr b
    rw [hab] at ha
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast h
      linarith [ha.2, hb.1]
    · have : ((b : ℕ) : ℝ) + 1 ≤ ((a : ℕ) : ℝ) := by exact_mod_cast h
      linarith [ha.1, hb.2]
  have hG0 : G ≠ 0 := (hmon.map (algebraMap ℚ ℝ)).ne_zero
  have hsub : Finset.univ.image r ⊆ G.roots.toFinset := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots hG0]
    exact hr0 j
  have hcard : n ≤ G.roots.card := by
    calc n = (Finset.univ.image r).card := by
          rw [Finset.card_image_of_injective _ hinj]; simp
      _ ≤ G.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ G.roots.card := Multiset.toFinset_card_le _
  have hdG : G.natDegree = n := by
    rw [hGdef, natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective, hdeg]
  rw [splits_iff_card_roots]
  exact le_antisymm (card_roots' G) (hdG ▸ hcard)

open Polynomial in
private theorem exists_root_near_of_aeval_small (l : ℕ) [Fact l.Prime] (g : ℚ[X]) (n : ℕ) (hmon : g.Monic)
    (hdeg : g.natDegree = n) (α : Om l) (δ : ℝ) (hδ : 0 < δ) (hsmall : ‖aeval α g‖ < δ ^ n) :
    ∃ β : Om l, aeval β g = 0 ∧ ‖α - β‖ < δ := by
  set G := g.map (algebraMap ℚ (Om l)) with hGdef
  have hGm : G.Monic := hmon.map _
  have hsp : G.Splits := IsAlgClosed.splits G
  have hprod := hsp.eq_prod_roots_of_monic hGm
  have hcard : G.roots.card = n := by
    rw [splits_iff_card_roots.mp hsp, hGdef,
      natDegree_map_eq_of_injective (algebraMap ℚ (Om l)).injective, hdeg]
  have hev : aeval α g = (G.roots.map (fun b => α - b)).prod := by
    rw [aeval_def, ← eval_map, ← hGdef]
    conv_lhs => rw [hprod]
    rw [eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro b _
    simp
  by_contra hno
  push_neg at hno
  have hle : δ ^ n ≤ ‖aeval α g‖ := by
    rw [hev]
    show δ ^ n ≤ (normHom : Om l →*₀ ℝ) _
    rw [map_multiset_prod, Multiset.map_map]
    have h2 : (G.roots.map (fun _ => δ)).prod ≤
        (G.roots.map ((normHom : Om l →*₀ ℝ) ∘ fun b => α - b)).prod := by
      apply Multiset.prod_map_le_prod_map₀
      · intro _ _; exact hδ.le
      intro b hb
      have hroot : aeval b g = 0 := by
        rw [aeval_def, ← eval_map, ← hGdef]
        exact (mem_roots hGm.ne_zero).mp hb
      simpa using hno b hroot
    calc δ ^ n = (G.roots.map (fun _ => δ)).prod := by
          rw [Multiset.map_const', Multiset.prod_replicate, hcard]
      _ ≤ _ := h2
  linarith

open Polynomial in
private theorem exists_rat_monic_aeval_close (l : ℕ) [Fact l.Prime] (f : ℚ_[l][X]) (hf : f.Monic) (n : ℕ)
    (hn : f.natDegree = n) (α : Om l) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℚ[X], g.Monic ∧ g.natDegree = n ∧ ‖aeval α g - aeval α f‖ < ε := by
  set S : ℝ := ∑ i : Fin n, ‖α‖ ^ (i : ℕ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => by positivity)
  have hB : 0 < S + 1 := by linarith
  have hq : ∀ i : Fin n, ∃ r : ℚ, ‖f.coeff i - (r : ℚ_[l])‖ < ε / (S + 1) :=
    fun i => Padic.rat_dense l _ (by positivity)
  choose q hq using hq
  set p : ℚ[X] := ∑ i : Fin n, C (q i) * X ^ (i : ℕ) with hp
  have hpd : p.degree < n := degree_sum_fin_lt q
  have hdX : (X ^ n : ℚ[X]).degree = n := degree_X_pow n
  refine ⟨X ^ n + p, monic_X_pow_add hpd, ?_, ?_⟩
  · rw [natDegree_add_eq_left_of_degree_lt (by rw [hdX]; exact hpd), natDegree_X_pow]
  · have hf' : f = X ^ n + ∑ i : Fin n, C (f.coeff i) * X ^ (i : ℕ) := by
      conv_lhs => rw [hf.as_sum]
      rw [hn, Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) n]
    have e : aeval α (X ^ n + p) - aeval α f =
        ∑ i : Fin n, algebraMap ℚ_[l] (Om l) ((q i : ℚ_[l]) - f.coeff i) * α ^ (i : ℕ) := by
      conv_lhs => rw [hf', hp]
      simp only [map_add, map_sum, map_mul, aeval_C, aeval_X_pow, add_sub_add_left_eq_sub,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_sub, sub_mul, map_ratCast]
      simp
    rw [e]
    calc ‖∑ i : Fin n, algebraMap ℚ_[l] (Om l) ((q i : ℚ_[l]) - f.coeff i) * α ^ (i : ℕ)‖
        ≤ ∑ i : Fin n, ‖algebraMap ℚ_[l] (Om l) ((q i : ℚ_[l]) - f.coeff i) * α ^ (i : ℕ)‖ :=
          norm_sum_le _ _
      _ = ∑ i : Fin n, ‖(q i : ℚ_[l]) - f.coeff i‖ * ‖α‖ ^ (i : ℕ) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_mul, norm_pow, norm_algebraMap']
      _ ≤ ∑ i : Fin n, ε / (S + 1) * ‖α‖ ^ (i : ℕ) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [norm_sub_rev]
          exact (hq i).le
      _ = ε / (S + 1) * S := by rw [hS, Finset.mul_sum]
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hB]
          nlinarith

open Polynomial in
private theorem exists_rat_monic_close_sign_changing_at_integers (l : ℕ) [Fact l.Prime] (g₁ : ℚ[X]) (n : ℕ) (hn : 0 < n)
    (hmon : g₁.Monic) (hdeg : g₁.natDegree = n) (α : Om l) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℚ[X], g.Monic ∧ g.natDegree = n ∧ ‖aeval α g - aeval α g₁‖ < ε ∧
      ∀ j < n, g.eval (j : ℚ) * g.eval ((j : ℚ) + 1) < 0 := by
  set M := UpperTheory.V.RealGen.model n with hM
  obtain ⟨hMm, hMd⟩ := model_monic_natDegree n
  rw [← hM] at hMm hMd
  have hMs : ∀ j < n, M.eval (j : ℚ) * M.eval ((j : ℚ) + 1) < 0 := fun j hj => model_eval_mul_eval_succ_neg n j hj
  have hMnz : ∀ j ∈ Finset.range (n + 1), M.eval (j : ℚ) ≠ 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases Nat.lt_or_ge j n with h | h
    · exact left_ne_zero_of_mul (hMs j h).ne
    · have hjn : j = n := by omega
      have h2 := hMs (n - 1) (by omega)
      have e : ((n - 1 : ℕ) : ℚ) + 1 = (j : ℚ) := by
        rw [hjn, Nat.cast_sub (by omega)]; push_cast; ring
      rw [e] at h2
      exact right_ne_zero_of_mul h2.ne
  set D : ℚ := ∑ j ∈ Finset.range (n + 1), (|g₁.eval (j : ℚ)| + 1) / |M.eval (j : ℚ)| with hD
  have hDj : ∀ j ∈ Finset.range (n + 1), (|g₁.eval (j : ℚ)| + 1) / |M.eval (j : ℚ)| ≤ D := by
    intro j hj
    exact Finset.single_le_sum (f := fun j : ℕ => (|g₁.eval (j : ℚ)| + 1) / |M.eval (j : ℚ)|)
      (fun i _ => by positivity) hj
  have hD0 : 0 < D := by
    have h0 : (0 : ℕ) ∈ Finset.range (n + 1) := by simp
    have hp : 0 < (|g₁.eval ((0 : ℕ) : ℚ)| + 1) / |M.eval ((0 : ℕ) : ℚ)| := by
      have := hMnz 0 h0
      positivity
    exact lt_of_lt_of_le hp (hDj 0 h0)
  set A : ℝ := ‖aeval α (M - g₁)‖ with hA
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (max (A / ε) (2 * (D : ℝ))) hl1
  set L : ℚ := (l : ℚ) ^ (k + 1) with hL
  have hLpos : 0 < L := pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  have hLk : ((l : ℝ)) ^ k ≤ (L : ℝ) := by
    rw [hL]; push_cast
    exact pow_le_pow_right₀ hl1.le (Nat.le_succ k)
  set t : ℚ := L / (L + 1) with ht
  have ht0 : t ≠ 0 := by positivity
  have hdiff : (M - g₁).degree < g₁.degree := by
    have := degree_sub_lt (p := M) (q := g₁)
      (by rw [degree_eq_natDegree hMm.ne_zero, degree_eq_natDegree hmon.ne_zero, hMd, hdeg])
      hMm.ne_zero (by rw [hMm.leadingCoeff, hmon.leadingCoeff])
    rwa [degree_eq_natDegree hMm.ne_zero, hMd, ← hdeg, ← degree_eq_natDegree hmon.ne_zero] at this
  have hCd : (C t * (M - g₁)).degree < g₁.degree := by
    rw [degree_C_mul ht0]; exact hdiff
  refine ⟨g₁ + C t * (M - g₁), hmon.add_of_left hCd, ?_, ?_, ?_⟩
  · rw [natDegree_add_eq_left_of_degree_lt hCd, hdeg]
  · have e : aeval α (g₁ + C t * (M - g₁)) - aeval α g₁ = algebraMap ℚ (Om l) t * aeval α (M - g₁) := by
      rw [map_add, add_sub_cancel_left, map_mul, aeval_C]
    rw [e, norm_mul, IsScalarTower.algebraMap_apply ℚ ℚ_[l] (Om l), norm_algebraMap', ← hA]
    have hnL : ‖((L : ℚ) : ℚ_[l])‖ = (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
      rw [hL]; push_cast; exact Padic.norm_p_pow (k + 1)
    have hlt : ‖((L : ℚ) : ℚ_[l])‖ < 1 := by
      rw [hnL]
      apply zpow_lt_one_of_neg₀ hl1
      omega
    have hn1 : ‖((L : ℚ) : ℚ_[l]) + 1‖ = 1 := by
      rw [Padic.add_eq_max_of_ne (by rw [norm_one]; exact hlt.ne), norm_one]
      exact max_eq_right hlt.le
    have hnt : ‖((t : ℚ) : ℚ_[l])‖ = (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
      rw [ht]; push_cast
      rw [norm_div, hn1, div_one, hnL]
      push_cast; rfl
    rw [eq_ratCast (algebraMap ℚ ℚ_[l]) t, hnt]
    have hA0 : 0 ≤ A := norm_nonneg _
    have hkA : A / ε < (l : ℝ) ^ k := lt_of_le_of_lt (le_max_left _ _) hk
    have hA' : A < ε * (l : ℝ) ^ k := by rwa [div_lt_iff₀ hε, mul_comm] at hkA
    have hz : (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) = 1 / ((l : ℝ) ^ k * l) := by
      rw [zpow_neg, zpow_natCast, pow_succ, one_div]
    rw [hz, one_div_mul_eq_div, div_lt_iff₀ (by positivity)]
    nlinarith
  · intro j hj
    have hkD : 2 * (D : ℝ) < (L : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hk) hLk
    have hkD' : 2 * D < L := by exact_mod_cast hkD
    have sgn : ∀ i ∈ Finset.range (n + 1),
        0 < (g₁ + C t * (M - g₁)).eval (i : ℚ) * M.eval (i : ℚ) := by
      intro i hi
      have hMi := hMnz i hi
      have hbi := hDj i hi
      set a := g₁.eval (i : ℚ)
      set m := M.eval (i : ℚ)
      have hm : 0 < |m| := abs_pos.mpr hMi
      have hb : |a| + 1 ≤ D * |m| := by rwa [div_le_iff₀ hm] at hbi
      have ev : (g₁ + C t * (M - g₁)).eval (i : ℚ) = a + t * (m - a) := by
        simp [a, m]
      rw [ev]
      have hL1 : 0 < L + 1 := by linarith
      have key : (a + t * (m - a)) * m * (L + 1) = a * m + L * m * m := by
        rw [ht]; field_simp; ring
      have hmm : m * m = |m| * |m| := (abs_mul_abs_self m).symm
      have ham : -(|a| * |m|) ≤ a * m := by
        have := neg_abs_le (a * m); rwa [abs_mul] at this
      have h3 : (|a| + 1) * |m| ≤ D * |m| * |m| := by nlinarith
      have h4 : 2 * D * (|m| * |m|) < L * (|m| * |m|) := by
        apply mul_lt_mul_of_pos_right hkD'; positivity
      have hLm : L * m * m = L * (|m| * |m|) := by rw [mul_assoc, hmm]
      have h5 : 0 < (a + t * (m - a)) * m * (L + 1) := by
        rw [key, hLm]; nlinarith
      exact lt_of_mul_lt_mul_right (by rw [zero_mul]; exact h5) hL1.le
    have s1 := sgn j (by rw [Finset.mem_range]; omega)
    have s2 := sgn (j + 1) (by rw [Finset.mem_range]; omega)
    push_cast at s2
    have hm := hMs j hj
    nlinarith [mul_pos s1 s2]

open Polynomial IntermediateField in
theorem UpperTheory.exists_real_split_primitive_element_padic_finite_ext :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ (β : Om l) (g : Polynomial ℚ), g.Monic ∧ (g.map (algebraMap ℚ ℝ)).Splits ∧ Polynomial.aeval β g = 0 ∧ IntermediateField.adjoin ℚ_[l] {β} = K.1 := by
  classical
  intro l _ K
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨α₀, hα₀⟩ := Field.exists_primitive_element ℚ_[l] K.1
  set α : Om l := (α₀ : Om l) with hαdef
  have hαK : α ∈ K.1 := α₀.2
  have hint : IsIntegral ℚ_[l] α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set f := minpoly ℚ_[l] α with hfdef
  set n := f.natDegree with hndef
  have hfm : f.Monic := minpoly.monic hint
  have hn : 0 < n := minpoly.natDegree_pos hint
  have hKn : Module.finrank ℚ_[l] K.1 = n := by
    have h1 : Module.finrank ℚ_[l] (ℚ_[l]⟮α₀⟯) = (minpoly ℚ_[l] α₀).natDegree :=
      IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α₀)
    rw [hα₀, IntermediateField.finrank_top', IntermediateField.minpoly_eq] at h1
    exact h1
  have hKeq : ℚ_[l]⟮α⟯ = K.1 := by
    apply IntermediateField.eq_of_le_of_finrank_le (IntermediateField.adjoin_simple_le_iff.mpr hαK)
    rw [IntermediateField.adjoin.finrank hint, hKn]
  set R := (f.map (algebraMap ℚ_[l] (Om l))).roots.toFinset.erase α with hR
  have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ R, δ ≤ ‖α - x‖ := by
    by_cases hne : R.Nonempty
    · obtain ⟨x0, hx0, hmin⟩ := R.exists_min_image (fun x => ‖α - x‖) hne
      refine ⟨‖α - x0‖, ?_, hmin⟩
      rw [norm_pos_iff, sub_ne_zero]
      exact (Finset.ne_of_mem_erase hx0).symm
    · refine ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  obtain ⟨δ, hδ0, hδR⟩ := hδ
  have hε : 0 < δ ^ n / 2 := by positivity
  obtain ⟨g₁, hg₁m, hg₁d, hg₁⟩ := exists_rat_monic_aeval_close l f hfm n rfl α (δ ^ n / 2) hε
  obtain ⟨g, hgm, hgd, hg, halt⟩ := exists_rat_monic_close_sign_changing_at_integers l g₁ n hn hg₁m hg₁d α (δ ^ n / 2) hε
  have hf0 : Polynomial.aeval α f = 0 := minpoly.aeval ℚ_[l] α
  have hsmall : ‖Polynomial.aeval α g‖ < δ ^ n := by
    have e : Polynomial.aeval α g =
        (Polynomial.aeval α g - Polynomial.aeval α g₁) + (Polynomial.aeval α g₁ - Polynomial.aeval α f) := by
      rw [hf0]; ring
    rw [e]
    calc _ ≤ ‖Polynomial.aeval α g - Polynomial.aeval α g₁‖ + ‖Polynomial.aeval α g₁ - Polynomial.aeval α f‖ :=
          norm_add_le _ _
      _ < δ ^ n / 2 + δ ^ n / 2 := add_lt_add hg hg₁
      _ = δ ^ n := by ring
  obtain ⟨β, hβ, hαβ⟩ := exists_root_near_of_aeval_small l g n hgm hgd α δ hδ0 hsmall
  have hβint : IsIntegral ℚ_[l] β := (Algebra.IsAlgebraic.isAlgebraic β).isIntegral
  have hαβK : α ∈ ℚ_[l]⟮β⟯ := by
    apply IsKrasner.krasner (minpoly.irreducible hint).separable (IsAlgClosed.splits _) hβint
    intro x' hconj hne
    have hx' : x' ∈ R := by
      rw [hR, Finset.mem_erase, Multiset.mem_toFinset,
        Polynomial.mem_roots (Polynomial.map_monic_ne_zero hfm), Polynomial.IsRoot,
        Polynomial.eval_map_algebraMap]
      exact ⟨fun h => hne h.symm, hconj.aeval_eq_zero⟩
    exact lt_of_lt_of_le hαβ (hδR x' hx')
  refine ⟨β, g, hgm, splits_real_of_sign_changing_at_integers g n hgm hgd halt, hβ, ?_⟩
  haveI : FiniteDimensional ℚ_[l] (ℚ_[l]⟮β⟯) := IntermediateField.adjoin.finiteDimensional hβint
  symm
  apply IntermediateField.eq_of_le_of_finrank_le
  · rw [← hKeq]; exact IntermediateField.adjoin_simple_le_iff.mpr hαβK
  · rw [IntermediateField.adjoin.finrank hβint, hKn]
    have hgm' : (g.map (algebraMap ℚ ℚ_[l])).Monic := hgm.map _
    have hdvd : minpoly ℚ_[l] β ∣ g.map (algebraMap ℚ ℚ_[l]) := by
      apply minpoly.dvd
      rw [Polynomial.aeval_map_algebraMap]
      exact hβ
    calc (minpoly ℚ_[l] β).natDegree ≤ (g.map (algebraMap ℚ ℚ_[l])).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd hgm'.ne_zero
      _ = n := by rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℚ_[l]).injective, hgd]
