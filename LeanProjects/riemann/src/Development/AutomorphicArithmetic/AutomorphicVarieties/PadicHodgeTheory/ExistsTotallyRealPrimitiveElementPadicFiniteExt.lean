import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section
open Polynomial IntermediateField Filter Topology

private theorem totally_real_of_sign_changes (n : ℕ) (g : ℚ[X]) (hg : g.Monic) (hd : g.natDegree = n)
    (hs : ∀ j < n, aeval ((j : ℝ) - 1 / 2) g * aeval ((j : ℝ) + 1 / 2) g < 0) :
    ∀ z : ℂ, aeval z g = 0 → z.im = 0 := by
  have hroot : ∀ j : Fin n, ∃ r : ℝ, ((j : ℕ) : ℝ) - 1 / 2 < r ∧ r < ((j : ℕ) : ℝ) + 1 / 2 ∧
      aeval r g = 0 := by
    intro j
    have hc : ContinuousOn (fun x : ℝ => aeval x g)
        (Set.Icc (((j : ℕ) : ℝ) - 1 / 2) (((j : ℕ) : ℝ) + 1 / 2)) :=
      (Polynomial.continuous_aeval g).continuousOn
    have hle : ((j : ℕ) : ℝ) - 1 / 2 ≤ ((j : ℕ) : ℝ) + 1 / 2 := by linarith
    rcases mul_neg_iff.1 (hs j j.2) with h | h
    · obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' hle hc ⟨h.2, h.1⟩
      exact ⟨r, hr.1, hr.2, hr0⟩
    · obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo hle hc ⟨h.1, h.2⟩
      exact ⟨r, hr.1, hr.2, hr0⟩
  choose r hr1 hr2 hr0 using hroot
  have hinj : Function.Injective fun j : Fin n => ((r j : ℝ) : ℂ) := by
    intro i j hij
    have hij' : r i = r j := Complex.ofReal_injective hij
    have h1 : ((i : ℕ) : ℝ) < (j : ℕ) + 1 := by linarith [hr1 i, hr2 j]
    have h2 : ((j : ℕ) : ℝ) < (i : ℕ) + 1 := by linarith [hr1 j, hr2 i]
    have h1' : (i : ℕ) < (j : ℕ) + 1 := by exact_mod_cast h1
    have h2' : (j : ℕ) < (i : ℕ) + 1 := by exact_mod_cast h2
    exact Fin.ext (by omega)
  intro z hz
  by_contra hzim
  classical
  have hne : g.map (algebraMap ℚ ℂ) ≠ 0 := (hg.map _).ne_zero
  have hnot : z ∉ (Finset.univ : Finset (Fin n)).image fun j : Fin n => ((r j : ℝ) : ℂ) := by
    intro hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hmem
    exact hzim (by rw [← hj]; simp)
  have hcard := Polynomial.card_le_degree_of_subset_roots (p := g.map (algebraMap ℚ ℂ))
    (Z := insert z ((Finset.univ : Finset (Fin n)).image fun j : Fin n => ((r j : ℝ) : ℂ))) (by
      intro x hx
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
      rcases Finset.mem_insert.1 (Finset.mem_def.2 hx) with rfl | hx
      · exact hz
      · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hx
        rw [← hj]
        have := Polynomial.aeval_algebraMap_apply ℂ (r j) g
        rw [hr0 j, map_zero] at this
        exact this)
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj,
    Polynomial.natDegree_map, hd] at hcard
  simp at hcard

private theorem sign_change_between_integers (n j : ℕ) (hj : j < n) :
    aeval ((j : ℝ) - 1 / 2) (∏ i ∈ Finset.range n, (X - C (i : ℚ)) : ℚ[X]) *
      aeval ((j : ℝ) + 1 / 2) (∏ i ∈ Finset.range n, (X - C (i : ℚ)) : ℚ[X]) < 0 := by
  rw [map_prod, map_prod, ← Finset.prod_mul_distrib,
    ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hj)]
  refine mul_neg_of_neg_of_pos ?_ (Finset.prod_pos fun i hi => ?_)
  · simp
  · have hij : i ≠ j := (Finset.mem_erase.1 hi).1
    simp only [map_sub, aeval_X, aeval_C, eq_ratCast, Rat.cast_natCast]
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      apply mul_pos <;> linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      apply mul_pos_of_neg_of_neg <;> linarith

private theorem approx_monic_totally_real_rational (l : ℕ) [Fact l.Prime] (f : ℚ_[l][X]) (hf : f.Monic)
    (ε : ℝ) (hε : ε > 0) :
    ∃ g : ℚ[X], g.Monic ∧ f.natDegree = g.natDegree ∧
      (∀ i, ‖(g.map (algebraMap ℚ ℚ_[l])).coeff i - f.coeff i‖ < ε) ∧
      ∀ z : ℂ, aeval z g = 0 → z.im = 0 := by
  obtain ⟨g₀, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
      (Padic.denseRange_ratCast l) hf hε
  set n := g₀.natDegree with hn
  set h : ℚ[X] := ∏ i ∈ Finset.range n, (X - C (i : ℚ)) with hh
  have hmon : h.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hdeg : h.natDegree = n := by
    rw [hh, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C]
    simp
  have hdlt : (g₀ - h).degree < h.degree := by
    have e : g₀.degree = h.degree := by
      rw [degree_eq_natDegree gmon.ne_zero, degree_eq_natDegree hmon.ne_zero, hdeg]
    rw [← e]
    exact degree_sub_lt e gmon.ne_zero (by rw [gmon.leadingCoeff, hmon.leadingCoeff])
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  let u : ℕ → ℚ := fun N => (1 + (l : ℚ) ^ N)⁻¹
  have huR : Tendsto (fun N => ((u N : ℚ) : ℝ)) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => 1 + (l : ℝ) ^ N) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop_atTop_of_one_lt hl)
    have := this.inv_tendsto_atTop
    refine this.congr fun N => ?_
    simp [u]
  have huP : Tendsto (fun N => ((u N : ℚ) : ℚ_[l])) atTop (𝓝 1) := by
    have h1 : Tendsto (fun N : ℕ => (l : ℚ_[l]) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
    have h2 := ((tendsto_const_nhds (x := (1 : ℚ_[l]))).add h1).inv₀ (by simp)
    simp only [add_zero, inv_one] at h2
    refine h2.congr fun N => ?_
    simp [u]
  have hG : ∀ N, (h + C (u N) * (g₀ - h)).Monic ∧ (h + C (u N) * (g₀ - h)).natDegree = n := by
    intro N
    have hlt : (C (u N) * (g₀ - h)).degree < h.degree := by
      rw [← smul_eq_C_mul]
      exact (degree_smul_le _ _).trans_lt hdlt
    exact ⟨hmon.add_of_left hlt, by rw [natDegree_add_eq_left_of_degree_lt hlt, hdeg]⟩
  have e1 : ∀ᶠ N in atTop, ∀ j ∈ Finset.range n,
      aeval ((j : ℝ) - 1 / 2) (h + C (u N) * (g₀ - h)) *
        aeval ((j : ℝ) + 1 / 2) (h + C (u N) * (g₀ - h)) < 0 := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hev : ∀ x : ℝ, Tendsto (fun N => aeval x (h + C (u N) * (g₀ - h))) atTop
        (𝓝 (aeval x h)) := by
      intro x
      have := (tendsto_const_nhds (x := aeval x h)).add (huR.mul_const (aeval x (g₀ - h)))
      simp only [zero_mul, add_zero] at this
      refine this.congr fun N => ?_
      simp only [map_add, map_mul, aeval_C, eq_ratCast]
    exact ((hev _).mul (hev _)).eventually
      (gt_mem_nhds (sign_change_between_integers n j (Finset.mem_range.1 hj)))
  have e2 : ∀ᶠ N in atTop, ∀ i ∈ Finset.range (n + 1),
      ‖((h + C (u N) * (g₀ - h)).map (algebraMap ℚ ℚ_[l])).coeff i - f.coeff i‖ < ε := by
    rw [Filter.eventually_all_finset]
    intro i _
    have hev : Tendsto (fun N => ((h + C (u N) * (g₀ - h)).map (algebraMap ℚ ℚ_[l])).coeff i)
        atTop (𝓝 ((g₀.map (algebraMap ℚ ℚ_[l])).coeff i)) := by
      have := (tendsto_const_nhds (x := ((h.coeff i : ℚ) : ℚ_[l]))).add
        (huP.mul_const (((g₀.coeff i : ℚ) : ℚ_[l]) - ((h.coeff i : ℚ) : ℚ_[l])))
      simp only [one_mul, add_sub_cancel] at this
      simp only [coeff_map, coeff_add, coeff_C_mul, coeff_sub, eq_ratCast]
      refine this.congr fun N => ?_
      push_cast
      ring
    exact ((hev.sub_const _).norm).eventually (gt_mem_nhds (gcoeff i))
  obtain ⟨N, hN1, hN2⟩ := (e1.and e2).exists
  refine ⟨h + C (u N) * (g₀ - h), (hG N).1, by rw [(hG N).2, gdeg], fun i => ?_,
    totally_real_of_sign_changes n _ (hG N).1 (hG N).2 fun j hj => hN1 j (Finset.mem_range.2 hj)⟩
  by_cases hi : i < n + 1
  · exact hN2 i (Finset.mem_range.2 hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_map, (hG N).2]; omega),
      coeff_eq_zero_of_natDegree_lt (by rw [gdeg]; omega)]
    simpa using hε

private theorem krasner_totally_real_generator (l : ℕ) [Fact l.Prime] (α : PadicAlgCl l) :
    ∃ β : PadicAlgCl l, ∃ g : ℚ[X], g.Monic ∧ g.natDegree = (minpoly ℚ_[l] α).natDegree ∧
      aeval β g = 0 ∧ (∀ z : ℂ, aeval z g = 0 → z.im = 0) ∧ α ∈ ℚ_[l]⟮β⟯ := by
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have fmon : (minpoly ℚ_[l] α).Monic := minpoly.monic (hint α)
  have fa0 : (minpoly ℚ_[l] α).aeval α = 0 := minpoly.aeval _ _
  have hfin : ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)).Finite := by
    refine ((minpoly ℚ_[l] α).rootSet_finite (PadicAlgCl l)).subset fun x' hx' => ?_
    exact (isConjRoot_iff_mem_minpoly_rootSet (hint α)).1 hx'.1
  have hop : IsOpen (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖α - y‖ < ‖α - x'‖}) :=
    hfin.isOpen_biInter fun x' _ => isOpen_lt (by fun_prop) continuous_const
  have hmem : α ∈ (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖α - y‖ < ‖α - x'‖}) := by
    simp only [Set.mem_iInter, Set.mem_setOf_eq, sub_self, norm_zero, norm_pos_iff, sub_ne_zero]
    exact fun x' h => h.2
  obtain ⟨δ, δpos, hball⟩ := Metric.isOpen_iff.1 hop α hmem
  have hn : (minpoly ℚ_[l] α).natDegree ≠ 0 := (minpoly.natDegree_pos (hint α)).ne'
  have hε : (δ / (max ‖α‖ 1)) ^ (minpoly ℚ_[l] α).natDegree /
      ((minpoly ℚ_[l] α).natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff, greal⟩ := approx_monic_totally_real_rational l _ fmon _ hε
  obtain ⟨β, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (L := PadicAlgCl l)
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖α - β‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖α‖ 1) > 0).ne'] using hab
    · simp [hn]
    · positivity
  have hβU := hball
    (show β ∈ Metric.ball α δ by rw [Metric.mem_ball, dist_comm, dist_eq_norm]; exact hab)
  have hgβ : aeval β g = 0 := by
    rw [Polynomial.mem_aroots] at hb
    simpa [Polynomial.aeval_map_algebraMap] using hb.2
  refine ⟨β, g, gmon, gdeg.symm, hgβ, greal, ?_⟩
  refine IsKrasner.krasner (minpoly.irreducible (hint α)).separable (IsAlgClosed.splits _)
    (hint β) fun x' h1 h2 => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hβU
  exact hβU x' ⟨h1, h2⟩

private theorem exists_totally_real_generator (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ (β : PadicAlgCl l) (g : ℚ[X]), g.Monic ∧ aeval β g = 0 ∧
      (∀ z : ℂ, aeval z g = 0 → z.im = 0) ∧ ℚ_[l]⟮β⟯ = K := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ_[l] K
  have hKα : K = ℚ_[l]⟮(α : PadicAlgCl l)⟯ := by
    rw [← IntermediateField.lift_adjoin_simple, hα, IntermediateField.lift_top]
  obtain ⟨β, g, gmon, gdeg, hgβ, greal, hαβ⟩ := krasner_totally_real_generator l (α : PadicAlgCl l)
  refine ⟨β, g, gmon, hgβ, greal, ?_⟩
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  rw [hKα]
  symm
  haveI : FiniteDimensional ℚ_[l] ℚ_[l]⟮β⟯ := IntermediateField.adjoin.finiteDimensional (hint β)
  refine IntermediateField.eq_of_le_of_finrank_le
    (IntermediateField.adjoin_simple_le_iff.2 hαβ) ?_
  rw [IntermediateField.adjoin.finrank (hint β), IntermediateField.adjoin.finrank (hint _), ← gdeg]
  have hg0 : g.map (algebraMap ℚ ℚ_[l]) ≠ 0 := (gmon.map _).ne_zero
  have hdvd : minpoly ℚ_[l] β ∣ g.map (algebraMap ℚ ℚ_[l]) :=
    minpoly.dvd _ _ (by rw [Polynomial.aeval_map_algebraMap]; exact hgβ)
  calc (minpoly ℚ_[l] β).natDegree ≤ (g.map (algebraMap ℚ ℚ_[l])).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hg0
    _ = g.natDegree := g.natDegree_map _

end

theorem UpperTheory.exists_totally_real_primitive_element_padic_finite_ext :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ (β : Om l) (g : Polynomial ℚ), g.Monic ∧ Polynomial.aeval β g = 0 ∧ (∀ z : ℂ, Polynomial.aeval z g = 0 → z.im = 0) ∧ IntermediateField.adjoin ℚ_[l] {β} = K.1 := by
  intro l _ K
  haveI := K.2
  exact exists_totally_real_generator l K.1
