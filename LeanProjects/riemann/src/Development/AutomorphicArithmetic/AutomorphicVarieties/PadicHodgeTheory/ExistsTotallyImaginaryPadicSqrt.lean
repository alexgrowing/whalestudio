import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTotallyRealPrimitiveElementPadicFiniteExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsCMOfConjAlt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem isCM_of_conj (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h : ∀ x : K, ∃ y : K, ∀ φ : K →+* ℂ, φ y = starRingEnd ℂ (φ x)) : IsCMField K :=
  _root_.UpperTheory.Reformulated.B.Qh9.isCM_of_conj K h

private theorem exists_root_lift {Ω M : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Field M] [CharZero M]
    (j : Ω →+* M) (g : Polynomial ℚ) (hg : g ≠ 0) (β : M) (hβ : Polynomial.aeval β g = 0) :
    ∃ b : Ω, j b = β ∧ Polynomial.aeval b g = 0 := by
  have hs : (g.map (algebraMap ℚ Ω)).Splits := IsAlgClosed.splits _
  have hne : g.map (algebraMap ℚ Ω) ≠ 0 := Polynomial.map_ne_zero hg
  have hroot : ((g.map (algebraMap ℚ Ω)).map j).IsRoot β := by
    rw [Polynomial.map_map, Subsingleton.elim (j.comp (algebraMap ℚ Ω)) (algebraMap ℚ M)]
    simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hβ
  obtain ⟨b, hb⟩ := hs.mem_range_of_isRoot hne hroot
  refine ⟨b, hb, j.injective ?_⟩
  have := Polynomial.aeval_algHom_apply j.toRatAlgHom b g
  rw [map_zero]
  change Polynomial.aeval (j b) g = j _ at this
  rw [← this, hb, hβ]

private theorem exists_sqrt_padic (l : ℕ) [Fact l.Prime] : ∃ d : ℚ_[l], d ^ 2 = 1 - 4 * l := by
  let P : Polynomial ℤ_[l] := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (l : ℤ_[l])
  have h : ‖Polynomial.aeval (0 : ℤ_[l]) P‖ < ‖Polynomial.aeval (0 : ℤ_[l]) (Polynomial.derivative P)‖ ^ 2 := by
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    simp [P]
    exact inv_lt_one_of_one_lt₀ hl
  obtain ⟨z, hz, -⟩ := hensels_lemma h
  have hz' : z ^ 2 - z + l = 0 := by simpa [P] using hz
  have hz2 : (z : ℚ_[l]) ^ 2 - z + l = 0 := by exact_mod_cast congrArg (fun t : ℤ_[l] => (t : ℚ_[l])) hz'
  exact ⟨2 * z - 1, by linear_combination 4 * hz2⟩

theorem UpperTheory.exists_totally_imaginary_padic_sqrt :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (j : Ω →+* Om l) (K : FinExt l), ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (_ : Algebra E Ω) (_ : IsAlgClosure E Ω), IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)) = K.1 ∧ ∃ δ : E, δ ≠ 0 ∧ (∀ φ : E →+* ℂ, starRingEnd ℂ (φ δ) = -φ δ) ∧ j (algebraMap E Ω δ) ∈ Set.range (algebraMap ℚ_[l] (Om l)) := by
  intro F Ω _ _ _ _ _ l _ j K
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero (Om l) := charZero_of_injective_algebraMap (algebraMap ℚ_[l] (Om l)).injective
  have halg : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  obtain ⟨β, g, hg, hβ, hreal, hK⟩ := UpperTheory.exists_totally_real_primitive_element_padic_finite_ext l K
  obtain ⟨b, hb, hbg⟩ := exists_root_lift j g hg.ne_zero β hβ
  obtain ⟨d, hd⟩ := exists_sqrt_padic l
  obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq (1 - 4 * l : Ω) (n := 2) two_pos
  obtain ⟨δ, hδ, hjδ⟩ : ∃ δ : Ω, δ ^ 2 = 1 - 4 * l ∧ j δ = algebraMap ℚ_[l] (Om l) d := by
    have h1 : j e ^ 2 = (algebraMap ℚ_[l] (Om l) d) ^ 2 := by
      rw [← map_pow, ← map_pow, he, hd]; simp [map_ofNat]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact ⟨e, he, h⟩
    · exact ⟨-e, by rw [neg_sq, he], by rw [map_neg, h, neg_neg]⟩
  let E : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ {b, δ}
  have hfin : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (halg.isAlgebraic x).isIntegral)
  have hNF : NumberField E := ⟨⟩
  let b' : E := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let δ' : E := ⟨δ, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hδ' : δ' ^ 2 = 1 - 4 * l := (algebraMap E Ω).injective (by
    rw [map_pow, map_sub, map_mul, map_one, map_ofNat, map_natCast]; exact hδ)
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hre : ∀ φ : E →+* ℂ, (φ δ').re = 0 ∧ (φ δ').im ≠ 0 := fun φ => by
    have h : φ δ' ^ 2 = 1 - 4 * l := by rw [← map_pow, hδ']; simp [map_ofNat]
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [pow_two] at h1 h2
    have h3 : (φ δ').im ≠ 0 := by
      intro h0
      rw [h0] at h1
      nlinarith [mul_self_nonneg (φ δ').re]
    refine ⟨?_, h3⟩
    have : (φ δ').re * (φ δ').im = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right h3
  have hconj : ∀ φ : E →+* ℂ, starRingEnd ℂ (φ δ') = -φ δ' := fun φ => by
    apply Complex.ext <;> simp [(hre φ).1]
  have hbb : ∀ φ : E →+* ℂ, (φ b').im = 0 := fun φ => by
    apply hreal
    have h0 : Polynomial.aeval b' g = 0 := by
      apply (algebraMap E Ω).injective
      rw [← Polynomial.aeval_algebraMap_apply, map_zero]
      exact hbg
    have := Polynomial.aeval_algHom_apply φ.toRatAlgHom b' g
    rw [h0, map_zero] at this
    exact this
  have htc : IsTotallyComplex E := ⟨fun w => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    intro h
    have h1 : starRingEnd ℂ (w.embedding δ') = w.embedding δ' := congrArg (fun f : E →+* ℂ => f δ') h
    exact (hre w.embedding).2 (Complex.conj_eq_iff_im.mp h1)⟩
  have hCM : IsCMField E := by
    refine isCM_of_conj _ ?_
    rintro ⟨x, hx⟩
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨b', fun φ => (Complex.conj_eq_iff_im.mpr (hbb φ)).symm⟩
      · exact ⟨-δ', fun φ => by rw [map_neg]; exact (hconj φ).symm⟩
    | algebraMap a =>
      refine ⟨(a : E), fun φ => ?_⟩
      change φ (a : E) = starRingEnd ℂ (φ (a : E))
      simp
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a + b, fun φ => ?_⟩
      rw [map_add, ha, hb, ← map_add, ← map_add]
      rfl
    | inv x hx ihx =>
      obtain ⟨a, ha⟩ := ihx
      refine ⟨a⁻¹, fun φ => ?_⟩
      rw [map_inv₀, ha, ← map_inv₀, ← map_inv₀]
      rfl
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a * b, fun φ => ?_⟩
      rw [map_mul, ha, hb, ← map_mul, ← map_mul]
      rfl
  have hAC : IsAlgClosure E Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  refine ⟨E, inferInstance, hNF, hCM, inferInstance, hAC, ?_, δ', ?_, hconj, ⟨d, hjδ.symm⟩⟩
  · apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      change j x ∈ K.1
      induction hx using IntermediateField.adjoin_induction with
      | mem x hx =>
        rcases hx with rfl | rfl
        · rw [hb, ← hK]; exact IntermediateField.mem_adjoin_simple_self _ _
        · rw [hjδ]; exact IntermediateField.algebraMap_mem _ _
      | algebraMap a => simp
      | add x y hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
      | inv x hx ihx => rw [map_inv₀]; exact inv_mem ihx
      | mul x y hx hy ihx ihy => rw [map_mul]; exact mul_mem ihx ihy
    · rw [← hK]
      apply IntermediateField.adjoin.mono
      rintro _ rfl
      exact ⟨b', hb⟩
  · intro h
    have φ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    exact (hre φ).2 (by rw [h]; simp)
