import Mathlib
import Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.DirichletDensity.HostDensityArith
import Formalism.CMTypeGalois.HalfTypesFromGeneral

open NumberField IntermediateField NumberField.InfinitePlace

noncomputable section

namespace Formalism.FrobeniusOrbits.DiscrB

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {L : Type} [Field L] [NumberField L]

lemma isCoprime_odd_two_pow {m : ℤ} (hm : Odd m) (k : ℕ) : IsCoprime m (2 ^ k) := by
  obtain ⟨j, rfl⟩ := hm
  exact IsCoprime.pow_right ⟨1, -j, by ring⟩

lemma adjoin_eq_top_of_map {K : Type} [Field K] [Algebra ℚ K] (ι : K →ₐ[ℚ] L) (S : Set K)
    (T : IntermediateField ℚ L) (hS : adjoin ℚ (ι '' S) = T) (hx : ∀ x : K, ι x ∈ T) :
    adjoin ℚ S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h2 : ι x ∈ (adjoin ℚ S).map ι := by
    rw [IntermediateField.adjoin_map, hS]
    exact hx x
  obtain ⟨y, hy, hyx⟩ := h2
  rwa [← (ι : K →+* L).injective hyx]

lemma exp_E (e : ℕ) : (2 ^ e * (e + 1) - 1) * 4 = 2 ^ (e + 2) * (e + 1) - 4 := by
  rw [Nat.sub_mul, one_mul, show 2 ^ (e + 2) * (e + 1) = 2 ^ e * (e + 1) * 4 by ring]

lemma exp_F (e : ℕ) : (2 ^ e * (e + 1) - 1) * 2 = 2 ^ (e + 1) * (e + 1) - 2 := by
  rw [Nat.sub_mul, one_mul, show 2 ^ (e + 1) * (e + 1) = 2 ^ e * (e + 1) * 2 by ring]

lemma odd_of_mod {q : ℕ} (h : q % 2 = 1) : Odd (q : ℤ) :=
  ⟨((q / 2 : ℕ) : ℤ), by have := Nat.div_add_mod q 2; omega⟩

variable {e q d : ℕ} {ζ a b : L}

lemma bE_sq (h : IsLayer (e + 2) q d ζ a b) : bE ζ a b ^ 2 = -(d : hostE ζ a b) := by
  apply Subtype.ext
  simpa [bE] using h.2.2.1

theorem discr_hostE (h1 : DiscrMaximalRealCyclotomic) (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b) :
    discr (hostE ζ a b) = 2 ^ (2 ^ (e + 2) * (e + 1) - 4) * ((q * d : ℕ) : ℤ) ^ (2 ^ (e + 1)) := by
  classical
  have hqd := hH.toHypOdd
  obtain ⟨hqp, hdp, hq8, hd16, -⟩ := hH
  have hne : q ≠ d := hqd.2.2.1
  let α₀ : Fin 2 → hostE ζ a b := ![aE ζ a b, bE ζ a b]
  let K₁ : IntermediateField ℚ (hostE ζ a b) := adjoin ℚ (Set.range α₀)
  let K₂ : IntermediateField ℚ (hostE ζ a b) := adjoin ℚ {thE ζ a b}
  let β : Fin 2 → K₁ := fun i => ⟨α₀ i, subset_adjoin _ _ ⟨i, rfl⟩⟩
  let qq : Fin 2 → ℕ := ![q, d]
  have hβ : Formalism.Q3.IsMQ (fun i => -(qq i : ℤ)) β := by
    refine ⟨fun i => Subtype.ext ?_, ?_⟩
    · fin_cases i
      · simpa [β, α₀, qq] using ConjReal.aE_sq h
      · simpa [β, α₀, qq] using bE_sq h
    · apply Formalism.HF.P.adjoin_top_of_lift
      rw [← Set.range_comp]
      rfl
  have hqq : ∀ i, (qq i).Prime ∧ qq i % 4 = 3 := by
    intro i; fin_cases i
    · exact ⟨hqp, by simp [qq]; omega⟩
    · exact ⟨hdp, by simp [qq]; omega⟩
  have hinj : Function.Injective qq := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [qq]
  have hd₁ : discr K₁ = (q : ℤ) ^ 2 * (d : ℤ) ^ 2 := by
    rw [Formalism.HF.Final.mqDiscr 2 qq (by norm_num) hqq hinj K₁ β hβ]
    simp [Fin.prod_univ_two, qq]
  have hGal₁ : IsGalois ℚ K₁ := (Formalism.Q3.mqGalois 2 K₁ _ β hβ
    (fun i => neg_ne_zero.2 (Nat.cast_ne_zero.2 (hqq i).1.ne_zero))).1
  let ι : hostE ζ a b →ₐ[ℚ] L := ((hostE ζ a b).val : hostE ζ a b →+* L).toRatAlgHom
  have hmap : K₂.map ι = F1 ζ := by
    rw [adjoin_map, Set.image_singleton]
    rfl
  let f₂ := (K₂.equivMap ι).trans (equivOfEq hmap)
  have hd₂ : discr K₂ = 2 ^ (2 ^ e * (e + 1) - 1) := by
    rw [discr_eq_discr_of_algEquiv _ f₂.toRingEquiv.toRatAlgEquiv, h1 e L ζ h.1]
  have hf₂ : Module.finrank ℚ K₂ = 2 ^ e := by
    rw [f₂.toLinearEquiv.finrank_eq]
    exact RealCyclotomicSubfield.finrank_real_subfield h.1
  have hcop : IsCoprime (discr K₁) (discr K₂) := by
    rw [hd₁, hd₂]
    apply isCoprime_odd_two_pow
    exact ((odd_of_mod (by omega)).pow).mul ((odd_of_mod (by omega)).pow)
  have hld := linearDisjoint_of_isGalois_isCoprime_discr (hostE ζ a b) K₁ K₂ hcop
  have hsup : K₁ ⊔ K₂ = ⊤ := by
    rw [← adjoin_union]
    refine adjoin_eq_top_of_map ι _ ℚ⟮ζ + ζ⁻¹, a, b⟯ ?_
      (fun x => by rw [← Galois.hostE_eq_adjoin]; exact x.2)
    congr 1
    ext x
    simp [α₀, aE, bE, thE, ι]
    tauto
  have hf₁ : Module.finrank ℚ K₁ = 4 := by
    have := hld.finrank_sup
    rw [hsup, finrank_top', finrank_cmField hqd h, hf₂] at this
    have h4 : 2 ^ (e + 2) = 4 * 2 ^ e := by ring
    rw [h4] at this
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) this).symm
  have hnat := natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow (hostE ζ a b) K₁ K₂ hld hsup
    (isCoprime_differentIdeal_of_isCoprime_discr (hostE ζ a b) hcop)
  have hr : nrRealPlaces (hostE ζ a b) = 0 :=
    Formalism.HF.P.nrRealPlaces_zero (aE ζ a b) (-(q : ℤ)) (by have := hqp.pos; omega)
      (by rw [ConjReal.aE_sq h]; push_cast; rfl)
  have hc : nrComplexPlaces (hostE ζ a b) = 2 ^ (e + 1) := by
    have := card_add_two_mul_card_eq_rank (K := hostE ζ a b)
    rw [hr, finrank_cmField hqd h, pow_succ] at this
    linarith
  have hs : (discr (hostE ζ a b)).sign = 1 := by
    rw [sign_discr, hc]
    exact Even.neg_one_pow ⟨2 ^ e, by ring⟩
  rw [← Int.sign_mul_natAbs (discr (hostE ζ a b)), hs, hnat, hd₁, hd₂, hf₁, hf₂, one_mul]
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  push_cast
  rw [← pow_mul, exp_E, show 2 ^ (e + 1) = 2 * 2 ^ e by ring, pow_mul]
  ring

theorem discr_hostF (h1 : DiscrMaximalRealCyclotomic) (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b) :
    discr (hostF ζ a b) = 2 ^ (2 ^ (e + 1) * (e + 1) - 2) * ((q * d : ℕ) : ℤ) ^ (2 ^ e) := by
  classical
  have hqd := hH.toHypOdd
  obtain ⟨hqp, hdp, hq8, hd16, -⟩ := hH
  have hne : q ≠ d := hqd.2.2.1
  let ι : hostF ζ a b →ₐ[ℚ] L :=
    (((hostE ζ a b).val : hostE ζ a b →+* L).comp (hostF ζ a b).subtype).toRatAlgHom
  have hab : aE ζ a b * bE ζ a b ∈ hostF ζ a b :=
    (mem_hostF_iff_adjoin hqd h _).2 (subset_adjoin ℚ _ (by simp [aE, bE]))
  have hth : thE ζ a b ∈ hostF ζ a b :=
    (mem_hostF_iff_adjoin hqd h _).2 (subset_adjoin ℚ _ (by simp [thE]))
  let abF : hostF ζ a b := ⟨_, hab⟩
  let thF : hostF ζ a b := ⟨_, hth⟩
  let M₁ : IntermediateField ℚ (hostF ζ a b) := adjoin ℚ {abF}
  let M₂ : IntermediateField ℚ (hostF ζ a b) := adjoin ℚ {thF}
  let x₁ : M₁ := ⟨abF, mem_adjoin_simple_self _ _⟩
  have hx₁ : x₁ ^ 2 = (((q : ℤ) * d : ℤ) : M₁) := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    push_cast
    show (a * b) ^ 2 = _
    rw [mul_pow, h.2.1, h.2.2.1]
    ring
  have htop₁ : adjoin ℚ {x₁} = ⊤ := by
    apply Formalism.HF.P.adjoin_top_of_lift
    rw [Set.image_singleton]
  have hsf : Squarefree ((q : ℤ) * d) := by
    rw [show ((q : ℤ) * d) = ((q * d : ℕ) : ℤ) by push_cast; rfl, Int.squarefree_natCast,
      Nat.squarefree_mul_iff]
    exact ⟨(Nat.coprime_primes hqp hdp).2 hne, hqp.squarefree, hdp.squarefree⟩
  have hmod : ((q : ℤ) * d) % 4 = 1 := by
    have hq4 : (q : ℤ) % 4 = 3 := by omega
    have hd4 : (d : ℤ) % 4 = 3 := by omega
    rw [Int.mul_emod, hq4, hd4]
    norm_num
  have hd₁ : discr M₁ = (q : ℤ) * d := Formalism.HF.Final.quadDiscr M₁ _ x₁ hx₁ htop₁ hsf hmod
  have hGal₁ : IsGalois ℚ M₁ := (Formalism.Q3.mqGalois 1 M₁ (fun _ => (q : ℤ) * d) (fun _ => x₁)
    ⟨fun _ => hx₁, by rw [Set.range_const]; exact htop₁⟩
    (fun _ => mul_ne_zero (Nat.cast_ne_zero.2 hqp.ne_zero) (Nat.cast_ne_zero.2 hdp.ne_zero))).1
  have hmap : M₂.map ι = F1 ζ := by
    rw [adjoin_map, Set.image_singleton]
    rfl
  let f₂ := (M₂.equivMap ι).trans (equivOfEq hmap)
  have hd₂ : discr M₂ = 2 ^ (2 ^ e * (e + 1) - 1) := by
    rw [discr_eq_discr_of_algEquiv _ f₂.toRingEquiv.toRatAlgEquiv, h1 e L ζ h.1]
  have hf₂ : Module.finrank ℚ M₂ = 2 ^ e := by
    rw [f₂.toLinearEquiv.finrank_eq]
    exact RealCyclotomicSubfield.finrank_real_subfield h.1
  have hcop : IsCoprime (discr M₁) (discr M₂) := by
    rw [hd₁, hd₂]
    apply isCoprime_odd_two_pow
    exact (odd_of_mod (by omega)).mul (odd_of_mod (by omega))
  have hld := linearDisjoint_of_isGalois_isCoprime_discr (hostF ζ a b) M₁ M₂ hcop
  have hsup : M₁ ⊔ M₂ = ⊤ := by
    rw [← adjoin_union]
    refine adjoin_eq_top_of_map ι _ ℚ⟮a * b, ζ + ζ⁻¹⟯ ?_
      (fun x => (mem_hostF_iff_adjoin hqd h (x : hostE ζ a b)).1 x.2)
    congr 1
    ext x
    simp [ι, abF, thF, aE, bE, thE]
    tauto
  have hf₁ : Module.finrank ℚ M₁ = 2 := by
    have := hld.finrank_sup
    rw [hsup, finrank_top', finrank_hostF hqd h, hf₂] at this
    have h2 : 2 ^ (e + 1) = 2 * 2 ^ e := by ring
    rw [h2] at this
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) this).symm
  have hnat := natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow (hostF ζ a b) M₁ M₂ hld hsup
    (isCoprime_differentIdeal_of_isCoprime_discr (hostF ζ a b) hcop)
  have hs : (discr (hostF ζ a b)).sign = 1 := by
    rw [sign_discr, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero]
  rw [← Int.sign_mul_natAbs (discr (hostF ζ a b)), hs, hnat, hd₁, hd₂, hf₁, hf₂, one_mul]
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  push_cast
  rw [← pow_mul, exp_F]
  ring

theorem rdE (e q d : ℕ) (hq : 0 < q) (hd : 0 < d) :
    |(((2 : ℤ) ^ (2 ^ (e + 2) * (e + 1) - 4) * ((q * d : ℕ) : ℤ) ^ (2 ^ (e + 1)) : ℤ) : ℝ)| ^
        ((1 : ℝ) / (2 ^ (e + 2) : ℝ)) =
      (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d) := by
  have hX : (0 : ℝ) ≤ (q : ℝ) * d := by positivity
  have hB : 4 ≤ 2 ^ (e + 2) * (e + 1) := by
    have : 4 ≤ 2 ^ (e + 2) := by
      rw [pow_add]; norm_num; exact Nat.one_le_two_pow
    nlinarith
  push_cast
  rw [abs_of_nonneg (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast (2 : ℝ) (2 ^ (e + 2) * (e + 1) - 4), ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast ((q : ℝ) * d) (2 ^ (e + 1)), ← Real.rpow_mul hX, Real.sqrt_eq_rpow]
  congr 2
  · rw [Nat.cast_sub hB, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    push_cast
    field_simp
    ring
  · push_cast
    field_simp
    ring

theorem rdF (e q d : ℕ) (hq : 0 < q) (hd : 0 < d) :
    |(((2 : ℤ) ^ (2 ^ (e + 1) * (e + 1) - 2) * ((q * d : ℕ) : ℤ) ^ (2 ^ e) : ℤ) : ℝ)| ^
        ((1 : ℝ) / (2 ^ (e + 1) : ℝ)) =
      (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d) := by
  have hX : (0 : ℝ) ≤ (q : ℝ) * d := by positivity
  have hB : 2 ≤ 2 ^ (e + 1) * (e + 1) := by
    have : 2 ≤ 2 ^ (e + 1) := by
      rw [pow_succ]; norm_num; exact Nat.one_le_two_pow
    nlinarith
  push_cast
  rw [abs_of_nonneg (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast (2 : ℝ) (2 ^ (e + 1) * (e + 1) - 2), ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast ((q : ℝ) * d) (2 ^ e), ← Real.rpow_mul hX, Real.sqrt_eq_rpow]
  congr 2
  · rw [Nat.cast_sub hB, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    push_cast
    field_simp
    ring
  · push_cast
    field_simp
    ring

theorem sqF (e q d : ℕ) :
    ((2 : ℤ) ^ (2 ^ (e + 1) * (e + 1) - 2) * ((q * d : ℕ) : ℤ) ^ (2 ^ e)) ^ 2 =
      (2 : ℤ) ^ (2 ^ (e + 2) * (e + 1) - 4) * ((q * d : ℕ) : ℤ) ^ (2 ^ (e + 1)) := by
  have hB : 2 ^ (e + 2) * (e + 1) - 4 = (2 ^ (e + 1) * (e + 1) - 2) * 2 := by
    rw [Nat.sub_mul, show 2 ^ (e + 2) * (e + 1) = 2 ^ (e + 1) * (e + 1) * 2 by ring]
  rw [hB, mul_pow, ← pow_mul, ← pow_mul, ← pow_succ]

end Formalism.FrobeniusOrbits.DiscrB

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

theorem hostDiscr_of (h1 : DiscrMaximalRealCyclotomic) : HostDiscr := by
  intro e q d hH L _ _ ζ a b h
  have hq : 0 < q := hH.1.pos
  have hd : 0 < d := hH.2.1.pos
  have hE := DiscrB.discr_hostE h1 hH h
  have hF := DiscrB.discr_hostF h1 hH h
  refine ⟨hE, hF, by rw [hE, hF]; exact (DiscrB.sqF e q d).symm, ?_, ?_⟩
  · rw [hE]; exact DiscrB.rdE e q d hq hd
  · rw [hF]; exact DiscrB.rdF e q d hq hd

end Formalism.FrobeniusOrbits
