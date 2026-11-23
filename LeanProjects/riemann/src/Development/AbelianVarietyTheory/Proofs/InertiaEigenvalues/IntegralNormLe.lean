import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NonPowerRoot

theorem norm_pow_finrank {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] K] (x : K) :
    ‖(x : PadicAlgCl l)‖ ^ Module.finrank ℚ_[l] K = ‖Algebra.norm ℚ_[l] x‖ := by
  have h := Algebra.norm_eq_prod_embeddings ℚ_[l] (PadicAlgCl l) x
  have h2 : ∀ σ : K →ₐ[ℚ_[l]] PadicAlgCl l, ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
    intro σ
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
      minpoly.algHom_eq σ σ.injective]
    congr 1
    exact (minpoly.algHom_eq K.val K.val.injective x).symm
  rw [← PadicAlgCl.norm_extends, h, norm_prod]
  simp only [h2, Finset.prod_const, Finset.card_univ]
  rw [AlgHom.card]

theorem exists_not_pow {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] K] (u : PadicAlgCl l) (hu : u ∈ K) (h1 : 1 < ‖u‖) :
    ∃ m : ℕ, 0 < m ∧ ∀ y ∈ K, ‖y‖ ^ (m + 1) ≠ ‖u‖ := by
  have hd : 0 < Module.finrank ℚ_[l] K := Module.finrank_pos
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have key : ∀ y ∈ K, 0 < ‖y‖ → ∃ k : ℤ, ‖y‖ ^ Module.finrank ℚ_[l] K = (l : ℝ) ^ k := by
    intro y hy hy0
    have h := norm_pow_finrank K ⟨y, hy⟩
    have h0 : Algebra.norm ℚ_[l] (⟨y, hy⟩ : K) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      exact (pow_pos hy0 _).ne' h
    exact ⟨_, h.trans (Padic.norm_eq_zpow_neg_valuation h0)⟩
  obtain ⟨k, hk⟩ := key u hu (by linarith)
  have hk0 : 0 < k := by
    have : (1 : ℝ) < (l : ℝ) ^ k := by
      rw [← hk]; exact one_lt_pow₀ h1 hd.ne'
    exact (one_lt_zpow_iff_right₀ hl).mp this
  refine ⟨k.toNat, by omega, fun y hy hyu => ?_⟩
  have hy0 : 0 < ‖y‖ := by
    rcases (norm_nonneg y).eq_or_lt with h | h
    · rw [← h, zero_pow (Nat.succ_ne_zero _)] at hyu; linarith
    · exact h
  obtain ⟨a, ha⟩ := key y hy hy0
  have : (l : ℝ) ^ (a * ((k.toNat + 1 : ℕ) : ℤ)) = (l : ℝ) ^ k := by
    rw [zpow_mul, ← ha, ← hk, ← hyu, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm]
  have h3 : a * ((k.toNat + 1 : ℕ) : ℤ) = k := zpow_right_injective₀ (by linarith) hl.ne' this
  have h4 : ((k.toNat + 1 : ℕ) : ℤ) = k + 1 := by omega
  rw [h4] at h3
  rcases le_or_gt a 0 with h | h
  · nlinarith
  · nlinarith

theorem exists_root {Ω : Type} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) (u : Ω) {m : ℕ} (hm : 0 < m) :
    ∃ y : Ω, y ^ (m + 1) + y ^ m + u = 0 ∧ 1 ≤ A.valuation y := by
  by_contra hne
  push_neg at hne
  set Q : Polynomial Ω := X ^ (m + 1) + X ^ m + C u with hQ
  have hdeg : Q.natDegree = m + 1 := by
    rw [hQ]; compute_degree!
    all_goals omega
  have hmon : Q.Monic := by
    rw [hQ]; monicity!
    all_goals omega
  have hnext : Q.nextCoeff = 1 := by
    rw [nextCoeff_of_natDegree_pos (by omega), hdeg, hQ]
    simp [coeff_X_pow, coeff_C, hm.ne']
  have hs := (IsAlgClosed.splits Q).nextCoeff_eq_neg_sum_roots_of_monic hmon
  have hlt : A.valuation Q.roots.sum < 1 := by
    refine Multiset.sum_induction (fun z => A.valuation z < 1) _ ?_ ?_ ?_
    · intro a b ha hb
      exact A.valuation.map_add_lt ha hb
    · simp
    · intro a ha
      have := (mem_roots hmon.ne_zero).mp ha
      apply hne
      simpa [hQ] using this
  have : Q.roots.sum = -1 := by rw [← hnext, hs, neg_neg]
  rw [this] at hlt
  simp at hlt

theorem root_unique {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {u : Ω} (hu : A.valuation u < 1) (n : ℕ)
    {a b : Ω} (ha : a ∈ A) (hb : b ∈ A) (h1 : u * a ^ n + a + 1 = 0) (h2 : u * b ^ n + b + 1 = 0) : a = b := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (⟨a, ha⟩ : A) ⟨b, hb⟩ n
  have hc' : a ^ n - b ^ n = (a - b) * (c : Ω) := by
    simpa using congrArg (fun z : A => (z : Ω)) hc
  by_contra hab
  have h3 : (a - b) * (u * c + 1) = 0 := by linear_combination h1 - h2 - u * hc'
  have h4 : u * c = -1 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h) hab
    · linear_combination h
  have h5 : A.valuation (u * c) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hu (A.valuation_le_one c)
  rw [h4] at h5
  simp at h5

theorem norm_le_one {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : Formalism.BasicNotions.LocBridge l E Ω (ReciprocityTheory.Gal.Dec A) O) (u : E)
    (hu : A.valuation (algebraMap E Ω u) < 1) : ‖Bw.j (algebraMap E Ω u)‖ ≤ 1 := by
  by_contra h1
  push_neg at h1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI := Bw.Kw.2
  obtain ⟨m, hm, hK⟩ := exists_not_pow Bw.Kw.1 _ (Bw.j_E u) h1
  obtain ⟨y, hy, hy1⟩ := exists_root A (algebraMap E Ω u) hm
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy1
  have hyA : y⁻¹ ∈ A := by
    rw [← A.valuation_le_one_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hy1
  have hroot : algebraMap E Ω u * y⁻¹ ^ (m + 1) + y⁻¹ + 1 = 0 := by
    have : algebraMap E Ω u = -(y ^ (m + 1) + y ^ m) := by linear_combination hy
    rw [this, inv_pow]
    field_simp
    ring
  have hfix : ∀ g : ReciprocityTheory.Gal.Dec (F := E) A, (g : Ω ≃ₐ[E] Ω) y = y := by
    intro g
    have h2 : (g : Ω ≃ₐ[E] Ω) y⁻¹ ∈ A := (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec g.2 _).mpr hyA
    have h3 := congrArg (g : Ω ≃ₐ[E] Ω) hroot
    simp only [map_add, map_mul, map_pow, map_one, map_zero, AlgEquiv.commutes] at h3
    have h4 := root_unique A hu (m + 1) h2 hyA h3 hroot
    rw [map_inv₀] at h4
    exact inv_injective h4
  have hmem : Bw.j y ∈ Bw.Kw.1 := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup Bw.Kw.1, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨g, hg⟩ := Bw.e.surjective ⟨σ, hσ⟩
    have := Bw.e_comm g y
    rw [hg, hfix g] at this
    exact this
  apply hK _ hmem
  have hz := congrArg Bw.j hy
  simp only [map_add, map_pow, map_zero] at hz
  set z := Bw.j y
  set w := Bw.j (algebraMap E Ω u)
  have hw : ‖w‖ = ‖z‖ ^ m * ‖z + 1‖ := by
    have : w = -(z ^ m * (z + 1)) := by linear_combination hz
    rw [this, norm_neg, norm_mul, norm_pow]
  have hz1 : 1 < ‖z‖ := by
    by_contra hle
    push_neg at hle
    have h5 : ‖z + 1‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max z 1).trans (max_le hle (by simp))
    have h6 : ‖z‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) hle
    have := mul_le_one₀ h6 (norm_nonneg _) h5
    linarith
  have h7 : ‖z + 1‖ = ‖z‖ := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hz1.ne')]
    simpa using hz1.le
  rw [hw, h7, pow_succ]

theorem integral_norm_le {l : ℕ} [Fact l.Prime] {y : PadicAlgCl l} (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  let B : ValuationSubring (PadicAlgCl l) := (Valued.v (R := PadicAlgCl l)).valuationSubring
  have h1 : IsIntegral B y := hy.tower_top
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h1
  have h2 : Valued.v y ≤ 1 := by
    rw [← hb]; exact b.2
  rw [← PadicAlgCl.valuation_coe]
  exact_mod_cast h2

theorem norm_lt_one_iff : ∀ {l : ℕ} [Fact (Nat.Prime l)] {E Ω : Type} [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω},
    Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : Formalism.BasicNotions.LocBridge l E Ω (ReciprocityTheory.Gal.Dec A) O) (x : 𝓞 E),
      ‖(Formalism.BasicNotions.LocBridge.j Bw : Ω → Formalism.BasicNotions.Loc.Om l) ((algebraMap E Ω : E → Ω) (↑x : E))‖ < (1 : ℝ) ↔
        x ∈ v.asIdeal := by
  intro l _ E Ω _ _ _ _ _ v A hA O _ _ _ Bw
  let φ : 𝓞 E →+* PadicAlgCl l := (Bw.j.comp (algebraMap E Ω)).comp (algebraMap (𝓞 E) E)
  have hφ : ∀ x : 𝓞 E, φ x = Bw.j (algebraMap E Ω (x : E)) := fun _ => rfl
  have hle : ∀ x : 𝓞 E, ‖φ x‖ ≤ 1 := fun x =>
    integral_norm_le ((RingOfIntegers.isIntegral x).map φ.toIntAlgHom)
  let P : Ideal (𝓞 E) :=
    { carrier := {x | ‖φ x‖ < 1}
      add_mem' := fun {a b} ha hb => by
        show ‖φ (a + b)‖ < 1
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        show ‖φ (c * a)‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) ha }
  have hP : ∀ x, x ∈ P ↔ ‖φ x‖ < 1 := fun _ => Iff.rfl
  have hPp : P.IsPrime := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · rw [Ideal.ne_top_iff_one, hP]; simp
    · rw [hP, map_mul, norm_mul] at hab
      by_contra hn
      rw [not_or, hP, hP, not_lt, not_lt] at hn
      nlinarith [hn.1, hn.2]
  have hP0 : P ≠ ⊥ := by
    intro h
    have hl : (l : 𝓞 E) ∈ P := by
      rw [hP, map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
      exact Padic.norm_p_lt_one
    rw [h, Ideal.mem_bot] at hl
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hl)
  have hPv : P ≤ v.asIdeal := by
    intro s hs
    by_contra hsv
    obtain ⟨a, t, ht, hat⟩ := v.isMaximal.exists_inv hsv
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hsv v.asIdeal.zero_mem
    have hs1 : 1 ≤ A.valuation (algebraMap E Ω (s : E)) := not_lt.mp (fun h => hsv ((hA s).mp h))
    have ht1 := (hA t).mpr ht
    have hu : A.valuation (algebraMap E Ω ((t : E) / (s : E))) < 1 := by
      rw [map_div₀, map_div₀, div_lt_one₀ (lt_of_lt_of_le zero_lt_one hs1)]
      exact ht1.trans_le hs1
    have h1 := norm_le_one Bw _ hu
    have hφs : 0 < ‖φ s‖ := by
      rw [norm_pos_iff, hφ]
      simpa using hs0
    rw [map_div₀, map_div₀, norm_div, ← hφ, ← hφ, div_le_one hφs] at h1
    have htP : t ∈ P := (hP t).mpr (h1.trans_lt hs)
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, ← hat]
    exact P.add_mem (P.mul_mem_left a hs) htP
  have heq : P = v.asIdeal := (hPp.isMaximal hP0).eq_of_le v.isPrime.ne_top hPv
  intro x
  rw [← heq, hP, hφ]

end GlobalTheory.NonPowerRoot
