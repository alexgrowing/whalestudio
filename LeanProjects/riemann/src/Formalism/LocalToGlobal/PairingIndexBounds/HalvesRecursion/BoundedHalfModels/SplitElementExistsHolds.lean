import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.Assemble

noncomputable section
open scoped nonZeroDivisors

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

def GenSplit : Prop :=
  ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (m n : Type) (I : Ideal R) (π πb : R) (n₀ : ℕ) (ι : Type) (Y₀ : Submodule R (Matrix m n K))
    (Y : ι → Submodule R (Matrix m n K)),
    π ≠ 0 → πb ≠ 0 → IsCoprime π πb →
    (∀ i, ∀ y ∈ Y₀, (π * πb) ^ n₀ • y ∈ Y i) → (∀ i, ∀ y ∈ Y i, (π * πb) ^ n₀ • y ∈ Y₀) →
    ∀ i,
      let u : K := (algebraMap R K πb / algebraMap R K π) ^ n₀
      let MA := I • sMod u Y₀
      let MB := I • sMod u⁻¹ Y₀
      (∀ y ∈ I • Y i, ∃ a ∈ I • Y i ⊓ MA, ∃ b ∈ I • Y i ⊓ MB, y = a + b) ∧
      (∀ a ∈ MA, ∀ b ∈ MB, a + b ∈ I • Y i → a ∈ I • Y i)

def RecSplitElt : Prop :=
  ∀ (D : D7) (a : 𝓞 D.host.E), a ≠ 0 → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), a ∈ Q.asIdeal → SplitP D Q) →
    ∃ π : 𝓞 D.host.E, π ≠ 0 ∧ IsCoprime π (cO D π) ∧ ∃ j : ℕ, a ∣ (π * cO D π) ^ j

theorem generic_splitting_holds : GenSplit := by
  intro R _ _ K _ _ _ m n I π πb n₀ ι Y₀ Y hπ0 hπb0 hcop h0i hi0 i
  have hP : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ0
  have hQ : algebraMap R K πb ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπb0
  obtain ⟨x, y, hxy⟩ : IsCoprime (πb ^ n₀ * πb ^ n₀) (π ^ n₀ * π ^ n₀) := by
    have h := hcop.symm.pow (m := n₀) (n := n₀)
    have h' := h.mul_left h
    exact h'.mul_right h'
  intro u MA MB
  refine ⟨?_, ?_⟩
  · intro w hw
    refine ⟨(x * (πb ^ n₀ * πb ^ n₀)) • w, Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hw, ?_⟩,
      (y * (π ^ n₀ * π ^ n₀)) • w, Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hw, ?_⟩, ?_⟩
    · exact gh_toHalf I (r := x * (π * πb) ^ n₀)
        (fun z hz => by rw [mul_smul]; exact Y₀.smul_mem x (hi0 i z hz))
        (by simp only [u, map_mul, map_pow]; exact div_pow_mul_prod_pow_left hP n₀) w hw
    · exact gh_toHalf I (r := y * (π * πb) ^ n₀)
        (fun z hz => by rw [mul_smul]; exact Y₀.smul_mem y (hi0 i z hz))
        (by simp only [u, map_mul, map_pow]; exact inv_div_pow_mul_prod_pow_right hQ n₀) w hw
    · rw [← add_smul, hxy, one_smul]
  · intro a ha b hb hab
    have hfa : (y * (π ^ n₀ * π ^ n₀)) • a ∈ I • Y i :=
      gh_fromHalf I (r := y * (π * πb) ^ n₀)
        (fun z hz => by rw [mul_smul]; exact (Y i).smul_mem y (h0i i z hz))
        (by simp only [u, map_mul, map_pow]; exact sq_pow_mul_div_pow_eq_prod_pow hP n₀) a ha
    have heb : (x * (πb ^ n₀ * πb ^ n₀)) • b ∈ I • Y i :=
      gh_fromHalf I (r := x * (π * πb) ^ n₀)
        (fun z hz => by rw [mul_smul]; exact (Y i).smul_mem x (h0i i z hz))
        (by simp only [u, map_mul, map_pow]; exact sq_pow_mul_inv_div_pow_eq_prod_pow hQ n₀) b hb
    have h1 : (x * (πb ^ n₀ * πb ^ n₀)) • (a + b) + (y * (π ^ n₀ * π ^ n₀)) • a -
        (x * (πb ^ n₀ * πb ^ n₀)) • b = (x * (πb ^ n₀ * πb ^ n₀) + y * (π ^ n₀ * π ^ n₀)) • a := by
      rw [smul_add, add_smul]; abel
    rw [hxy, one_smul] at h1
    rw [← h1]
    exact sub_mem (add_mem (Submodule.smul_mem _ _ hab) hfa) heb

theorem genPow (D : D7) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ x : 𝓞 D.host.E, x ≠ 0 ∧ x ∈ Q.asIdeal ∧ ∀ M : Ideal (𝓞 D.host.E), M.IsPrime → x ∈ M → Q.asIdeal = M := by
  classical
  have hP0 : Q.asIdeal ≠ ⊥ := Q.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 D.host.E))
  have hh : 0 < h := Fintype.card_pos
  have hm : Q.asIdeal ^ h ∈ (Ideal (𝓞 D.host.E))⁰ := pow_mem (mem_nonZeroDivisors_of_ne_zero hP0) h
  have hprin : (Q.asIdeal ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hm]
    have : ClassGroup.mk0 (⟨Q.asIdeal ^ h, hm⟩ : (Ideal (𝓞 D.host.E))⁰) =
        ClassGroup.mk0 ⟨Q.asIdeal, mem_nonZeroDivisors_of_ne_zero hP0⟩ ^ h := by
      rw [← map_pow, SubmonoidClass.mk_pow]
    rw [this, pow_card_eq_one]
  obtain ⟨π, hπ⟩ := hprin
  have hspan : Ideal.span {π} = Q.asIdeal ^ h := hπ.symm
  refine ⟨π, ?_, ?_, ?_⟩
  · intro h0
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at hspan
    exact pow_ne_zero h hP0 hspan.symm
  · have : π ∈ Q.asIdeal ^ h := by rw [← hspan]; exact Ideal.mem_span_singleton_self π
    exact Ideal.pow_le_self hh.ne' this
  · intro M hM hπM
    have : Q.asIdeal ^ h ≤ M := by rw [← hspan, Ideal.span_le]; simpa using hπM
    exact Q.isMaximal.eq_of_le hM.ne_top (hM.le_of_pow_le this)

theorem cO_cO (D : D7) (x : 𝓞 D.host.E) : cO D (cO D x) = x := Subtype.ext (conj_conj' D (x : D.host.E))

def cQ (D : D7) (Q : HeightOneSpectrum (𝓞 D.host.E)) : HeightOneSpectrum (𝓞 D.host.E) where
  asIdeal := Q.asIdeal.comap (cO D)
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    intro h
    have : cO D x ∈ Q.asIdeal.comap (cO D) := by rw [Ideal.mem_comap, cO_cO]; exact hx
    rw [h, Ideal.mem_bot] at this
    apply hx0
    rw [← cO_cO D x, this, map_zero]

theorem mem_cQ (D : D7) (Q : HeightOneSpectrum (𝓞 D.host.E)) (x : 𝓞 D.host.E) :
    x ∈ (cQ D Q).asIdeal ↔ cO D x ∈ Q.asIdeal := Ideal.mem_comap

theorem cQ_cQ (D : D7) (Q : HeightOneSpectrum (𝓞 D.host.E)) : cQ D (cQ D Q) = Q := by
  ext x; rw [mem_cQ, mem_cQ, cO_cO]

theorem cQ_ne (D : D7) (Q : HeightOneSpectrum (𝓞 D.host.E)) (h : SplitP D Q) : cQ D Q ≠ Q := by
  obtain ⟨a, b, hab, ha, hb⟩ := h
  intro he
  apply hb
  have hb' : b = cO D a := Subtype.ext (hab.trans rfl)
  rw [hb', ← mem_cQ, he]; exact ha

theorem split_element_exists_holds : RecSplitElt := by
  intro D a ha0 hsplit
  classical
  have hfin : {Q : HeightOneSpectrum (𝓞 D.host.E) | Q.asIdeal ∣ Ideal.span {a}}.Finite :=
    Ideal.finite_factors (by rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha0)
  let S0 := hfin.toFinset
  let S := S0 ∪ S0.image (cQ D)
  let r := WellOrderingRel (α := HeightOneSpectrum (𝓞 D.host.E))
  let Sp := S.filter (fun Q => r Q (cQ D Q))
  choose g hg0 hgQ hgM using genPow D
  let π := ∏ Q ∈ Sp, g Q
  have hπ0 : π ≠ 0 := Finset.prod_ne_zero_iff.2 fun Q _ => hg0 Q
  have hmemπ : ∀ M : Ideal (𝓞 D.host.E), M.IsPrime → π ∈ M → ∃ Q ∈ Sp, Q.asIdeal = M := by
    intro M hM h
    obtain ⟨Q, hQ, hgm⟩ := (hM.prod_mem_iff).1 h
    exact ⟨Q, hQ, hgM Q M hM hgm⟩
  have hmemπb : ∀ M : Ideal (𝓞 D.host.E), M.IsPrime → cO D π ∈ M → ∃ Q ∈ Sp, (cQ D Q).asIdeal = M := by
    intro M hM h
    rw [map_prod] at h
    obtain ⟨Q, hQ, hgm⟩ := (hM.prod_mem_iff).1 h
    refine ⟨Q, hQ, ?_⟩
    have hM' : (M.comap (cO D)).IsPrime := Ideal.IsPrime.comap _
    have e := hgM Q _ hM' (Ideal.mem_comap.2 hgm)
    ext x
    rw [mem_cQ, e, Ideal.mem_comap, cO_cO]
  refine ⟨π, hπ0, ?_, ?_⟩
  · rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨Q₁, hQ₁, e₁⟩ := hmemπ M hM.isPrime (hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)))
    obtain ⟨Q₂, hQ₂, e₂⟩ := hmemπb M hM.isPrime (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    have e : Q₁ = cQ D Q₂ := HeightOneSpectrum.ext (e₁.trans e₂.symm)
    have r1 : WellOrderingRel Q₁ (cQ D Q₁) := (Finset.mem_filter.1 hQ₁).2
    have r2 : WellOrderingRel Q₂ (cQ D Q₂) := (Finset.mem_filter.1 hQ₂).2
    rw [e, cQ_cQ] at r1
    exact asymm r2 r1
  · have hrad : π * cO D π ∈ (Ideal.span {a}).radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro J ⟨hJa, hJ⟩
      have haJ : a ∈ J := hJa (Ideal.mem_span_singleton_self a)
      have hJ0 : J ≠ ⊥ := by intro h; rw [h, Ideal.mem_bot] at haJ; exact ha0 haJ
      let Q : HeightOneSpectrum (𝓞 D.host.E) := ⟨J, hJ, hJ0⟩
      have hQS0 : Q ∈ S0 := by rw [Set.Finite.mem_toFinset]; exact Ideal.dvd_iff_le.2 hJa
      rcases trichotomous_of WellOrderingRel Q (cQ D Q) with h | h | h
      · have hQ : Q ∈ Sp := Finset.mem_filter.2 ⟨Finset.mem_union_left _ hQS0, h⟩
        have : π ∈ J := Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem g hQ) (hgQ Q)
        exact Ideal.mul_mem_right _ J this
      · exact absurd h.symm (cQ_ne D Q (hsplit Q haJ))
      · have hQ : cQ D Q ∈ Sp := Finset.mem_filter.2
          ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQS0), by rw [cQ_cQ]; exact h⟩
        have h1 : cO D (g (cQ D Q)) ∈ J := (mem_cQ D Q _).1 (hgQ (cQ D Q))
        have : cO D π ∈ J := by
          rw [map_prod]
          exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem (fun Q' => cO D (g Q')) hQ) h1
        exact Ideal.mul_mem_left J _ this
    obtain ⟨j, hj⟩ := hrad
    exact ⟨j, Ideal.mem_span_singleton.1 hj⟩

end Formalism.L2.PairingIndexBounds.Rec
