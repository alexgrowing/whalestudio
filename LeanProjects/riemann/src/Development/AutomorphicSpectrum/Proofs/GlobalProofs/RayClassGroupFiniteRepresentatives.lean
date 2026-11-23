import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Formalism.LocalToGlobal.GlobalTheory.GL2.TotallyComplexOfNoReal

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

variable {F : Type} [Field F] [NumberField F]

theorem finite_realEmbeddings : Finite (F →+* ℝ) := by
  infer_instance

theorem rayRel_of_signs (𝔣 I J R : Ideal (𝓞 F)) (a a' b b' : 𝓞 F) (ha0 : a ≠ 0) (ha0' : a' ≠ 0) (hb0 : b ≠ 0) (hb0' : b' ≠ 0)
    (hb1 : b - 1 ∈ 𝔣) (hb1' : b' - 1 ∈ 𝔣) (haq : Ideal.span {a} ⊔ 𝔣 = ⊤) (haa : a - a' ∈ 𝔣)
    (hs : ∀ σ : F →+* ℝ, 0 < σ ((a * b : 𝓞 F) : F) ↔ 0 < σ ((a' * b' : 𝓞 F) : F))
    (e1 : Ideal.span {a} * I = Ideal.span {b} * R) (e2 : Ideal.span {a'} * J = Ideal.span {b'} * R) :
    RayRel F 𝔣 I J := by
  obtain ⟨c, hc0, hc⟩ : ∃ c : 𝓞 F, c ≠ 0 ∧ c * a - 1 ∈ 𝔣 := by
    have h1 : (1 : 𝓞 F) ∈ Ideal.span {a} ⊔ 𝔣 := by rw [haq]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    by_cases h : c = 0
    · subst h
      have hz1 : (1 : 𝓞 F) ∈ 𝔣 := by rw [← hyz]; simpa using hz
      exact ⟨1, one_ne_zero, by simpa using 𝔣.mul_mem_left (1 * a - 1) hz1⟩
    · refine ⟨c, h, ?_⟩
      have : c * a - 1 = -z := by rw [← hyz]; ring
      rw [this]; exact 𝔣.neg_mem hz
  have qb : Ideal.Quotient.mk 𝔣 b = 1 := by
    rw [← map_one (Ideal.Quotient.mk 𝔣)]; exact Ideal.Quotient.eq.2 hb1
  have qb' : Ideal.Quotient.mk 𝔣 b' = 1 := by
    rw [← map_one (Ideal.Quotient.mk 𝔣)]; exact Ideal.Quotient.eq.2 hb1'
  have qa : Ideal.Quotient.mk 𝔣 a' = Ideal.Quotient.mk 𝔣 a := (Ideal.Quotient.eq.2 haa).symm
  have qc : Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔣)]; exact Ideal.Quotient.eq.2 hc
  have same : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → (0 < x ↔ 0 < y) → 0 < x * y := by
    intro x y hx hy hxy
    rcases lt_or_gt_of_ne hx with h | h
    · have hy' : y < 0 := lt_of_le_of_ne (not_lt.1 (fun h' => absurd (hxy.2 h') (not_lt.2 h.le))) hy
      exact mul_pos_of_neg_of_neg h hy'
    · exact mul_pos h (hxy.1 h)
  have coe0 : ∀ x : 𝓞 F, x ≠ 0 → ∀ σ : F →+* ℝ, σ (x : F) ≠ 0 := by
    intro x hx σ
    exact (map_ne_zero σ).2 (by exact_mod_cast hx)
  refine ⟨(a * b' * c) ^ 2, a' * b * a * b' * c ^ 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pow_ne_zero 2 (mul_ne_zero (mul_ne_zero ha0 hb0') hc0)
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha0' hb0) ha0) hb0') (pow_ne_zero 2 hc0)
  · apply Ideal.Quotient.eq.1
    simp only [map_pow, map_mul, map_one, qb']
    linear_combination (Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a + 1) * qc
  · apply Ideal.Quotient.eq.1
    simp only [map_pow, map_mul, map_one, qb, qb', qa]
    linear_combination (Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a + 1) * qc
  · intro σ
    constructor
    · have hx := coe0 _ (mul_ne_zero (mul_ne_zero ha0 hb0') hc0) σ
      have : σ (((a * b' * c) ^ 2 : 𝓞 F) : F) = (σ ((a * b' * c : 𝓞 F) : F)) ^ 2 := by
        push_cast; simp only [map_pow]
      rw [this]
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))
    · have h1 := coe0 _ (mul_ne_zero ha0 hb0) σ
      have h2 := coe0 _ (mul_ne_zero ha0' hb0') σ
      have h3 := coe0 _ hc0 σ
      have : σ ((a' * b * a * b' * c ^ 2 : 𝓞 F) : F) =
          σ ((a * b : 𝓞 F) : F) * σ ((a' * b' : 𝓞 F) : F) * (σ (c : F)) ^ 2 := by
        push_cast; simp only [map_mul, map_pow]; ring
      rw [this]
      exact mul_pos (same _ _ h1 h2 (hs σ)) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h3)))
  · calc Ideal.span {(a * b' * c) ^ 2} * I
        = Ideal.span {a * b' ^ 2 * c ^ 2} * (Ideal.span {a} * I) := by
          rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton]; congr 2; ring_nf
      _ = Ideal.span {a * b' ^ 2 * c ^ 2} * (Ideal.span {b} * R) := by rw [e1]
      _ = Ideal.span {a * b * b' * c ^ 2} * (Ideal.span {b'} * R) := by
          rw [← mul_assoc, ← mul_assoc, Ideal.span_singleton_mul_span_singleton,
            Ideal.span_singleton_mul_span_singleton]; congr 3; ring
      _ = Ideal.span {a * b * b' * c ^ 2} * (Ideal.span {a'} * J) := by rw [e2]
      _ = Ideal.span {a' * b * a * b' * c ^ 2} * J := by
          rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton]; congr 3; ring

theorem finRay (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) :
    ∃ S : Finset (Ideal (𝓞 F)), (∀ a ∈ S, CoprimeTo F 𝔣 a) ∧ (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) ∧
      ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a := by
  classical
  haveI : Finite (F →+* ℝ) := finite_realEmbeddings
  haveI : Finite (𝓞 F ⧸ 𝔣) :=
    (Ideal.absNorm_ne_zero_iff 𝔣).1 (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have key : ∀ A : Ideal (𝓞 F), A ≠ ⊥ → ∃ B : Ideal (𝓞 F), B ≠ ⊥ ∧ B ⊔ 𝔣 = ⊤ ∧
      ∃ r : 𝓞 F, r ≠ 0 ∧ A * B = Ideal.span {r} := by
    intro A hA
    have hA' : A ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
    have h𝔣' : 𝔣 ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
    have hM0 : M ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot]
      exact Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
    have hAg : A * (𝔣 * M) ≠ 0 := mul_ne_zero hA' (mul_ne_zero h𝔣' hM0)
    obtain ⟨r, hr⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_inf.trans inf_le_left : A * (𝔣 * M) ≤ A) hAg
    obtain ⟨B, hB⟩ : A ∣ Ideal.span {r} :=
      Ideal.dvd_iff_le.2 ((le_sup_right : Ideal.span {r} ≤ A * (𝔣 * M) ⊔ Ideal.span {r}).trans hr.le)
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq] at hr
      have h1 : 𝔣 * M = ⊤ := by
        apply mul_left_cancel₀ hA'
        rw [hr, Ideal.mul_top]
      have h2 : 𝔣 * M ≤ M := Ideal.mul_le_inf.trans inf_le_right
      rw [h1] at h2
      exact hM.ne_top (top_le_iff.1 h2)
    refine ⟨B, ?_, ?_, r, hr0, hB.symm⟩
    · rintro rfl
      rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hB
      exact hr0 hB
    · have h1 : A * (𝔣 * M ⊔ B) = A * ⊤ := by
        rw [Ideal.mul_sup, ← hB, hr, Ideal.mul_top]
      have h2 : 𝔣 * M ⊔ B = ⊤ := mul_left_cancel₀ hA' h1
      rw [eq_top_iff, ← h2]
      exact sup_le ((Ideal.mul_le_inf.trans inf_le_left).trans le_sup_right) le_sup_left
  have rep : ∀ c : ClassGroup (𝓞 F), ∃ P : Ideal (𝓞 F), ∃ hP : P ∈ nonZeroDivisors (Ideal (𝓞 F)),
      P ⊔ 𝔣 = ⊤ ∧ ClassGroup.mk0 ⟨P, hP⟩ = c := by
    intro c
    obtain ⟨⟨A, hA⟩, hAc⟩ := ClassGroup.mk0_surjective c⁻¹
    have hA0 : A ≠ ⊥ := by
      have := nonZeroDivisors.ne_zero hA
      rwa [Ne, Ideal.zero_eq_bot] at this
    obtain ⟨B, hB0, hBf, r, hr0, hAB⟩ := key A hA0
    have hBm : B ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.zero_eq_bot])
    refine ⟨B, hBm, hBf, ?_⟩
    have hABm : A * B ∈ nonZeroDivisors (Ideal (𝓞 F)) := Submonoid.mul_mem _ hA hBm
    have h1 : ClassGroup.mk0 ⟨A * B, hABm⟩ = 1 := (ClassGroup.mk0_eq_one_iff hABm).2 ⟨⟨r, hAB⟩⟩
    have h2 : ClassGroup.mk0 ⟨A * B, hABm⟩ = ClassGroup.mk0 ⟨A, hA⟩ * ClassGroup.mk0 ⟨B, hBm⟩ := by
      rw [← map_mul]; rfl
    rw [h2, hAc] at h1
    exact (inv_mul_eq_one.1 h1).symm
  choose P hPm hPf hPc using rep
  have hPcop : ∀ c, CoprimeTo F 𝔣 (P c) := by
    intro c
    have := nonZeroDivisors.ne_zero (hPm c)
    rw [Ne, Ideal.zero_eq_bot] at this
    exact (show P c ≠ ⊥ ∧ P c ⊔ 𝔣 = ⊤ from ⟨this, hPf c⟩)
  have hcov : ∀ I : Ideal (𝓞 F), CoprimeTo F 𝔣 I → ∃ (c : ClassGroup (𝓞 F)) (a b : 𝓞 F),
      a ≠ 0 ∧ b ≠ 0 ∧ b - 1 ∈ 𝔣 ∧ Ideal.span {a} ⊔ 𝔣 = ⊤ ∧
        Ideal.span {a} * I = Ideal.span {b} * P c := by
    intro I hI
    have hI' : I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤ := hI
    have hIm : I ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero (by rw [Ne, Ideal.zero_eq_bot]; exact hI'.1)
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 (hPc (ClassGroup.mk0 ⟨I, hIm⟩)).symm
    obtain ⟨a, b, ha, hb, hb1, haq, he⟩ :=
      Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.exists_rel_of_class 𝔣 I (P (ClassGroup.mk0 ⟨I, hIm⟩)) hI (hPcop _) x y hx hy hxy
    exact ⟨_, a, b, ha, hb, hb1, haq, he⟩
  choose cl a b ha hb hb1 haq he using hcov
  obtain ⟨κ, hκ⟩ : ∃ κ : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} →
      ClassGroup (𝓞 F) × (𝓞 F ⧸ 𝔣) × Set (F →+* ℝ),
      κ = fun I => (cl I.1 I.2, Ideal.Quotient.mk 𝔣 (a I.1 I.2),
        {σ : F →+* ℝ | 0 < σ ((a I.1 I.2 * b I.1 I.2 : 𝓞 F) : F)}) := ⟨_, rfl⟩
  have hrel : ∀ I J : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I}, κ I = κ J → RayRel F 𝔣 I.1 J.1 := by
    intro I J h
    rw [hκ] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hc, hq, hs⟩ := h
    refine rayRel_of_signs 𝔣 I.1 J.1 (P (cl I.1 I.2)) (a I.1 I.2) (a J.1 J.2) (b I.1 I.2) (b J.1 J.2)
      (ha _ _) (ha _ _) (hb _ _) (hb _ _) (hb1 _ _) (hb1 _ _) (haq _ _) (Ideal.Quotient.eq.1 hq)
      (fun σ => Set.ext_iff.1 hs σ) (he _ _) ?_
    rw [hc]; exact he _ _
  haveI : Nonempty {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} :=
    ⟨⟨⊤, show (⊤ : Ideal (𝓞 F)) ≠ ⊥ ∧ (⊤ : Ideal (𝓞 F)) ⊔ 𝔣 = ⊤ from ⟨top_ne_bot, top_sup_eq _⟩⟩⟩
  have hfin : (Set.range κ).Finite := Set.toFinite _
  have hne : ∀ d ∈ Set.range κ, ∃ I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I}, κ I = d := fun d hd => hd
  choose! g hg using hne
  obtain ⟨T, hTc, hTcov⟩ : ∃ T : Finset (Ideal (𝓞 F)), (∀ t ∈ T, CoprimeTo F 𝔣 t) ∧
      ∀ I, CoprimeTo F 𝔣 I → ∃ t ∈ T, RayRel F 𝔣 I t := by
    refine ⟨hfin.toFinset.image (fun d => (g d).1), ?_, ?_⟩
    · intro t ht
      obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 ht
      exact (g d).2
    · intro I hI
      have hd : κ ⟨I, hI⟩ ∈ Set.range κ := ⟨_, rfl⟩
      refine ⟨(g (κ ⟨I, hI⟩)).1, Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hd), ?_⟩
      exact hrel ⟨I, hI⟩ (g (κ ⟨I, hI⟩)) (hg _ hd).symm
  obtain ⟨f, hf⟩ : ∃ f : Ideal (𝓞 F) → Ideal (𝓞 F),
      f = fun t => Classical.epsilon (fun s => s ∈ T ∧ RayRel F 𝔣 t s) := ⟨_, rfl⟩
  have hfT : ∀ t ∈ T, f t ∈ T ∧ RayRel F 𝔣 t (f t) := by
    intro t ht
    rw [hf]
    exact Classical.epsilon_spec (p := fun s => s ∈ T ∧ RayRel F 𝔣 t s) ⟨t, ht, rayRel_refl t⟩
  have hfeq : ∀ t t', RayRel F 𝔣 t t' → f t = f t' := by
    intro t t' h
    simp only [hf]
    congr 1
    funext s
    apply propext
    constructor
    · rintro ⟨hs, h'⟩
      exact ⟨hs, rayRel_trans (rayRel_symm h) h'⟩
    · rintro ⟨hs, h'⟩
      exact ⟨hs, rayRel_trans h h'⟩
  refine ⟨T.image f, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    exact hTc _ (hfT t ht).1
  · intro s hs s' hs' h
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hs'
    apply hfeq
    exact rayRel_trans (hfT t ht).2 (rayRel_trans h (rayRel_symm (hfT t' ht').2))
  · intro I hI
    obtain ⟨t, ht, hIt⟩ := hTcov I hI
    exact ⟨f t, Finset.mem_image_of_mem _ ht, rayRel_trans hIt (hfT t ht).2⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
