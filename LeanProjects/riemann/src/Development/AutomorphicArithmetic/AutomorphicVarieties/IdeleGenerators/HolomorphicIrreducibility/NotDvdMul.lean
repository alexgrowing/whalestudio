import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.MemMirabQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Sd

variable {F : Type} [Field F] [NumberField F]

private theorem div_mul (a : Ideal (𝓞 F) → ℂ) (w : Pl F) (n : Ideal (𝓞 F)) : coefDiv a w.asIdeal (w.asIdeal * n) = a n := by
  have h : ∃ 𝔫, w.asIdeal * n = w.asIdeal * 𝔫 := ⟨n, rfl⟩
  unfold coefDiv
  rw [dif_pos h, ← mul_left_cancel₀ w.ne_bot h.choose_spec]

private theorem div_not (a : Ideal (𝓞 F) → ℂ) (w : Pl F) {m : Ideal (𝓞 F)} (h : ¬ w.asIdeal ∣ m) : coefDiv a w.asIdeal m = 0 := by
  unfold coefDiv
  rw [dif_neg]
  exact h

private theorem not_dvd_mul {v w : Pl F} (hvw : v ≠ w) {m : Ideal (𝓞 F)} (h : ¬ v.asIdeal ∣ m) : ¬ v.asIdeal ∣ w.asIdeal * m := by
  intro h'
  rcases v.prime.dvd_or_dvd h' with h1 | h1
  · exact hvw (HeightOneSpectrum.ext (associated_iff_eq.1 ((v.prime.dvd_prime_iff_associated w.prime).1 h1)))
  · exact h h1

private theorem div_comm {v w : Pl F} (hvw : v ≠ w) (a : Ideal (𝓞 F) → ℂ) (m : Ideal (𝓞 F)) :
    coefDiv a v.asIdeal (w.asIdeal * m) = coefDiv (fun n => a (w.asIdeal * n)) v.asIdeal m := by
  by_cases h : v.asIdeal ∣ m
  · obtain ⟨n, rfl⟩ := h
    rw [div_mul, mul_left_comm, div_mul]
  · rw [div_not _ _ h, div_not _ _ (not_dvd_mul hvw h)]

private def Rel (w : Pl F) (e t : ℂ) (a : Ideal (𝓞 F) → ℂ) : Prop :=
  ∀ m, m ≠ ⊥ → a (w.asIdeal * m) + e * coefDiv a w.asIdeal m = t * a m

private theorem rel_div {v w : Pl F} (hvw : v ≠ w) {e t : ℂ} {a : Ideal (𝓞 F) → ℂ} (h : Rel w e t a) :
    Rel w e t (coefDiv a v.asIdeal) := by
  intro m hm
  by_cases h1 : v.asIdeal ∣ m
  · obtain ⟨n, rfl⟩ := h1
    have hn : n ≠ ⊥ := fun h0 => hm (by rw [h0, Ideal.mul_bot])
    rw [div_comm hvw.symm, mul_left_comm, div_mul, div_mul, ← h n hn]
    simp only [div_mul]
  · rw [div_not _ _ h1, div_not _ _ (not_dvd_mul hvw h1)]
    by_cases h2 : w.asIdeal ∣ m
    · obtain ⟨n, rfl⟩ := h2
      rw [div_mul, div_not _ _ (fun h3 => h1 (h3.mul_left _))]
      simp
    · rw [div_not _ _ h2]
      simp

private theorem div_add (a b : Ideal (𝓞 F) → ℂ) (z : ℂ) (q m : Ideal (𝓞 F)) :
    coefDiv (a + z • b) q m = coefDiv a q m + z * coefDiv b q m := by
  unfold coefDiv
  split_ifs <;> simp

private theorem rel_add {w : Pl F} {e t : ℂ} {a b : Ideal (𝓞 F) → ℂ} (z : ℂ) (h : Rel w e t a) (h' : Rel w e t b) :
    Rel w e t (a + z • b) := by
  intro m hm
  rw [div_add]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination h m hm + z * h' m hm

private theorem rel_same {w : Pl F} {x y : ℂ} {a : Ideal (𝓞 F) → ℂ} (h : Rel w (x * y) (x + y) a) :
    Rel w 0 x (a + (-y) • coefDiv a w.asIdeal) := by
  intro m hm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_mul]
  linear_combination h m hm

private theorem ord_fin {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : {w : Pl F | ordI w I ≠ 0}.Finite := by
  refine (Ideal.finite_factors hI).subset fun w hw => ?_
  exact (Associates.count_ne_zero_iff_dvd hI w.irreducible).1 hw

private theorem chi_mul (ω : HChar F) (c : Pl F → ℕ) {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    chiI ω c (I * J) = chiI ω c I * chiI ω c J := by
  unfold chiI
  rw [← finprod_mul_distrib]
  · refine finprod_congr fun w => ?_
    rw [← pow_add]
    congr 1
    unfold ordI
    rw [← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.2 hI) (Associates.mk_ne_zero.2 hJ) w.associates_irreducible]
  · refine (ord_fin hI).subset fun w hw h0 => hw ?_
    simp only [h0, pow_zero]
  · refine (ord_fin hJ).subset fun w hw h0 => hw ?_
    simp only [h0, pow_zero]

private theorem chi_prime (ω : HChar F) (c : Pl F → ℕ) (w : Pl F) :
    chiI ω c w.asIdeal = if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0 := by
  unfold chiI
  rw [finprod_eq_single _ w]
  · have : ordI w w.asIdeal = 1 := Associates.count_self w.associates_irreducible
    rw [this, pow_one]
  · intro v hv
    have : ordI v w.asIdeal = 0 := by
      by_contra h0
      have h1 := (Associates.count_ne_zero_iff_dvd w.ne_bot v.irreducible).1 h0
      exact hv (HeightOneSpectrum.ext (associated_iff_eq.1 ((v.prime.dvd_prime_iff_associated w.prime).1 h1)))
    rw [this, pow_zero]

private theorem chi_top (ω : HChar F) (c : Pl F → ℕ) : chiI ω c ⊤ = 1 := by
  unfold chiI
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  have : ordI v ⊤ = 0 := by
    by_contra h0
    have h1 := (Associates.count_ne_zero_iff_dvd top_ne_bot v.irreducible).1 h0
    exact v.isPrime.ne_top (top_le_iff.1 (Ideal.dvd_iff_le.1 h1))
  rw [this, pow_zero]

private theorem dvd_fin {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) : {r : Ideal (𝓞 F) | r ∣ m}.Finite := by
  have := UniqueFactorizationMonoid.fintypeSubtypeDvd m hm
  exact Set.finite_coe_iff.1 (Finite.of_fintype {r // r ∣ m})

private theorem sum_step (χ : Ideal (𝓞 F) → ℂ) (hχ : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → χ (I * J) = χ I * χ J) (w : Pl F)
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) :
    ∑ᶠ r ∈ {r | r ∣ w.asIdeal * m}, χ r = χ w.asIdeal * ∑ᶠ r ∈ {r | r ∣ m}, χ r + ∑ᶠ r ∈ {r | r ∣ m ∧ ¬ w.asIdeal ∣ r}, χ r := by
  have hs : {r | r ∣ w.asIdeal * m} = (fun r => w.asIdeal * r) '' {r | r ∣ m} ∪ {r | r ∣ m ∧ ¬ w.asIdeal ∣ r} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro h
      by_cases h1 : w.asIdeal ∣ r
      · obtain ⟨n, rfl⟩ := h1
        exact Or.inl ⟨n, (mul_dvd_mul_iff_left w.ne_bot).1 h, rfl⟩
      · refine Or.inr ⟨?_, h1⟩
        exact ((w.irreducible.isRelPrime_iff_not_dvd.2 h1).symm).dvd_of_dvd_mul_left h
    · rintro (⟨n, hn, rfl⟩ | ⟨h, -⟩)
      · exact mul_dvd_mul_left _ hn
      · exact h.mul_left _
  rw [hs, finsum_mem_union _ ((dvd_fin hm).image _) ((dvd_fin hm).subset fun r h => h.1),
    finsum_mem_image (fun x _ y _ h => mul_left_cancel₀ w.ne_bot h)]
  · congr 1
    rw [finsum_mem_eq_finite_toFinset_sum _ (dvd_fin hm), finsum_mem_eq_finite_toFinset_sum _ (dvd_fin hm), Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => hχ _ _ w.ne_bot ?_
    rintro rfl
    exact hm (zero_dvd_iff.1 ((dvd_fin hm).mem_toFinset.1 hr))
  · rw [Set.disjoint_left]
    rintro _ ⟨n, -, rfl⟩ h
    exact h.2 (dvd_mul_right _ _)

private theorem rel_sum (χ : Ideal (𝓞 F) → ℂ) (hχ : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → χ (I * J) = χ I * χ J) (w : Pl F) :
    Rel w (χ w.asIdeal) (1 + χ w.asIdeal) fun m => ∑ᶠ r ∈ {r | r ∣ m}, χ r := by
  intro m hm
  simp only
  rw [sum_step χ hχ w hm]
  by_cases h : w.asIdeal ∣ m
  · obtain ⟨n, rfl⟩ := h
    have hn : n ≠ ⊥ := fun h0 => hm (by rw [h0, Ideal.mul_bot])
    have hs : {r | r ∣ w.asIdeal * n ∧ ¬ w.asIdeal ∣ r} = {r | r ∣ n ∧ ¬ w.asIdeal ∣ r} := by
      ext r
      exact ⟨fun h => ⟨((w.irreducible.isRelPrime_iff_not_dvd.2 h.2).symm).dvd_of_dvd_mul_left h.1, h.2⟩,
        fun h => ⟨h.1.mul_left _, h.2⟩⟩
    rw [div_mul, hs]
    linear_combination -sum_step χ hχ w hn
  · have hs : {r | r ∣ m ∧ ¬ w.asIdeal ∣ r} = {r | r ∣ m} := by
      ext r
      exact ⟨fun h => h.1, fun h1 => ⟨h1, fun h2 => h (h2.trans h1)⟩⟩
    rw [div_not _ _ h, hs]
    ring

private def intS {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) : Subring ℂ where
  carrier := {z | ‖ι.symm z‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

private theorem val_mem {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {ω : HChar F} (hω : IsOfFinOrder ω) (w : Pl F) :
    ((ω.val w : ℂˣ) : ℂ) ∈ intS ι := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hω
  have h1 : ∀ k : ℕ, (ω ^ k).val w = ω.val w ^ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, pow_succ, HChar.val_mul, ih]
  have h2 : ω.val w ^ n = 1 := by rw [← h1, h]; rfl
  have h3 : ‖ι.symm ((ω.val w : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, h2]
    simp
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h3).le

private theorem chi_mem (S : Subring ℂ) {ω : HChar F} (h : ∀ w, ((ω.val w : ℂˣ) : ℂ) ∈ S) (c : Pl F → ℕ) (I : Ideal (𝓞 F)) :
    chiI ω c I ∈ S := by
  unfold chiI
  refine finprod_induction (· ∈ S) S.one_mem (fun _ _ => S.mul_mem) fun w => S.pow_mem ?_ _
  split_ifs
  exacts [h w, S.zero_mem]

private theorem div_mem (S : Subring ℂ) {a : Ideal (𝓞 F) → ℂ} (h : ∀ m, a m ∈ S) (q m : Ideal (𝓞 F)) : coefDiv a q m ∈ S := by
  unfold coefDiv
  split_ifs
  exacts [h _, S.zero_mem]

open Classical in
private theorem step [IsTotallyReal F] (S : Subring ℂ) (ω : HChar F) (hS : ∀ w, ((ω.val w : ℂˣ) : ℂ) ∈ S) (c : Pl F → ℕ)
    (P : Set (Pl F)) (φ₀ : TR.Sm F 2) (L₀ : ℂ) (h1 : IsHol 1 c ω φ₀)
    (h2 : HasExp φ₀.1 1 (fun _ => L₀) fun 𝔪 => ∑ᶠ 𝔯 ∈ {𝔯 | 𝔯 ∣ 𝔪}, chiI ω c 𝔯) (T : Finset (Pl F)) (hT : ∀ w ∈ T, c w = 0) :
    ∃ (φ : TR.Sm F 2) (L : ℂ) (a : Ideal (𝓞 F) → ℂ), IsHol 1 (fun w => if w ∈ T then 1 else c w) ω φ ∧
      HasExp φ.1 1 (fun _ => L) a ∧ ((∃ w ∈ T, w ∈ P) → L = 0) ∧ a ⊤ = 1 ∧ (∀ m, a m ∈ S) ∧
      (∀ w ∈ T, Rel w 0 (if w ∈ P then ((ω.val w : ℂˣ) : ℂ) else 1) a) ∧
      ∀ w ∉ T, Rel w (chiI ω c w.asIdeal) (1 + chiI ω c w.asIdeal) a := by
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨φ₀, L₀, _, by simpa using h1, h2, by simp, ?_, fun m => ?_, by simp, fun w _ => rel_sum _ (fun I J => chi_mul ω c) w⟩
    · have : {r : Ideal (𝓞 F) | r ∣ ⊤} = {⊤} := by
        ext r
        simp [Ideal.dvd_iff_le]
      simp only [this, finsum_mem_singleton, chi_top]
    · refine finsum_mem_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem) fun r _ => chi_mem S hS c r
  | insert v T hv ih =>
    obtain ⟨φ, L, a, g1, g2, g3, g4, g5, g6, g7⟩ := ih fun w hw => hT w (Finset.mem_insert_of_mem hw)
    have hc : c v = 0 := hT v (Finset.mem_insert_self _ _)
    obtain ⟨ψ, u, k1, k2⟩ := holB F 1 _ ω φ _ a v g1 g2
    have he : Function.update (fun w => if w ∈ T then 1 else c w) v ((if v ∈ T then 1 else c v) + 1) =
        fun w => if w ∈ insert v T then 1 else c w := by
      funext w
      by_cases hw : w = v
      · subst hw
        simp [hv, hc]
      · simp [hw]
    rw [he] at k1
    obtain ⟨-, -, l1, -, l2⟩ := holLin F 1 (fun w => if w ∈ insert v T then 1 else c w) ω
    obtain ⟨-, -, -, l3, l4⟩ := holLin F 1 (fun w => if w ∈ T then 1 else c w) ω
    have g1' : IsHol 1 (fun w => if w ∈ insert v T then 1 else c w) ω φ := by
      refine l4 φ _ (fun w => ?_) g1
      by_cases hw : w = v
      · subst hw
        simp [hv, hc]
      · simp [hw]
    set y : ℂ := if v ∈ P then 1 else ((ω.val v : ℂˣ) : ℂ) with hy
    have hyS : y ∈ S := by
      rw [hy]
      split_ifs
      exacts [S.one_mem, hS v]
    refine ⟨φ + (-y) • ψ, L + (-y) * L, a + (-y) • coefDiv a v.asIdeal, l1 _ _ _ g1' k1, l3 _ _ (-y) _ _ _ _ g2 k2, ?_, ?_,
      fun m => S.add_mem (g5 m) (S.mul_mem (S.neg_mem hyS) (div_mem S g5 _ _)), fun w hw => ?_, fun w hw => ?_⟩
    · rintro ⟨w, hw, hP⟩
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rw [hy, if_pos hP]
        ring
      · rw [g3 ⟨w, hw, hP⟩]
        ring
    · have : ¬ v.asIdeal ∣ ⊤ := fun h => v.isPrime.ne_top (top_le_iff.1 (Ideal.dvd_iff_le.1 h))
      simp [g4, div_not a v this]
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · apply rel_same
        have := g7 w hv
        rw [chi_prime, if_pos hc] at this
        rw [hy]
        split_ifs
        · rwa [mul_one, add_comm]
        · rwa [one_mul]
      · exact rel_add _ (g6 w hw) (rel_div (fun h : v = w => hv (h ▸ hw)) (g6 w hw))
    · rw [Finset.mem_insert, not_or] at hw
      exact rel_add _ (g7 w hw.2) (rel_div (Ne.symm hw.1) (g7 w hw.2))

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.emix :
    UpperTheory.V.Published.HilbertEisOne → UpperTheory.V.Sd.Emix := by
  intro hE F _ _ _ l hl ι ω c hω hodd hcond hne hcl P hP
  classical
  obtain ⟨φ₀, L₀, h1, h2⟩ := hE F ω c hω hodd hcond hne
  have hl0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.out.ne_zero
  have hfin := Ideal.finite_factors hl0
  have hT : ∀ w : Pl F, w ∈ hfin.toFinset ↔ ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := fun w => by
    rw [hfin.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  obtain ⟨φ, L, a, g1, g2, g3, g4, g5, g6, g7⟩ := step (intS ι) ω (val_mem ι hω) c P φ₀ L₀ h1 h2 hfin.toFinset
    fun w hw => hcl w ((hT w).1 hw)
  obtain ⟨w₀, hw₀, hw₁⟩ := hP
  obtain rfl := g3 ⟨w₀, (hT _).2 hw₁, hw₀⟩
  have he : (fun w => if w ∈ hfin.toFinset then 1 else c w) = levL l c := by
    funext w
    simp only [levL, hT]
  refine ⟨φ, a, he ▸ g1, g2, g4, fun m _ => g5 m, fun w m hm => ?_⟩
  unfold hkCoef eisT
  rw [chi_prime, Nat.sub_self, pow_zero, mul_one]
  by_cases hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
  · have := g6 w ((hT w).2 hw) m hm
    simp only [levL, hw, if_true, one_ne_zero, if_false]
    convert this
  · have := g7 w (fun h => hw ((hT w).1 h)) m hm
    rw [chi_prime] at this
    simp only [levL, hw, if_false]
    rw [this]
    split_ifs <;> simp
