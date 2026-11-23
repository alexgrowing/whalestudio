import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HomogCob

variable {R : Type} [CommRing R]

theorem hom_mul {σ : Type} {m n : ℕ} {g h : MvPowerSeries σ R}
    (hg : ∀ e : σ →₀ ℕ, e.degree ≠ m → coeff e g = 0)
    (hh : ∀ e : σ →₀ ℕ, e.degree ≠ n → coeff e h = 0) :
    ∀ e : σ →₀ ℕ, e.degree ≠ m + n → coeff e (g * h) = 0 := by
  classical
  intro e he
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_cases h1 : p.1.degree = m
  · have h2 : p.2.degree ≠ n := by
      intro h2; apply he; rw [← hp, map_add, h1, h2]
    rw [hh _ h2, mul_zero]
  · rw [hg _ h1, zero_mul]

theorem hom_one {σ : Type} : ∀ e : σ →₀ ℕ, e.degree ≠ 0 → coeff e (1 : MvPowerSeries σ R) = 0 := by
  classical
  intro e he
  rw [coeff_one, if_neg]
  rintro rfl; exact he (map_zero _)

theorem hom_pow {σ : Type} {g : MvPowerSeries σ R}
    (hg : ∀ e : σ →₀ ℕ, e.degree ≠ 1 → coeff e g = 0) (b : ℕ) :
    ∀ e : σ →₀ ℕ, e.degree ≠ b → coeff e (g ^ b) = 0 := by
  induction b with
  | zero => simpa using hom_one
  | succ b ih => rw [pow_succ]; exact hom_mul ih hg

theorem hom_prod {σ τ : Type} {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, ∀ e : τ →₀ ℕ, e.degree ≠ 1 → coeff e (a s) = 0) (d : σ →₀ ℕ) :
    ∀ e : τ →₀ ℕ, e.degree ≠ d.degree → coeff e (d.prod fun s n => a s ^ n) = 0 := by
  induction d using Finsupp.induction with
  | zero => simpa using hom_one
  | single_add s b f _ _ ih =>
    rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), Finsupp.prod_single_index (by simp),
      map_add, Finsupp.degree_single]
    exact hom_mul (hom_pow (ha s) b) ih

theorem hom_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, ∀ e : τ →₀ ℕ, e.degree ≠ 1 → coeff e (a s) = 0) {N : ℕ} {f : MvPowerSeries σ R}
    (hf : ∀ e : σ →₀ ℕ, e.degree ≠ N → coeff e f = 0) :
    ∀ e : τ →₀ ℕ, e.degree ≠ N → coeff e (subst a f) = 0 := by
  intro e he
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero fun s => by
    rw [← coeff_zero_eq_constantCoeff_apply]; exact ha s 0 (by simp)
  rw [coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : d.degree = N
  · rw [hom_prod ha d e (by rw [hd]; exact he), smul_zero]
  · rw [hf d hd, zero_smul]

theorem hom_X {σ : Type} (s : σ) :
    ∀ e : σ →₀ ℕ, e.degree ≠ 1 → coeff e (X s : MvPowerSeries σ R) = 0 := by
  classical
  intro e he
  rw [coeff_X, if_neg]
  rintro rfl; exact he (by simp)

theorem hom_add {σ : Type} {n : ℕ} {g h : MvPowerSeries σ R}
    (hg : ∀ e : σ →₀ ℕ, e.degree ≠ n → coeff e g = 0)
    (hh : ∀ e : σ →₀ ℕ, e.degree ≠ n → coeff e h = 0) :
    ∀ e : σ →₀ ℕ, e.degree ≠ n → coeff e (g + h) = 0 := by
  intro e he; rw [map_add, hg e he, hh e he, add_zero]

theorem hom_sub {σ : Type} {n : ℕ} {g h : MvPowerSeries σ R}
    (hg : ∀ e : σ →₀ ℕ, e.degree ≠ n → coeff e g = 0)
    (hh : ∀ e : σ →₀ ℕ, e.degree ≠ n → coeff e h = 0) :
    ∀ e : σ →₀ ℕ, e.degree ≠ n → coeff e (g - h) = 0 := by
  intro e he; rw [map_sub, hg e he, hh e he, sub_zero]

theorem hom_addLaw (d : ℕ) (i : Fin d) :
    ∀ e : Fin d ⊕ Fin d →₀ ℕ, e.degree ≠ 1 → coeff e (addLaw R d i) = 0 :=
  hom_add (hom_X _) (hom_X _)

theorem hom_elim {τ : Type} {d : ℕ} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ s, ∀ e : τ →₀ ℕ, e.degree ≠ 1 → coeff e (u s) = 0)
    (hv : ∀ s, ∀ e : τ →₀ ℕ, e.degree ≠ 1 → coeff e (v s) = 0) :
    ∀ s, ∀ e : τ →₀ ℕ, e.degree ≠ 1 → coeff e (Sum.elim u v s) = 0 := by
  rintro (s | s) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> [exact hu s; exact hv s]

theorem coeff_cob1_addLaw_eq_zero_of_degree_ne (d N : ℕ) (f : MvPowerSeries (Fin d) R)
    (hf : ∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α f = 0) :
    ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ (cob1 (addLaw R d) f) = 0 := by
  unfold cob1 inL inR
  exact hom_sub (hom_sub (hom_subst (hom_addLaw d) hf) (hom_subst (fun _ => hom_X _) hf))
    (hom_subst (fun _ => hom_X _) hf)

theorem coeff_cob2_addLaw_eq_zero_of_degree_ne (d N : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree ≠ N → coeff α c = 0) :
    ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≠ N → coeff γ (cob2 (addLaw R d) c) = 0 := by
  have h1 : ∀ s, ∀ e : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, e.degree ≠ 1 → coeff e (x1 (R := R) s) = 0 :=
    fun s => hom_X _
  have h2 : ∀ s, ∀ e : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, e.degree ≠ 1 → coeff e (x2 (R := R) s) = 0 :=
    fun s => hom_X _
  have h3 : ∀ s, ∀ e : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, e.degree ≠ 1 → coeff e (x3 (R := R) s) = 0 :=
    fun s => hom_X _
  have hop : ∀ {u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R},
      (∀ s, ∀ e : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, e.degree ≠ 1 → coeff e (u s) = 0) →
      (∀ s, ∀ e : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, e.degree ≠ 1 → coeff e (v s) = 0) →
      ∀ s, ∀ e : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, e.degree ≠ 1 → coeff e (op (addLaw R d) u v s) = 0 :=
    fun hu hv s => hom_subst (hom_elim hu hv) (hom_addLaw d s)
  unfold cob2 at2
  exact hom_sub (hom_add (hom_sub (hom_subst (hom_elim h2 h3) hc)
    (hom_subst (hom_elim (hop h1 h2) h3) hc)) (hom_subst (hom_elim h1 (hop h2 h3)) hc))
    (hom_subst (hom_elim h1 h2) hc)

end GlobalTheory.HomogCob

namespace GlobalTheory.HomogCob

variable {R : Type} [CommRing R]

theorem prod_X_map {σ τ : Type} (g : σ → τ) (δ : σ →₀ ℕ) :
    (δ.prod fun s n => (X (g s) : MvPowerSeries τ R) ^ n) = monomial (δ.mapDomain g) 1 := by
  induction δ using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), Finsupp.prod_single_index (by simp),
      ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single, X_pow_eq, monomial_mul_monomial, mul_one]

theorem coeff_swap_eq (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (γ : Fin d ⊕ Fin d →₀ ℕ) :
    coeff γ (swap c) = coeff (γ.mapDomain Sum.swap) c := by
  classical
  have ha : (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inl i))) = fun s => X (Sum.swap s) := by
    funext s; rcases s with s | s <;> rfl
  have hs : HasSubst (fun s : Fin d ⊕ Fin d => (X (Sum.swap s) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _
  unfold swap at2
  rw [ha, coeff_subst hs]
  simp_rw [prod_X_map, coeff_monomial]
  rw [finsum_eq_single _ (γ.mapDomain Sum.swap)]
  · rw [← Finsupp.mapDomain_comp, Sum.swap_swap_eq, Finsupp.mapDomain_id, if_pos rfl, smul_eq_mul,
      mul_one]
  · intro δ hδ
    rw [if_neg, smul_zero]
    rintro rfl
    apply hδ
    rw [← Finsupp.mapDomain_comp, Sum.swap_swap_eq, Finsupp.mapDomain_id]

end GlobalTheory.HomogCob

namespace GlobalTheory.HomogCob

variable {R : Type} [CommRing R]

theorem mdl_inl {d : ℕ} (β : Fin d →₀ ℕ) (k : Fin d) :
    (β.mapDomain Sum.inl : Fin d ⊕ Fin d →₀ ℕ) (Sum.inl k) = β k :=
  Finsupp.mapDomain_apply Sum.inl_injective β k

theorem mdl_inr {d : ℕ} (β : Fin d →₀ ℕ) (k : Fin d) :
    (β.mapDomain Sum.inl : Fin d ⊕ Fin d →₀ ℕ) (Sum.inr k) = 0 :=
  Finsupp.mapDomain_notin_range _ _ (by simp)

theorem mdr_inl {d : ℕ} (β : Fin d →₀ ℕ) (k : Fin d) :
    (β.mapDomain Sum.inr : Fin d ⊕ Fin d →₀ ℕ) (Sum.inl k) = 0 :=
  Finsupp.mapDomain_notin_range _ _ (by simp)

theorem eqA {d : ℕ} (a β : Fin d →₀ ℕ) (j : Fin d) (h : 1 ≤ β j) :
    a = β - Finsupp.single j 1 ↔ a + Finsupp.single j 1 = β := by
  constructor
  · rintro rfl
    ext k
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
    split_ifs with h1 <;> (try subst h1) <;> omega
  · rintro rfl
    ext k
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
    split_ifs <;> omega

theorem neA {d : ℕ} (a β : Fin d →₀ ℕ) (j : Fin d) (h : β j = 0) :
    a + Finsupp.single j 1 ≠ β := by
  intro e
  have := DFunLike.congr_fun e j
  simp at this
  omega

theorem eqB {d : ℕ} (a β : Fin d →₀ ℕ) (j i : Fin d) (hji : j ≠ i) (h : 1 ≤ β j) :
    a = β - Finsupp.single j 1 + Finsupp.single i 1 ↔ a + Finsupp.single j 1 = β + Finsupp.single i 1 := by
  constructor
  · rintro rfl
    ext k
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
    by_cases h1 : j = k
    · subst h1; simp [hji]; omega
    · by_cases h2 : i = k
      · subst h2; simp [h1]
      · simp [h1, h2]
  · intro e
    ext k
    have := DFunLike.congr_fun e k
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply] at this ⊢
    by_cases h1 : j = k
    · subst h1; simp [hji] at this ⊢; omega
    · by_cases h2 : i = k
      · subst h2; simp [h1] at this ⊢; omega
      · simp [h1, h2] at this ⊢; omega

theorem neB {d : ℕ} (a β : Fin d →₀ ℕ) (j i : Fin d) (hji : j ≠ i) (h : β j = 0) :
    a + Finsupp.single j 1 ≠ β + Finsupp.single i 1 := by
  intro e
  have := DFunLike.congr_fun e j
  simp [Finsupp.single_apply, hji.symm] at this
  omega

theorem eqC {d : ℕ} (β : Fin d →₀ ℕ) (j : Fin d) (h : 1 ≤ β j) :
    β - Finsupp.single j 1 + Finsupp.single j 1 = β := by
  ext k
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
  split_ifs with h1 <;> (try subst h1) <;> omega

theorem subA {d : ℕ} (β : Fin d →₀ ℕ) (j : Fin d) :
    (β.mapDomain Sum.inl : Fin d ⊕ Fin d →₀ ℕ) - Finsupp.single (Sum.inl j) 1 =
      (β - Finsupp.single j 1).mapDomain Sum.inl := by
  ext k
  rcases k with k | k
  · simp only [Finsupp.coe_tsub, Pi.sub_apply, mdl_inl, Finsupp.single_apply, Sum.inl.injEq]
  · simp [mdl_inr, Finsupp.single_apply]

theorem subB {d : ℕ} (β : Fin d →₀ ℕ) (j i : Fin d) :
    (β.mapDomain Sum.inl : Fin d ⊕ Fin d →₀ ℕ) + Finsupp.single (Sum.inr i) 1 -
      Finsupp.single (Sum.inl j) 1 =
      (β - Finsupp.single j 1).mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 := by
  ext k
  rcases k with k | k
  · simp [mdl_inl, Finsupp.single_apply]
  · simp [mdl_inr, Finsupp.single_apply]

end GlobalTheory.HomogCob

namespace GlobalTheory.HomogCob

variable {R : Type} [CommRing R]

theorem hX {σ : Type} (s : σ) : (X s : MvPowerSeries σ R) = monomial (Finsupp.single s 1) 1 := by
  rw [← pow_one (X s), X_pow_eq]

theorem coeff_prod_addLaw (d n : ℕ) : ∀ α : Fin d →₀ ℕ, α.degree = n → ∀ β : Fin d →₀ ℕ,
    coeff (β.mapDomain Sum.inl) (α.prod fun s m => addLaw R d s ^ m) = (if α = β then 1 else 0) ∧
    ∀ i : Fin d, coeff (β.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1)
      (α.prod fun s m => addLaw R d s ^ m) = if α = β + Finsupp.single i 1 then (α i : R) else 0 := by
  classical
  induction n with
  | zero =>
    intro α hα β
    rw [Finsupp.degree_eq_zero_iff] at hα
    subst hα
    rw [Finsupp.prod_zero_index]
    refine ⟨?_, fun i => ?_⟩
    · rw [coeff_one]
      by_cases hβ : β = 0
      · subst hβ; simp
      · rw [if_neg, if_neg (Ne.symm hβ)]
        intro h; apply hβ; ext k
        have := DFunLike.congr_fun h (Sum.inl k)
        simpa [mdl_inl] using this
    · rw [coeff_one, if_neg, if_neg]
      · intro h
        have := DFunLike.congr_fun h i
        simp at this
      · intro h
        have := DFunLike.congr_fun h (Sum.inr i)
        simp [mdl_inr] at this
  | succ n ih =>
    intro α hα β
    obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
      by_contra! hc
      have : α = 0 := Finsupp.ext hc
      rw [this, map_zero] at hα
      omega
    obtain ⟨a, rfl⟩ : ∃ a, α = a + Finsupp.single j 1 := ⟨α - Finsupp.single j 1, by
      ext k
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with h1 <;> (try subst h1) <;> omega⟩
    have ha : a.degree = n := by
      rw [map_add, Finsupp.degree_single] at hα; omega
    have hP : ((a + Finsupp.single j 1).prod fun s m => addLaw R d s ^ m) =
        (a.prod fun s m => addLaw R d s ^ m) * monomial (Finsupp.single (Sum.inl j) 1) 1 +
        (a.prod fun s m => addLaw R d s ^ m) * monomial (Finsupp.single (Sum.inr j) 1) 1 := by
      rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]),
        Finsupp.prod_single_index (by simp), pow_one, ← hX, ← hX, ← mul_add]
      rfl
    rw [hP]
    refine ⟨?_, fun i => ?_⟩
    · rw [map_add, coeff_mul_monomial, coeff_mul_monomial, if_neg (c := Finsupp.single (Sum.inr j) 1 ≤ _), add_zero]
      swap
      · rw [Finsupp.single_le_iff, mdl_inr]; omega
      by_cases hb : 1 ≤ β j
      · rw [if_pos (by rw [Finsupp.single_le_iff, mdl_inl]; exact hb), subA, (ih a ha _).1, mul_one]
        simp only [eqA a β j hb]
      · rw [if_neg (by rw [Finsupp.single_le_iff, mdl_inl]; exact hb), if_neg (neA a β j (by omega))]
    · rw [map_add, coeff_mul_monomial, coeff_mul_monomial]
      by_cases hji : j = i
      · subst hji
        rw [if_pos (c := Finsupp.single (Sum.inr j) 1 ≤ _) (by simp [Finsupp.single_le_iff]),
          add_tsub_cancel_right, (ih a ha _).1]
        simp only [add_left_inj]
        by_cases hb : 1 ≤ β j
        · rw [if_pos (by rw [Finsupp.single_le_iff]; simpa [mdl_inl] using hb), subB, (ih a ha _).2,
            eqC β j hb]
          by_cases hab : a = β
          · subst hab; simp <;> ring
          · simp [hab]
        · rw [if_neg (by rw [Finsupp.single_le_iff]; simpa [mdl_inl] using hb), zero_add]
          by_cases hab : a = β
          · subst hab
            have : a j = 0 := by omega
            simp [this]
          · simp [hab]
      · rw [if_neg (c := Finsupp.single (Sum.inr j) 1 ≤ _)
          (by rw [Finsupp.single_le_iff]; simp [mdl_inr, Finsupp.single_apply, Ne.symm hji]), add_zero]
        have hi : (((a + Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : R) = (a i : R) := by
          simp [Finsupp.single_apply, hji]
        rw [hi]
        by_cases hb : 1 ≤ β j
        · rw [if_pos (by rw [Finsupp.single_le_iff]; simpa [mdl_inl] using hb), subB, (ih a ha _).2,
            mul_one]
          simp only [eqB a β j i hji hb]
        · rw [if_neg (by rw [Finsupp.single_le_iff]; simpa [mdl_inl] using hb),
            if_neg (neB a β j i hji (by omega))]

end GlobalTheory.HomogCob

namespace GlobalTheory.HomogCob

variable {R : Type} [CommRing R]

theorem coeff_cob1_additive_law_mixed (d : ℕ) (f : MvPowerSeries (Fin d) R) (β : Fin d →₀ ℕ) (i : Fin d)
    (hβ : β ≠ 0) :
    coeff (β.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) (cob1 (addLaw R d) f) =
      ((β i + 1 : ℕ) : R) * coeff (β + Finsupp.single i 1) f := by
  classical
  have hL : HasSubst (fun s : Fin d => (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _
  have hR : HasSubst (fun s : Fin d => (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _
  have hA : HasSubst (addLaw R d) := hasSubst_of_constantCoeff_zero fun s => by
    simp [addLaw]
  unfold cob1 inL inR
  rw [map_sub, map_sub, coeff_subst hL, coeff_subst hR, coeff_subst hA]
  simp_rw [prod_X_map, coeff_monomial]
  have h1 : (∑ᶠ δ : Fin d →₀ ℕ, coeff δ f • (if β.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 =
      δ.mapDomain Sum.inl then (1 : R) else 0)) = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun δ => ?_
    rw [if_neg, smul_zero]
    intro h
    have := DFunLike.congr_fun h (Sum.inr i)
    simp [mdl_inr, Finsupp.mapDomain_apply Sum.inl_injective] at this
  have h2 : (∑ᶠ δ : Fin d →₀ ℕ, coeff δ f • (if β.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 =
      δ.mapDomain Sum.inr then (1 : R) else 0)) = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun δ => ?_
    rw [if_neg, smul_zero]
    obtain ⟨k, hk⟩ : ∃ k, β k ≠ 0 := by
      by_contra! hc; exact hβ (Finsupp.ext hc)
    intro h
    have := DFunLike.congr_fun h (Sum.inl k)
    simp [mdl_inl, mdr_inl] at this
    exact hk this
  rw [h1, h2, sub_zero, sub_zero]
  · rw [finsum_eq_single _ (β + Finsupp.single i 1)]
    · rw [(coeff_prod_addLaw d _ _ rfl β).2 i, if_pos rfl, smul_eq_mul, mul_comm]
      simp
    · intro δ hδ
      rw [(coeff_prod_addLaw d _ δ rfl β).2 i, if_neg hδ, smul_zero]

end GlobalTheory.HomogCob

theorem GlobalTheory.homog_cob_addLaw : ∀ (R : Type) [CommRing R] (d N : ℕ), (∀ f : MvPowerSeries (Fin d) R, (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α f = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ (cob1 (addLaw R d) f) = 0) ∧ (∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree ≠ N → coeff α c = 0) → ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≠ N → coeff γ (cob2 (addLaw R d) c) = 0) ∧ (∀ (c : MvPowerSeries (Fin d ⊕ Fin d) R) (γ : Fin d ⊕ Fin d →₀ ℕ), coeff γ (swap c) = coeff (γ.mapDomain Sum.swap) c) ∧ ∀ (f : MvPowerSeries (Fin d) R) (β : Fin d →₀ ℕ) (i : Fin d), β ≠ 0 → coeff (β.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) (cob1 (addLaw R d) f) = ((β i + 1 : ℕ) : R) * coeff (β + Finsupp.single i 1) f :=
  fun _ _ d N => ⟨GlobalTheory.HomogCob.coeff_cob1_addLaw_eq_zero_of_degree_ne d N, GlobalTheory.HomogCob.coeff_cob2_addLaw_eq_zero_of_degree_ne d N, GlobalTheory.HomogCob.coeff_swap_eq d,
    GlobalTheory.HomogCob.coeff_cob1_additive_law_mixed d⟩
