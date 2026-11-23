import Formalism.SatakeDualWeyl.StatementE
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeMat
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeRes
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Main

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

abbrev satakeTset (ϖ : v.adicCompletion F) (j : ℕ) : Set (GL (Fin n) (v.adicCompletion F)) :=
  {g | ∃ a ∈ GLint (Fin n) (Ov F v), ∃ b ∈ GLint (Fin n) (Ov F v),
    (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a : Matrix (Fin n) (Fin n) _) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) _)}

theorem satake_Tset_right {ϖ : v.adicCompletion F} {j : ℕ} {g k : GL (Fin n) (v.adicCompletion F)}
    (hg : g ∈ satakeTset v ϖ j) (hk : k ∈ GLint (Fin n) (Ov F v)) : g * k ∈ satakeTset v ϖ j := by
  obtain ⟨a, ha, b, hb, e⟩ := hg
  exact ⟨a, ha, b * k, (GLint (Fin n) (Ov F v)).mul_mem hb hk, by
    rw [Units.val_mul, e, Units.val_mul, Matrix.mul_assoc]⟩

theorem satake_Tset_left {ϖ : v.adicCompletion F} {j : ℕ} {g k : GL (Fin n) (v.adicCompletion F)}
    (hg : g ∈ satakeTset v ϖ j) (hk : k ∈ GLint (Fin n) (Ov F v)) : k * g ∈ satakeTset v ϖ j := by
  obtain ⟨a, ha, b, hb, e⟩ := hg
  exact ⟨k * a, (GLint (Fin n) (Ov F v)).mul_mem hk ha, b, hb, by
    rw [Units.val_mul, e, Units.val_mul]; simp only [Matrix.mul_assoc]⟩

theorem satake_Tj_eq (k : Type) [CommRing k] (ϖ : v.adicCompletion F) (j : ℕ)
    (g : GL (Fin n) (v.adicCompletion F)) :
    Tj k n (Ov F v) ϖ j g = Set.indicator (satakeTset v ϖ j) 1 g := rfl

theorem satake_Tj_ne_zero_iff (k : Type) [CommRing k] [Nontrivial k] (ϖ : v.adicCompletion F) (j : ℕ)
    (g : GL (Fin n) (v.adicCompletion F)) :
    Tj k n (Ov F v) ϖ j g ≠ 0 ↔ g ∈ satakeTset v ϖ j := by
  rw [satake_Tj_eq]
  by_cases h : g ∈ satakeTset v ϖ j
  · rw [Set.indicator_of_mem h]; simp [h]
  · rw [Set.indicator_of_notMem h]; simp [h]

theorem satake_prodD_ne {q : ℤ} (hq : 2 ≤ q) (j : ℕ) : ∏ i ∈ Finset.range j, (q ^ (i + 1) - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i _
  have : 1 < q ^ (i + 1) := one_lt_pow₀ (by omega) (by omega)
  omega

theorem prod_pow_sub_one_ne_zero {q : ℤ} (hq : 2 ≤ q) {j n : ℕ} (hj : j ≤ n) :
    ∏ i ∈ Finset.range j, (q ^ (n - i) - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi' := Finset.mem_range.1 hi
  have : 1 < q ^ (n - i) := one_lt_pow₀ (by omega) (by omega)
  omega

theorem satake_cosets_card (hTjCosets : TjCosets) {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v)
    (hu : IsUnifV F v ϖ) {j : ℕ} (hj : j ≤ n) :
    {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) | x.out ∈ satakeTset v ϖ j}.Finite ∧
    {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) | x.out ∈ satakeTset v ϖ j}.ncard =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, qV F v ^ satakeInv Finset.univ S := by
  have hq : (2 : ℤ) ≤ qV F v := by exact_mod_cast satake_two_le_qV v
  have h := hTjCosets F v n ϖ hϖ hu j hj
  have hset : {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) |
      Tj ℤ n (Ov F v) ϖ j x.out ≠ 0} =
      {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) | x.out ∈ satakeTset v ϖ j} := by
    ext x; exact satake_Tj_ne_zero_iff v ℤ ϖ j x.out
  rw [hset] at h
  have hb := satake_qbinom (qV F v : ℤ) (Finset.univ : Finset (Fin n)) j
  rw [Finset.card_univ, Fintype.card_fin, ← h] at hb
  have hD := satake_prodD_ne hq j
  have hc : (Nat.card {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) |
      x.out ∈ satakeTset v ϖ j} : ℤ) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, (qV F v : ℤ) ^ satakeInv Finset.univ S :=
    (mul_right_cancel₀ hD hb).symm
  have hne : Nat.card {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) |
      x.out ∈ satakeTset v ϖ j} ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, zero_mul] at h
    exact prod_pow_sub_one_ne_zero hq hj h.symm
  refine ⟨Set.finite_coe_iff.1 (Nat.finite_of_card_ne_zero hne), ?_⟩
  rw [← Nat.card_coe_set_eq]
  exact_mod_cast hc

theorem satake_cpow_prod {ι : Type} (x : ℂ) (hx : x ≠ 0) (s : Finset ι) (f : ι → ℂ) :
    ∏ i ∈ s, x ^ f i = x ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, Complex.cpow_add _ _ hx]

theorem satake_exponent (α : Fin n → ℂ) (S : Finset (Fin n)) :
    ((qV F v : ℂ)) ^ satakeInv Finset.univ S *
      ∏ a ∈ S, (α a * (qV F v : ℂ) ^ (-(((n : ℂ) - 1 - 2 * (a : ℂ)) / 2))) =
      (qV F v : ℂ) ^ (((S.card : ℂ) * ((n : ℂ) - S.card)) / 2) * ∏ a ∈ S, α a := by
  have hq : (qV F v : ℂ) ≠ 0 := by
    have := satake_two_le_qV v
    exact_mod_cast (show qV F v ≠ 0 by omega)
  rw [Finset.prod_mul_distrib, satake_cpow_prod _ hq, ← Complex.cpow_natCast, mul_left_comm,
    ← Complex.cpow_add _ _ hq, mul_comm]
  congr 2
  have h := satakeInv_two_mul S
  have h' : 2 * (satakeInv Finset.univ S : ℂ) =
      ∑ a ∈ S, ((n : ℂ) - 1 - 2 * ((a : ℕ) : ℂ)) + (S.card : ℂ) * ((n : ℂ) - S.card) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h
  rw [Finset.sum_neg_distrib, ← Finset.sum_div]
  linear_combination h' / 2

end Main

section Reps

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
  {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (hu : IsUnifV F v ϖ)

abbrev SatakeIdx (j : ℕ) : Type :=
  Σ S : {S : Finset (Fin n) // S.card = j}, satakePairs S.1 → satakeRes (Ov F v) ⟨ϖ, hϖ⟩

abbrev satakeB {j : ℕ} (i : SatakeIdx v hϖ (n := n) j) : GL (Fin n) (v.adicCompletion F) :=
  satakeRep (Ov F v) ⟨ϖ, hϖ⟩ (satake_unif_ne_zero v hu) j i

theorem satakeB_mem {j : ℕ} (i : SatakeIdx v hϖ (n := n) j) : satakeB v hϖ hu i ∈ satakeTset v ϖ j := by
  obtain ⟨a, ha, b, hb, e⟩ := satakeGL_mem_doset (Ov F v) (satake_unif_ne_zero v hu) i.1.1
    (fun p => satakeSec (Ov F v) ⟨ϖ, hϖ⟩ (i.2 p))
  rw [i.1.2] at e
  exact ⟨a, ha, b, hb, e⟩

theorem satakeB_upper {j : ℕ} (i : SatakeIdx v hϖ (n := n) j) : IsUpperB F v (satakeB v hϖ hu i) :=
  fun a l h => satakeGL_lower (Ov F v) _ _ _ a l h

theorem satakeB_inj {j : ℕ} :
    Function.Injective (fun i : SatakeIdx v hϖ (n := n) j =>
      ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v))) := by
  intro i i' h
  have h' := QuotientGroup.eq.1 h
  exact satakeRep_inj (Ov F v) ⟨ϖ, hϖ⟩ (satake_unif_ne_zero v hu) (satake_unif_inv_not_mem v hu) j i i' h'

include hu in
theorem satake_res_finite : Finite (satakeRes (Ov F v) ⟨ϖ, hϖ⟩) := by
  apply Nat.finite_of_card_ne_zero
  rw [satake_card_res v hϖ hu]
  have := satake_two_le_qV v
  omega

include hu in
theorem satake_idx_card [Fintype (satakeRes (Ov F v) ⟨ϖ, hϖ⟩)] (j : ℕ) :
    Nat.card (SatakeIdx v hϖ (n := n) j) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, qV F v ^ satakeInv Finset.univ S := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fun, satakePairs_card]
  rw [← Nat.card_eq_fintype_card, satake_card_res v hϖ hu]
  symm
  apply Finset.sum_subtype
  intro S
  simp [Finset.mem_powersetCard]

theorem satake_range_eq [Fintype (satakeRes (Ov F v) ⟨ϖ, hϖ⟩)] (hTjCosets : TjCosets) {j : ℕ}
    (hj : j ≤ n) :
    Set.range (fun i : SatakeIdx v hϖ (n := n) j =>
      ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v))) =
    {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) | x.out ∈ satakeTset v ϖ j} := by
  obtain ⟨hfin, hcard⟩ := satake_cosets_card v hTjCosets hϖ hu hj
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
  · rintro _ ⟨i, rfl⟩
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (GLint (Fin n) (Ov F v)) (satakeB v hϖ hu i)
    change (Quotient.out (((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v)))) ∈ satakeTset v ϖ j
    have e : (Quotient.out (((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v)))) = satakeB v hϖ hu i * κ := hκ
    rw [e]
    exact satake_Tset_right v (satakeB_mem v hϖ hu i) κ.2
  · rw [hcard, Set.ncard_range_of_injective (satakeB_inj v hϖ hu), satake_idx_card v hϖ hu j]

end Reps

section Value

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
  {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (hu : IsUnifV F v ϖ)

theorem satake_chiDelta_one (α : Fin n → ℂ) : chiDelta F v α 1 = 1 := by
  unfold chiDelta
  simp [satake_ordV_one v]

theorem satake_upper_one : IsUpperB F v (1 : GL (Fin n) (v.adicCompletion F)) :=
  fun a l h => by rw [Units.val_one, Matrix.one_apply_ne (ne_of_gt h)]

theorem satake_T_mul_right (j : ℕ) (z c : GL (Fin n) (v.adicCompletion F)) (hc : c ∈ GLint (Fin n) (Ov F v)) :
    Tj ℂ n (Ov F v) ϖ j (z * c) = Tj ℂ n (Ov F v) ϖ j z := by
  rw [satake_Tj_eq, satake_Tj_eq]
  by_cases h : z ∈ satakeTset v ϖ j
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (satake_Tset_right v h hc)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    intro h'
    apply h
    have := satake_Tset_right v h' ((GLint (Fin n) (Ov F v)).inv_mem hc)
    rwa [mul_inv_cancel_right] at this

theorem satake_T_mul_left (j : ℕ) (z c : GL (Fin n) (v.adicCompletion F)) (hc : c ∈ GLint (Fin n) (Ov F v)) :
    Tj ℂ n (Ov F v) ϖ j (c * z) = Tj ℂ n (Ov F v) ϖ j z := by
  rw [satake_Tj_eq, satake_Tj_eq]
  by_cases h : z ∈ satakeTset v ϖ j
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (satake_Tset_left v h hc)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    intro h'
    apply h
    have := satake_Tset_left v h' ((GLint (Fin n) (Ov F v)).inv_mem hc)
    rwa [inv_mul_cancel_left] at this

theorem satake_chiDelta_B (α : Fin n → ℂ) {j : ℕ} (i : SatakeIdx v hϖ (n := n) j) :
    chiDelta F v α (satakeB v hϖ hu i) =
      ∏ a ∈ i.1.1, (α a * (qV F v : ℂ) ^ (-(((n : ℂ) - 1 - 2 * (a : ℂ)) / 2))) := by
  unfold chiDelta
  rw [← Finset.univ_inter i.1.1, ← Finset.prod_ite_mem]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hd := satakeGL_diag (Ov F v) (satake_unif_ne_zero v hu) i.1.1
    (fun p => satakeSec (Ov F v) ⟨ϖ, hϖ⟩ (i.2 p)) a
  have e : ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) a a = if a ∈ i.1.1 then ϖ else 1 := hd
  rw [e]
  by_cases h : a ∈ i.1.1
  · simp [h, satake_ordV_unif v hu]
  · simp [h, satake_ordV_one v]

theorem satake_sum_chi [Fintype (satakeRes (Ov F v) ⟨ϖ, hϖ⟩)] (α : Fin n → ℂ) (j : ℕ) :
    ∑ i : SatakeIdx v hϖ (n := n) j, chiDelta F v α (satakeB v hϖ hu i) =
      (qV F v : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) * Multiset.esymm (Multiset.map α Finset.univ.val) j := by
  rw [Fintype.sum_sigma]
  simp_rw [satake_chiDelta_B v hϖ hu α]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, satakePairs_card]
  rw [← Nat.card_eq_fintype_card, satake_card_res v hϖ hu, Finset.esymm_map_val, Finset.mul_sum]
  rw [← Finset.sum_subtype (Finset.univ.powersetCard j) (p := fun S : Finset (Fin n) => S.card = j)
    (f := fun S => (qV F v ^ satakeInv Finset.univ S) • ∏ a ∈ S,
      (α a * (qV F v : ℂ) ^ (-(((n : ℂ) - 1 - 2 * (a : ℂ)) / 2)))) (fun S => by
        simp [Finset.mem_powersetCard])]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hc := (Finset.mem_powersetCard.1 hS).2
  rw [nsmul_eq_mul, Nat.cast_pow, satake_exponent v α S, hc]

theorem satake_value_one [Fintype (satakeRes (Ov F v) ⟨ϖ, hϖ⟩)] (hTjCosets : TjCosets) {j : ℕ}
    (hj : j ≤ n) (α : Fin n → ℂ) (φ : GL (Fin n) (v.adicCompletion F) → ℂ)
    (hφ : IsSpherical F v α φ) :
    hAct (GLint (Fin n) (Ov F v)) (Tj ℂ n (Ov F v) ϖ j) φ 1 =
      (∑ i : SatakeIdx v hϖ (n := n) j, chiDelta F v α (satakeB v hϖ hu i)) * φ 1 := by
  classical
  unfold hAct
  have hr := satake_range_eq v hϖ hu hTjCosets hj
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun i : SatakeIdx v hϖ (n := n) j =>
      ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v)))) ?_]
  · rw [Finset.sum_image (fun i _ i' _ h => satakeB_inj v hϖ hu h), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (GLint (Fin n) (Ov F v)) (satakeB v hϖ hu i)
    have e : (Quotient.out (((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v)))) = satakeB v hϖ hu i * κ := hκ
    rw [e, satake_Tj_eq, Set.indicator_of_mem (satake_Tset_right v (satakeB_mem v hϖ hu i) κ.2),
      Pi.one_apply, one_smul, one_mul]
    have := hφ (satakeB v hϖ hu i) 1 κ (satakeB_upper v hϖ hu i) κ.2
    rwa [mul_one] at this
  · intro x hx
    rw [Function.mem_support] at hx
    have hT : Tj ℂ n (Ov F v) ϖ j x.out ≠ 0 := fun h0 => hx (by rw [h0, zero_smul])
    rw [satake_Tj_ne_zero_iff] at hT
    have hx' : x ∈ Set.range (fun i : SatakeIdx v hϖ (n := n) j =>
        ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
          GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v))) := by
      rw [hr]; exact hT
    obtain ⟨i, rfl⟩ := hx'
    simp

theorem satake_hAct_spherical (j : ℕ) (α : Fin n → ℂ)
    (φ : GL (Fin n) (v.adicCompletion F) → ℂ) (hφ : IsSpherical F v α φ) :
    IsSpherical F v α (hAct (GLint (Fin n) (Ov F v)) (Tj ℂ n (Ov F v) ϖ j) φ) := by
  intro b g k hb hk
  unfold hAct
  have step1 : ∀ x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v),
      Tj ℂ n (Ov F v) ϖ j x.out • φ (b * g * k * x.out) =
        chiDelta F v α b * (Tj ℂ n (Ov F v) ϖ j x.out • φ (g * k * x.out)) := by
    intro x
    have := hφ b (g * k * x.out) 1 hb (one_mem _)
    rw [mul_one] at this
    rw [show b * g * k * x.out = b * (g * k * x.out) by group, this, smul_eq_mul, smul_eq_mul]
    ring
  rw [finsum_congr step1, ← mul_finsum]
  congr 1
  have hF : ∀ (y : GL (Fin n) (v.adicCompletion F)) (c : GLint (Fin n) (Ov F v)),
      Tj ℂ n (Ov F v) ϖ j (k⁻¹ * (y * c)) • φ (g * (y * c)) =
        Tj ℂ n (Ov F v) ϖ j (k⁻¹ * y) • φ (g * y) := by
    intro y c
    rw [← mul_assoc, satake_T_mul_right v j _ _ c.2]
    have := hφ 1 (g * y) c (satake_upper_one v) c.2
    rw [one_mul, satake_chiDelta_one, one_mul] at this
    rw [← mul_assoc, this]
  have hr := finsum_out_mul (GLint (Fin n) (Ov F v)) k
    (fun y => Tj ℂ n (Ov F v) ϖ j (k⁻¹ * y) • φ (g * y)) hF
  simp only [inv_mul_cancel_left] at hr
  rw [show (fun x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) =>
      Tj ℂ n (Ov F v) ϖ j x.out • φ (g * k * x.out)) =
      (fun x => Tj ℂ n (Ov F v) ϖ j x.out • φ (g * (k * x.out))) by
    funext x; rw [mul_assoc]]
  rw [hr]
  refine finsum_congr fun y => ?_
  rw [satake_T_mul_left v j _ _ ((GLint (Fin n) (Ov F v)).inv_mem hk)]

end Value

theorem satake_Tj_of_spherical_cosets (hSphericalExists : Formalism.UG.SphericalExists) (hTjCosets : Formalism.UG.TjCosets) :
    Formalism.UG.SatakeTj := by
  intro F _ _ v n ϖ hϖ hu α hα φ hφ j hj
  have := satake_res_finite v hϖ hu
  let _ : Fintype (satakeRes (Ov F v) ⟨ϖ, hϖ⟩) := Fintype.ofFinite _
  obtain ⟨φ₀, -, -, huniq⟩ := hSphericalExists F v n α hα
  have hsph := satake_hAct_spherical v (ϖ := ϖ) j α φ hφ
  have h1 := satake_value_one v hϖ hu hTjCosets hj α φ hφ
  rw [satake_sum_chi v hϖ hu α j] at h1
  have e1 := huniq _ hsph
  have e2 := huniq φ hφ
  funext g
  have e1g : hAct (GLint (Fin n) (Ov F v)) (Tj ℂ n (Ov F v) ϖ j) φ g =
      hAct (GLint (Fin n) (Ov F v)) (Tj ℂ n (Ov F v) ϖ j) φ 1 * φ₀ g := congrFun e1 g
  have e2g : φ g = φ 1 * φ₀ g := congrFun e2 g
  rw [Pi.smul_apply, smul_eq_mul, e1g, h1, e2g]
  ring

end Formalism.UG.P
