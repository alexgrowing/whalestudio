import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.NormGauss

theorem exists_norm_eq {k : Type} [Field k] [Finite k] (s : k →+* k) (hs : ∀ a, s (s a) = a)
    (hne : ∃ a, s a ≠ a) (u : k) (hu : s u = u) : ∃ t, t * s t = u := by
  classical
  let F : Subfield k := RingHom.eqLocusField s (RingHom.id k)
  let σ : k ≃ₐ[F] k :=
    { toFun := s, invFun := s, left_inv := hs, right_inv := hs,
      map_mul' := map_mul s, map_add' := map_add s, commutes' := fun r => r.2 }
  have hσ_apply : ∀ x, σ x = s x := fun _ => rfl
  have hσ1 : σ ≠ 1 := by
    obtain ⟨a, ha⟩ := hne
    intro h
    apply ha
    have := AlgEquiv.ext_iff.1 h a
    rwa [hσ_apply, AlgEquiv.one_apply] at this
  have hσ2 : σ ^ 2 = 1 := by
    ext a
    rw [pow_two, AlgEquiv.mul_apply, hσ_apply, hσ_apply, hs, AlgEquiv.one_apply]
  have hfix : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
    ext x
    rw [IntermediateField.mem_fixedField_iff, IntermediateField.mem_bot]
    constructor
    · intro h
      exact ⟨⟨x, h σ (Subgroup.mem_zpowers σ)⟩, rfl⟩
    · rintro ⟨r, rfl⟩ τ _
      exact τ.commutes r
  have htop : Subgroup.zpowers σ = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ), hfix]
    ext τ
    simp only [Subgroup.mem_top, iff_true]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact τ.commutes r
  have hcard : Fintype.card (k ≃ₐ[F] k) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.card_top, ← htop, Nat.card_zpowers,
      orderOf_eq_prime hσ2 hσ1]
  have huniv : (Finset.univ : Finset (k ≃ₐ[F] k)) = {1, σ} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hσ1.symm, hcard]
  have hnorm : ∀ t : k, algebraMap F k (Algebra.norm F t) = t * s t := by
    intro t
    rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hσ1.symm]
    rfl
  obtain ⟨t, ht⟩ := FiniteField.norm_surjective F k (⟨u, hu⟩ : F)
  refine ⟨t, ?_⟩
  rw [← hnorm, ht]
  rfl

theorem sum_norm_neg {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ a, s (s a) = a)
    (hne : ∃ a, s a ≠ a) (ψ : AddChar k ℂ) (hψ : ∃ a, ψ (a + s a) ≠ 1) :
    ∃ m : ℝ, 0 < m ∧ ∑ t : k, ψ (t * s t) = -(m : ℂ) := by
  classical
  let F : Subfield k := RingHom.eqLocusField s (RingHom.id k)
  have hs0 : ∀ x : k, s x = 0 → x = 0 := by
    intro x h
    have := congrArg s h
    rwa [hs, map_zero] at this
  have hNF : ∀ t : k, t * s t ∈ F := fun t => by
    show s (t * s t) = t * s t
    rw [map_mul, hs, mul_comm]
  let N : k → F := fun t => ⟨t * s t, hNF t⟩
  have hN : ∀ t, ((N t : F) : k) = t * s t := fun _ => rfl
  let φ : AddChar F ℂ := ψ.compAddMonoidHom F.subtype.toAddMonoidHom
  have hφ_apply : ∀ u : F, φ u = ψ (u : k) := fun _ => rfl
  have hφ : φ ≠ 1 := by
    obtain ⟨a, ha⟩ := hψ
    intro h
    have hmem : a + s a ∈ F := by
      show s (a + s a) = a + s a
      rw [map_add, hs, add_comm]
    apply ha
    have := congrArg (fun χ : AddChar F ℂ => χ ⟨a + s a, hmem⟩) h
    simpa only [hφ_apply, AddChar.one_apply] using this
  have hsumφ : ∑ u : F, ψ (u : k) = 0 := by
    simpa only [hφ_apply] using AddChar.sum_eq_zero_of_ne_one hφ
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = (Finset.univ.filter (fun t : k => t * s t = 1)).card := ⟨_, rfl⟩
  have hfib : ∀ u : F,
      (Finset.univ.filter (fun t : k => N t = u)).card = if u = 0 then 1 else c := by
    intro u
    split_ifs with hu
    · subst hu
      rw [Finset.card_eq_one]
      refine ⟨0, ?_⟩
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        have h' : t * s t = 0 := congrArg Subtype.val h
        rcases mul_eq_zero.1 h' with h0 | h0
        · exact h0
        · exact hs0 t h0
      · rintro rfl
        apply Subtype.ext
        rw [hN, zero_mul]
        rfl
    · obtain ⟨t0, ht0⟩ := exists_norm_eq s hs hne (u : k) u.2
      have hu0 : (u : k) ≠ 0 := fun h => hu (Subtype.ext h)
      have ht0ne : t0 ≠ 0 := by
        rintro rfl
        apply hu0
        rw [← ht0, zero_mul]
      rw [hc]
      apply Finset.card_nbij' (fun t => t * t0⁻¹) (fun t => t * t0)
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
        have h' : t * s t = u := congrArg Subtype.val ht
        have e : t * t0⁻¹ * s (t * t0⁻¹) = (t * s t) * (t0 * s t0)⁻¹ := by
          rw [map_mul, map_inv₀, mul_inv]
          ring
        rw [e, h', ht0, mul_inv_cancel₀ hu0]
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
        apply Subtype.ext
        rw [hN]
        have e : t * t0 * s (t * t0) = (t * s t) * (t0 * s t0) := by
          rw [map_mul]
          ring
        rw [e, ht, ht0, one_mul]
      · intro t _
        exact inv_mul_cancel_right₀ ht0ne t
      · intro t _
        exact mul_inv_cancel_right₀ ht0ne t
  have hsplit : ∑ t : k, ψ (t * s t) =
      ∑ u : F, ((Finset.univ.filter (fun t : k => N t = u)).card : ℂ) * ψ (u : k) := by
    rw [← Finset.sum_fiberwise Finset.univ N (fun t => ψ (t * s t))]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => ψ (u : k)), Finset.sum_const, nsmul_eq_mul]
    intro t ht
    have := (Finset.mem_filter.1 ht).2
    rw [← this]
  have hψ0 : ψ ((0 : F) : k) = 1 := by
    rw [ZeroMemClass.coe_zero, AddChar.map_zero_eq_one]
  have key : ∀ u : F, (((if u = 0 then 1 else c : ℕ)) : ℂ) * ψ (u : k) =
      (c : ℂ) * ψ (u : k) + (if u = 0 then (1 - (c : ℂ)) else 0) := by
    intro u
    split_ifs with h
    · subst h
      rw [hψ0]
      push_cast
      ring
    · ring
  have hval : ∑ u : F, (((if u = 0 then 1 else c : ℕ)) : ℂ) * ψ (u : k) = 1 - c := by
    rw [Finset.sum_congr rfl (fun u _ => key u), Finset.sum_add_distrib, ← Finset.mul_sum, hsumφ,
      mul_zero, zero_add]
    simp
  have hc2 : 2 ≤ c := by
    obtain ⟨a, ha⟩ := hne
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha (map_zero s)
    have hsa0 : s a ≠ 0 := fun h => ha0 (hs0 a h)
    have hne1 : a * (s a)⁻¹ ≠ 1 := by
      intro h
      apply ha
      rw [mul_inv_eq_one₀ hsa0] at h
      exact h.symm
    rw [hc]
    calc 2 = ({1, a * (s a)⁻¹} : Finset k).card := (Finset.card_pair hne1.symm).symm
      _ ≤ _ := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl
        · rw [map_one, one_mul]
        · rw [map_mul, map_inv₀, hs]
          field_simp
  refine ⟨(c : ℝ) - 1, ?_, ?_⟩
  · have : (2 : ℝ) ≤ c := by exact_mod_cast hc2
    linarith
  · rw [hsplit]
    simp_rw [hfib]
    rw [hval]
    push_cast
    ring

theorem finsum_norm_neg : ∀ (R : Type) [CommRing R] (σ : R →+* R) (P : Ideal R) [P.IsMaximal] [Finite (R ⧸ P)], (∀ a, σ (σ a) = a) → (∀ a ∈ P, σ a ∈ P) → (∃ a, a - σ a ∉ P) → ∀ χ : R → ℂ, (∀ a b, χ (a + b) = χ a * χ b) → (∀ a ∈ P, χ a = 1) → (∃ a, χ (a + σ a) ≠ 1) → ∃ m : ℝ, 0 < m ∧ ∑ᶠ q : R ⧸ P, χ (Quotient.out q * σ (Quotient.out q)) = -(m : ℂ) := by
  intro R _ σ P _ _ hσ hP hne χ hχ hχP hχa
  classical
  let _ : Field (R ⧸ P) := Ideal.Quotient.field P
  let _ : Fintype (R ⧸ P) := Fintype.ofFinite _
  have hle : P ≤ P.comap σ := fun a ha => hP a ha
  let s : R ⧸ P →+* R ⧸ P := Ideal.quotientMap P σ hle
  have hs_mk : ∀ a : R, s (Ideal.Quotient.mk P a) = Ideal.Quotient.mk P (σ a) :=
    fun a => Ideal.quotientMap_mk
  have hs : ∀ x, s (s x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hs_mk, hs_mk, hσ]
  have hsne : ∃ x, s x ≠ x := by
    obtain ⟨a, ha⟩ := hne
    refine ⟨Ideal.Quotient.mk P a, ?_⟩
    rw [hs_mk]
    intro h
    apply ha
    have h' := P.neg_mem (Ideal.Quotient.eq.1 h)
    rwa [neg_sub] at h'
  have hχ_congr : ∀ x y : R, x - y ∈ P → χ x = χ y := by
    intro x y h
    have e : x = y + (x - y) := by ring
    conv_lhs => rw [e]
    rw [hχ, hχP _ h, mul_one]
  let ψ : AddChar (R ⧸ P) ℂ :=
    { toFun := fun q => χ (Quotient.out q)
      map_zero_eq_one' := by
        apply hχP
        rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out]
      map_add_eq_mul' := by
        intro q₁ q₂
        rw [← hχ]
        apply hχ_congr
        rw [← Ideal.Quotient.eq, map_add, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out,
          Ideal.Quotient.mk_out] }
  have hψ_mk : ∀ a, ψ (Ideal.Quotient.mk P a) = χ a := fun a =>
    hχ_congr _ _ (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out])
  have hψne : ∃ x, ψ (x + s x) ≠ 1 := by
    obtain ⟨a, ha⟩ := hχa
    exact ⟨Ideal.Quotient.mk P a, by rw [hs_mk, ← map_add, hψ_mk]; exact ha⟩
  obtain ⟨m, hm, hsum⟩ := sum_norm_neg s hs hsne ψ hψne
  refine ⟨m, hm, ?_⟩
  rw [finsum_eq_sum_of_fintype, ← hsum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  conv_rhs => rw [← Ideal.Quotient.mk_out q]
  rw [hs_mk, ← map_mul, hψ_mk]

end GlobalTheory.NormGauss
