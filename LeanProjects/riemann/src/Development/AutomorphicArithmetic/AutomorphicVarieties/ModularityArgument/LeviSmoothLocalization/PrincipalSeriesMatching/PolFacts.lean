import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped Classical

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem unif_spec : valuation k (unif k : k) < 1 ∧
    ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (unif k : k) := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (K := k) (uniformizer k)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact uniformizer_ne_zero (R := k) hx.symm
  have hex : ∃ p : kˣ, valuation k (p : k) < 1 ∧
      ∀ y : k, valuation k y < 1 → valuation k y ≤ valuation k (p : k) :=
    ⟨Units.mk0 x hx0, by
      simp only [Units.val_mk0, hx]
      exact ⟨uniformizer_lt_one, fun y hy => le_uniformizer_iff.2 hy⟩⟩
  exact Classical.epsilon_spec hex

private theorem val_unif : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨p, hp⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  exact le_antisymm (le_uniformizer_iff.2 unif_spec.1) (hp ▸ unif_spec.2 p (hp ▸ uniformizer_lt_one))

private theorem eq_of_unram (ξ ξ' : kˣ →* ℂˣ) (h : IsUnram (ξ * ξ'⁻¹)) (e : ξ (unif k) = ξ' (unif k)) : ξ = ξ' := by
  have h1 : IsUnram (1 : kˣ →* ℂˣ) := fun _ _ => rfl
  have a := eq_unrChar h (val_unif (k := k))
  have b := eq_unrChar h1 (val_unif (k := k))
  have c : (ξ * ξ'⁻¹) (unif k) = 1 := by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, e, mul_inv_cancel]
  rw [c] at a
  rw [MonoidHom.one_apply] at b
  rw [← b] at a
  exact mul_inv_eq_one.1 a

private noncomputable def pfac (χ : kˣ →* ℂˣ) (y : IrrGL k) : ℂ[X] :=
  if h : ∃ ξ : kˣ →* ℂˣ, (∃ hξ, y = IrrGL.ofChar ξ hξ) ∧ IsUnram (ξ * χ) then
    1 - C (((h.choose * χ) (unif k) : ℂˣ) : ℂ) * X else 1

private theorem pol_cons (y : IrrGL k) (s : Multiset (IrrGL k)) (χ : kˣ →* ℂˣ) :
    pol (y ::ₘ s) χ = pfac χ y * pol s χ := by
  simp only [pol, Multiset.map_cons, Multiset.prod_cons]
  rfl

private theorem pol_zero (χ : kˣ →* ℂˣ) : pol (0 : Multiset (IrrGL k)) χ = 1 := by
  simp [pol]

private theorem fac_pos (χ ξ : kˣ →* ℂˣ) (hξ : IsSmoothChar ξ) (hu : IsUnram (ξ * χ)) :
    pfac χ (IrrGL.ofChar ξ hξ) = 1 - C (((ξ * χ) (unif k) : ℂˣ) : ℂ) * X := by
  have h : ∃ ξ' : kˣ →* ℂˣ, (∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL k) = IrrGL.ofChar ξ' hξ') ∧ IsUnram (ξ' * χ) :=
    ⟨ξ, ⟨hξ, rfl⟩, hu⟩
  unfold pfac
  rw [dif_pos h]
  obtain ⟨h', e⟩ := h.choose_spec.1
  rw [← IrrGL.ofChar_inj.1 e]

private theorem fac_neg (χ : kˣ →* ℂˣ) (y : IrrGL k) (h : ¬ ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * χ)) :
    pfac χ y = 1 := by
  unfold pfac
  rw [dif_neg]
  rintro ⟨ξ, ⟨hξ, e⟩, hu⟩
  exact h ⟨ξ, hξ, e, hu⟩

private theorem fac_eval (χ : kˣ →* ℂˣ) (y : IrrGL k) : (pfac χ y).eval 0 = 1 := by
  unfold pfac
  split_ifs <;> simp

private theorem pol_eval (s : Multiset (IrrGL k)) (χ : kˣ →* ℂˣ) : (pol s χ).eval 0 = 1 := by
  induction s using Multiset.induction_on with
  | empty => rw [pol_zero, eval_one]
  | cons y s ih => rw [pol_cons, eval_mul, ih, fac_eval, mul_one]

private theorem natDegree_lin (a : ℂ) (ha : a ≠ 0) : (1 - C a * X : ℂ[X]).natDegree = 1 := by
  rw [natDegree_sub_eq_right_of_natDegree_lt] <;> simp [natDegree_C_mul_X _ ha]

private theorem pol_deg (s : Multiset (IrrGL k)) (χ : kˣ →* ℂˣ) : (pol s χ).natDegree = cnt s χ := by
  induction s using Multiset.induction_on with
  | empty => simp [pol_zero, cnt]
  | cons y s ih =>
    have hne : ∀ p : ℂ[X], p.eval 0 = 1 → p ≠ 0 := fun p hp h0 => by simp [h0] at hp
    rw [pol_cons, natDegree_mul (hne _ (fac_eval χ y)) (hne _ (pol_eval s χ)), ih]
    simp only [cnt, Multiset.filter_cons]
    by_cases hy : ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * χ)
    · obtain ⟨ξ, hξ, rfl, hu⟩ := hy
      rw [fac_pos χ ξ hξ hu, natDegree_lin _ (Units.ne_zero _), if_pos ⟨ξ, hξ, rfl, hu⟩,
        Multiset.card_add, Multiset.card_singleton]
    · rw [fac_neg χ y hy, if_neg hy, natDegree_one, zero_add, zero_add]

private theorem fac_root (χ : kˣ →* ℂˣ) (y : IrrGL k) (x : ℂ) : (pfac χ y).eval x = 0 ↔
    ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * χ) ∧ (((ξ * χ) (unif k) : ℂˣ) : ℂ) * x = 1 := by
  by_cases hy : ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * χ)
  · obtain ⟨ξ, hξ, rfl, hu⟩ := hy
    rw [fac_pos χ ξ hξ hu]
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, sub_eq_zero]
    constructor
    · intro h
      exact ⟨ξ, hξ, rfl, hu, h.symm⟩
    · rintro ⟨ξ', hξ', e, _, h⟩
      have hq := IrrGL.ofChar_inj.1 e
      subst hq
      exact h.symm
  · rw [fac_neg χ y hy]
    simp only [eval_one, one_ne_zero, false_iff]
    rintro ⟨ξ, hξ, e, hu, _⟩
    exact hy ⟨ξ, hξ, e, hu⟩

private theorem pol_root (s : Multiset (IrrGL k)) (χ : kˣ →* ℂˣ) (x : ℂ) : (pol s χ).eval x = 0 ↔
    ∃ ξ ∈ chars s, IsUnram (ξ * χ) ∧ (((ξ * χ) (unif k) : ℂˣ) : ℂ) * x = 1 := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [pol_zero, eval_one, one_ne_zero, false_iff]
    rintro ⟨ξ, ⟨hξ, hm⟩, _⟩
    simp at hm
  | cons y s ih =>
    rw [pol_cons, eval_mul, mul_eq_zero, fac_root, ih]
    constructor
    · rintro (⟨ξ, hξ, rfl, hu, h⟩ | ⟨ξ, ⟨hξ, hm⟩, hu, h⟩)
      · exact ⟨ξ, ⟨hξ, Multiset.mem_cons.2 (Or.inl rfl)⟩, hu, h⟩
      · exact ⟨ξ, ⟨hξ, Multiset.mem_cons.2 (Or.inr hm)⟩, hu, h⟩
    · rintro ⟨ξ, ⟨hξ, hm⟩, hu, h⟩
      rcases Multiset.mem_cons.1 hm with e | hm
      · exact Or.inl ⟨ξ, hξ, e.symm, hu, h⟩
      · exact Or.inr ⟨ξ, ⟨hξ, hm⟩, hu, h⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unram_mul_iff (a μ : kˣ →* ℂˣ) (hμ : IsUnram μ) : IsUnram (a * μ) ↔ IsUnram a := by
  constructor
  · intro h x hx
    have h2 := h x hx
    rwa [MonoidHom.mul_apply, hμ x hx, mul_one] at h2
  · intro h x hx
    rw [MonoidHom.mul_apply, h x hx, hμ x hx, mul_one]

private theorem fac_comp (χ μ : kˣ →* ℂˣ) (hμ : IsUnram μ) (y : IrrGL k) :
    pfac (χ * μ) y = (pfac χ y).comp (C ((μ (unif k) : ℂˣ) : ℂ) * X) := by
  by_cases hy : ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * χ)
  · obtain ⟨ξ, hξ, rfl, hu⟩ := hy
    have hu' : IsUnram (ξ * (χ * μ)) := by
      rw [← mul_assoc ξ χ μ, unram_mul_iff _ _ hμ]
      exact hu
    rw [fac_pos _ ξ hξ hu', fac_pos _ ξ hξ hu, ← mul_assoc ξ χ μ, MonoidHom.mul_apply (ξ * χ) μ,
      Units.val_mul, C_mul, sub_comp, one_comp, mul_comp, C_comp, X_comp, mul_assoc]
  · have hy' : ¬ ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * (χ * μ)) := by
      rintro ⟨ξ, hξ, e, hu⟩
      rw [← mul_assoc ξ χ μ, unram_mul_iff _ _ hμ] at hu
      exact hy ⟨ξ, hξ, e, hu⟩
    rw [fac_neg _ _ hy', fac_neg _ _ hy, one_comp]

private theorem pol_comp (s : Multiset (IrrGL k)) (χ μ : kˣ →* ℂˣ) (hμ : IsUnram μ) :
    pol s (χ * μ) = (pol s χ).comp (C ((μ (unif k) : ℂˣ) : ℂ) * X) := by
  induction s using Multiset.induction_on with
  | empty => rw [pol_zero, pol_zero, one_comp]
  | cons y s ih => rw [pol_cons, pol_cons, mul_comp, ih, fac_comp χ μ hμ]

end Loc

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.polFacts :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.PolFacts := fun _ _ _ _ _ =>
  ⟨unif_spec, eq_of_unram, fun _ _ _ _ => IrrGL.ofChar_inj.1, fun s χ =>
    ⟨pol_eval s χ, pol_deg s χ, pol_root s χ, pol_comp s χ⟩⟩
