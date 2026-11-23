import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.smooth_vector_fixed_by_open_subgroup :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ χ : F.Γ →* kˣ, χ F.c = -1 → (∀ v, ∃ s, χ (F.loc v s) ≠ 1) → Nontrivial (H1C F.loc (chRep χ) fun _ => ⊥) → ∃ x : F.Γ → k, IsLocallyConstant x ∧ (∀ g h, x (g * h) = x g + χ g * x h) ∧ x F.c = 0 ∧ (∀ v, ∃ Y : k, ∀ s, x (F.loc v s) = χ (F.loc v s) * Y - Y) ∧ ∃ g : F.G0, x g ≠ 0 := by
  intro l _ k _ _ F C₀ hok χ hc hloc hnt
  obtain ⟨q, hq⟩ := exists_ne (0 : H1C F.loc (chRep χ) fun _ => ⊥)
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Ne, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hq
  obtain ⟨⟨x, y⟩, hz⟩ := z
  obtain ⟨hlc, hcoc, hlocz⟩ := hz
  simp only [chRep_apply] at hcoc
  simp only [chRep_apply, Submodule.mem_bot] at hlocz
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k l] at h'
    exact hok.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h')
  have hx1 : x 1 = 0 := by
    have e := hcoc 1 1
    rw [mul_one, map_one, Units.val_one, one_mul] at e
    linear_combination -e
  have hχ : ∀ s, (χ s : k) * x F.c = x (s * F.c) - x s := by
    intro s
    rw [hcoc]
    ring
  set X : k := -(x F.c) / 2 with hX
  set x' : F.Γ → k := fun s => x s - ((χ s : k) * X - X) with hx'
  have hform : x' = fun s => (x s + x (s * F.c) - x F.c) / 2 := by
    funext s
    simp only [hx', hX]
    rw [show x (s * F.c) = (χ s : k) * x F.c + x s by rw [hχ]; ring]
    field_simp
    ring
  have hcoc' : ∀ g h, x' (g * h) = x' g + (χ g : k) * x' h := by
    intro g h
    simp only [hx']
    rw [hcoc, map_mul, Units.val_mul]
    ring
  have hc' : x' F.c = 0 := by
    rw [hform]
    simp only
    rw [hok.c_sq, hx1]
    ring
  have hloc' : ∀ v s, x' (F.loc v s) = (χ (F.loc v s) : k) * (y v - X) - (y v - X) := by
    intro v s
    simp only [hx']
    have e := hlocz v s
    linear_combination e
  refine ⟨x', ?_, hcoc', hc', fun v => ⟨y v - X, hloc' v⟩, ?_⟩
  · rw [hform]
    exact IsLocallyConstant.comp₂ hlc (hlc.comp_continuous (continuous_mul_right F.c))
      (fun a b => (a + b - x F.c) / 2)
  · by_contra hall
    push_neg at hall
    have hzero : ∀ γ, x' γ = 0 := by
      intro γ
      rcases Int.units_eq_one_or (F.del γ) with hd | hd
      · exact hall ⟨γ, hd⟩
      · have hm : γ * F.c ∈ F.del.ker := by
          rw [MonoidHom.mem_ker, map_mul, hd, hok.del_c]
          rfl
        have e : γ = (γ * F.c) * F.c := by
          rw [mul_assoc, hok.c_sq, mul_one]
        rw [e, hcoc', hc', mul_zero, add_zero]
        exact hall ⟨_, hm⟩
    have hy : ∀ v, y v - X = 0 := by
      intro v
      obtain ⟨s, hs⟩ := hloc v
      have e := hloc' v s
      rw [hzero] at e
      have e' : ((χ (F.loc v s) : k) - 1) * (y v - X) = 0 := by
        linear_combination -e
      rcases mul_eq_zero.1 e' with h | h
      · exact absurd (by
          have : (χ (F.loc v s) : k) = 1 := sub_eq_zero.1 h
          exact Units.val_eq_one.1 this) hs
      · exact h
    apply hq
    refine ⟨X, fun s => ?_, fun v => ?_⟩
    · have e := hzero s
      simp only [hx'] at e
      show x s = (chRep χ s) X - X
      rw [chRep_apply]
      linear_combination e
    · show y v - X ∈ (⊥ : Submodule k k)
      rw [Submodule.mem_bot]
      exact hy v
