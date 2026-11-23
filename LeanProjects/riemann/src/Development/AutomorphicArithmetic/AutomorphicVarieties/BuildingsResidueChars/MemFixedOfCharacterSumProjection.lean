import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

private theorem chi_orth {Q : Type} [Group Q] [Fintype Q] (f g : Q →* ℂˣ) (h : f ≠ g) :
    ∑ x, (((f x)⁻¹ : ℂˣ) : ℂ) * ((g x : ℂˣ) : ℂ) = 0 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ g y := by
    by_contra hne
    push_neg at hne
    exact h (MonoidHom.ext hne)
  have ha : ((f y)⁻¹ * g y : ℂˣ) ≠ 1 := by
    intro h1
    exact hy (inv_mul_eq_one.mp h1)
  have ha' : ((((f y)⁻¹ * g y : ℂˣ)) : ℂ) ≠ 1 := by
    intro h1
    exact ha (Units.val_eq_one.mp h1)
  have key : ∑ x, (((f x)⁻¹ : ℂˣ) : ℂ) * ((g x : ℂˣ) : ℂ)
      = ((((f y)⁻¹ * g y : ℂˣ)) : ℂ) * ∑ x, (((f x)⁻¹ : ℂˣ) : ℂ) * ((g x : ℂˣ) : ℂ) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft y)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.coe_mulLeft, map_mul, _root_.mul_inv_rev, Units.val_mul]
    ring
  have h2 : (((((f y)⁻¹ * g y : ℂˣ)) : ℂ) - 1) * ∑ x, (((f x)⁻¹ : ℂˣ) : ℂ) * ((g x : ℂˣ) : ℂ) = 0 := by
    linear_combination -key
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) ha'
  · exact h3

private theorem c_conv {Q I : Type} [Group Q] [Fintype Q] [Fintype I]
    (χ : I → Q →* ℂˣ) (hχ : Function.Injective χ) (c : Q → ℤ)
    (hc : ∀ x, (c x : ℂ) = ∑ t, (((χ t x)⁻¹ : ℂˣ) : ℂ)) (w : Q) :
    ∑ x, c x * c (x⁻¹ * w) = (Fintype.card Q : ℤ) * c w := by
  classical
  have hQ : ∀ t s : I, ∑ x, (((χ t x)⁻¹ : ℂˣ) : ℂ) * ((χ s x : ℂˣ) : ℂ)
      = if t = s then (Fintype.card Q : ℂ) else 0 := by
    intro t s
    split_ifs with hts
    · subst hts
      simp
    · exact chi_orth _ _ (fun e => hts (hχ e))
  have term : ∀ (x : Q) (t s : I), (((χ t x)⁻¹ : ℂˣ) : ℂ) * (((χ s (x⁻¹ * w))⁻¹ : ℂˣ) : ℂ)
      = (((χ s w)⁻¹ : ℂˣ) : ℂ) * ((((χ t x)⁻¹ : ℂˣ) : ℂ) * ((χ s x : ℂˣ) : ℂ)) := by
    intro x t s
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, Units.val_mul]
    ring
  apply Int.cast_injective (α := ℂ)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, hc]
  calc ∑ x, (∑ t, (((χ t x)⁻¹ : ℂˣ) : ℂ)) * ∑ s, (((χ s (x⁻¹ * w))⁻¹ : ℂˣ) : ℂ)
      = ∑ x, ∑ t, ∑ s, (((χ s w)⁻¹ : ℂˣ) : ℂ) * ((((χ t x)⁻¹ : ℂˣ) : ℂ) * ((χ s x : ℂˣ) : ℂ)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => term x t s
    _ = ∑ t, ∑ s, ∑ x, (((χ s w)⁻¹ : ℂˣ) : ℂ) * ((((χ t x)⁻¹ : ℂˣ) : ℂ) * ((χ s x : ℂˣ) : ℂ)) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun t _ => Finset.sum_comm)
    _ = ∑ t, ∑ s, (((χ s w)⁻¹ : ℂˣ) : ℂ) * (if t = s then (Fintype.card Q : ℂ) else 0) := by
        simp only [← Finset.mul_sum, hQ]
    _ = (Fintype.card Q : ℂ) * ∑ t, (((χ t w)⁻¹ : ℂˣ) : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring

private theorem opE_sum {G R W Q : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W]
    [Fintype Q] (ρ : Representation R G W) (g : Q → G) (c : Q → ℤ) :
    opE ρ (∑ x, Finsupp.single (g x) (c x)) = ∑ x, c x • ρ (g x) := by
  show (∑ x, Finsupp.single (g x) (c x)).sum (fun h n => n • ρ h) = _
  rw [← Finsupp.sum_finset_sum_index (fun a => zero_smul ℤ (ρ a)) (fun a m n => add_smul m n (ρ a))]
  exact Finset.sum_congr rfl fun x _ => Finsupp.sum_single_index (zero_smul ℤ (ρ (g x)))

theorem UpperTheory.mem_fixed_of_character_sum_projection :
    ∀ {G Q A I : Type} [Group G] [Group Q] [Fintype Q] [Group A] [Fintype I]
        (K : Subgroup G) (ι : A →* G) (π : A →* Q) (s : Q → A), (∀ x, π (s x) = x) →
        (∀ a, π a = 1 ↔ ι a ∈ K) → (∀ a, ∀ u ∈ K, (ι a)⁻¹ * u * ι a ∈ K) →
        ∀ (χ : I → Q →* ℂˣ), Function.Injective χ → ∀ (c : Q → ℤ),
        (∀ x, (c x : ℂ) = ∑ t, (((χ t x)⁻¹ : ℂˣ) : ℂ)) → ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) (v : W), v ∈ fixd ρ K →
        opE ρ (∑ x, Finsupp.single (ι (s x)) (c x)) (opE ρ (∑ x, Finsupp.single (ι (s x)) (c x)) v) =
          Fintype.card Q • opE ρ (∑ x, Finsupp.single (ι (s x)) (c x)) v := by
  intro G Q A I _ _ _ _ _ K ι π s hs hker _ χ hχ c hc R W _ _ _ ρ v hv
  have hv' : ∀ u ∈ K, ρ u v = v := hv
  have hT : ∀ y x, ρ (ι (s y)) (ρ (ι (s x)) v) = ρ (ι (s (y * x))) v := by
    intro y x
    have hk : ι ((s (y * x))⁻¹ * (s y * s x)) ∈ K := by
      rw [← hker]
      simp [map_mul, map_inv, hs]
    calc ρ (ι (s y)) (ρ (ι (s x)) v) = ρ (ι (s y * s x)) v := by
          simp only [map_mul, Module.End.mul_apply]
      _ = ρ (ι (s (y * x) * ((s (y * x))⁻¹ * (s y * s x)))) v := by rw [mul_inv_cancel_left]
      _ = ρ (ι (s (y * x))) v := by
          rw [map_mul ι, map_mul ρ, Module.End.mul_apply, hv' _ hk]
  have hE : opE ρ (∑ x, Finsupp.single (ι (s x)) (c x)) = ∑ x, c x • ρ (ι (s x)) :=
    opE_sum ρ (fun x => ι (s x)) c
  rw [hE]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul, hT]
  calc ∑ a, ∑ b, (c a * c b) • ρ (ι (s (b * a))) v
      = ∑ b, ∑ a, (c a * c b) • ρ (ι (s (b * a))) v := Finset.sum_comm
    _ = ∑ b, ∑ z, (c b * c (b⁻¹ * z)) • ρ (ι (s z)) v := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Equiv.sum_comp (Equiv.mulLeft b⁻¹)]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only [Equiv.coe_mulLeft, mul_inv_cancel_left]
        rw [mul_comm (c (b⁻¹ * z))]
    _ = ∑ z, (∑ b, c b * c (b⁻¹ * z)) • ρ (ι (s z)) v := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_smul]
    _ = ∑ z, Fintype.card Q • c z • ρ (ι (s z)) v := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [c_conv χ hχ c hc z, mul_smul, natCast_zsmul]
