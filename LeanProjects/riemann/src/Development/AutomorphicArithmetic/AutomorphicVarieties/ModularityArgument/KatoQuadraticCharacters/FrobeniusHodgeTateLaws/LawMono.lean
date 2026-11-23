import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob

open UpperTheory.V.Z.Kato.Joint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

private theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℕ) : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem cg_scale {l : ℕ} [Fact l.Prime] (K : Qbar l) : ∃ N : ℕ, ∀ m, N ≤ m → ∀ (c₀ : ℕ) (u x y : Qbar l),
    ‖u‖ = 1 → Cg (2 * m) x y → Cg (m - c₀) (u * K * y) (u * K * x) := by
  have hl0 : 0 ≤ ‖((l : ℕ) : Qbar l)‖ := norm_nonneg _
  have hl1 := norm_l_lt_one l
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖((l : ℕ) : Qbar l)‖ ^ N * ‖K‖ ≤ 1 := by
    rcases eq_or_ne ‖K‖ 0 with hK | hK
    · exact ⟨0, by rw [hK, mul_zero]; exact zero_le_one⟩
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (lt_of_le_of_ne (norm_nonneg K) (Ne.symm hK))) hl1
      refine ⟨N, ?_⟩
      have hKpos : 0 < ‖K‖ := lt_of_le_of_ne (norm_nonneg K) (Ne.symm hK)
      calc ‖((l : ℕ) : Qbar l)‖ ^ N * ‖K‖ ≤ ‖K‖⁻¹ * ‖K‖ :=
            mul_le_mul_of_nonneg_right hN.le hKpos.le
        _ = 1 := inv_mul_cancel₀ hK
  refine ⟨N, fun m hm c₀ u x y hu hxy => ?_⟩
  unfold Cg at hxy ⊢
  rw [norm_pow] at hxy ⊢
  have hdiff : u * K * y - u * K * x = -(u * K * (x - y)) := by ring
  rw [hdiff, norm_neg, norm_mul, norm_mul, hu, one_mul]
  have hmN : ‖((l : ℕ) : Qbar l)‖ ^ m ≤ ‖((l : ℕ) : Qbar l)‖ ^ N := pow_le_pow_of_le_one hl0 hl1.le hm
  have hmc : ‖((l : ℕ) : Qbar l)‖ ^ m ≤ ‖((l : ℕ) : Qbar l)‖ ^ (m - c₀) :=
    pow_le_pow_of_le_one hl0 hl1.le (Nat.sub_le m c₀)
  have hKm : ‖((l : ℕ) : Qbar l)‖ ^ m * ‖K‖ ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right hmN (norm_nonneg K)) hN
  calc ‖K‖ * ‖x - y‖ ≤ ‖K‖ * ‖((l : ℕ) : Qbar l)‖ ^ (2 * m) :=
        mul_le_mul_of_nonneg_left hxy (norm_nonneg K)
    _ = (‖((l : ℕ) : Qbar l)‖ ^ m * ‖K‖) * ‖((l : ℕ) : Qbar l)‖ ^ m := by ring
    _ ≤ 1 * ‖((l : ℕ) : Qbar l)‖ ^ m :=
        mul_le_mul_of_nonneg_right hKm (pow_nonneg hl0 m)
    _ ≤ ‖((l : ℕ) : Qbar l)‖ ^ (m - c₀) := by rw [one_mul]; exact hmc

private theorem law_mono {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {c : Coef l}
    {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} {j : Ω →+* Qbar l} {m₀ m₁ c₀ : ℕ}
    {R : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l} (hm : m₀ ≤ m₁) (h : HTLawCsOfCoef A c Z j m₀ c₀ R) :
    HTLawCsOfCoef A c Z j m₁ c₀ R := by
  obtain ⟨ζ, hζ, hlaw⟩ := h
  exact ⟨ζ, hζ, fun m hm' => hlaw m (hm.trans hm')⟩

open Classical in
private theorem cg_cases {l : ℕ} [Fact l.Prime] {κ₀ κ : Qbar l} (hκ : κ ≠ 0) : ∃ N : ℕ, ∀ m, N ≤ m →
    ∀ (c₀ : ℕ) (v a p s X b g w : Qbar l), ‖v‖ = 1 → ‖a‖ = 1 → p ^ 2 = 1 → s ^ 2 = 1 →
    (p = s → Cg (2 * m) X (κ * b * g * w)) → (p = -s → Cg (2 * m) X 0) →
    Cg (m - c₀) (if p = s then v * κ₀ * a ^ m * (b * g * w) else 0) (v * (κ₀ / κ) * a ^ m * X) := by
  obtain ⟨N, hN⟩ := cg_scale (κ₀ / κ)
  refine ⟨N, fun m hm c₀ v a p s X b g w hv ha hp hs h1 h2 => ?_⟩
  have hu : ‖v * a ^ m‖ = 1 := by rw [norm_mul, norm_pow, hv, ha, one_pow, one_mul]
  by_cases hE : p = s
  · rw [if_pos hE]
    have h3 := hN m hm c₀ (v * a ^ m) X (κ * b * g * w) hu (h1 hE)
    have e1 : v * a ^ m * (κ₀ / κ) * (κ * b * g * w) = v * κ₀ * a ^ m * (b * g * w) := by
      field_simp
    have e2 : v * a ^ m * (κ₀ / κ) * X = v * (κ₀ / κ) * a ^ m * X := by ring
    rw [e1, e2] at h3
    exact h3
  · have hps : p ^ 2 = s ^ 2 := by rw [hp, hs]
    have hO : p = -s := (sq_eq_sq_iff_eq_or_eq_neg.1 hps).resolve_left hE
    rw [if_neg hE]
    have h3 := hN m hm c₀ (v * a ^ m) X 0 hu (h2 hO)
    have e2 : v * a ^ m * (κ₀ / κ) * X = v * (κ₀ / κ) * a ^ m * X := by ring
    rw [mul_zero, e2] at h3
    exact h3

theorem UpperTheory.V.Z.Kato.Joint.pinOf :
    UpperTheory.V.Z.Kato.Joint.PinOf := by
  intro hM hU hMo l _ Ω _ _ ι e A W c ν Z j u w ψ α B cc v n β t hl he hα hj hν hσ hμ hv ht hne hE
  obtain ⟨cO, L, κ, φ, n₀, r₁, hκ, hL, hφ, h1, h2, h3⟩ :=
    hM l ι e _ u w ψ α B cc v n β t hl he rfl hμ hv ht hne
  obtain ⟨c', hc, hcO, -⟩ := hU l c cO ∅ (fun x hx => absurd hx (Finset.notMem_empty x))
  obtain ⟨κ₀, vv, m₀, c₀, hκ₀, hvv, hH⟩ := hE
  obtain ⟨σ, hσ1, hσ2, hσ3⟩ := hσ
  obtain ⟨N, hN⟩ := cg_cases (κ₀ := κ₀) hκ
  have hH' := law_mono (le_max_left m₀ (max N 1)) ((hMo l Ω c c' hc).2.2 A Z j m₀ c₀ _ hH)
  refine ⟨c', hc, ?_⟩
  unfold Pin7
  refine ⟨ν σ, ι.symm α, κ₀ / κ, vv, j, _, L, φ, max m₀ (max N 1), c₀, n₀, hν, ⟨σ, hσ1, hσ2, rfl⟩, hσ3, hα, hvv,
    div_ne_zero hκ₀ hκ, hj, fun k => hcO (hL k), hH', ?_, ?_, r₁, h3⟩
  · intro m hm ψ' _ z hz
    have hm1 : 1 ≤ m := by omega
    have hmN : N ≤ m := by omega
    have ha : ψ' (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
    have hb : (ι.symm ((-1) ^ e * ψ (-1))) ^ 2 = 1 := by
      rw [← map_pow, mul_pow, ← map_pow, ← pow_mul, mul_comm e 2, pow_mul, neg_one_sq, neg_one_sq, one_pow, map_one,
        one_mul, map_one]
    exact hN m hmN c₀ _ _ _ _ _ _ _ _ (hvv m).1 hα ha hb (fun hs => h1 m hm1 ψ' hs z hz) (fun hs => h2 m hm1 ψ' hs z hz)
  · intro r _ x
    apply ι.injective
    rw [map_inv₀, hφ, MulChar.inv_apply_eq_inv', inv_inv]
    exact ι.apply_symm_apply _
