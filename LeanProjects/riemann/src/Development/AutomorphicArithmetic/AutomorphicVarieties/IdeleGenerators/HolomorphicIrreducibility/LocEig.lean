import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UopSum
import GroundTheory.GlobalFields.LocalAtPlace

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual
open scoped Matrix

namespace UpperTheory.V.Sd

private def low {R : Type} [CommRing R] (x : R) : GL (Fin 2) R where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

private def sw (R : Type) [CommRing R] : GL (Fin 2) R where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

private theorem low_val {R : Type} [CommRing R] (x : R) : (low x : Matrix (Fin 2) (Fin 2) R) = !![1, 0; x, 1] := rfl
private theorem sw_val {R : Type} [CommRing R] : (sw R : Matrix (Fin 2) (Fin 2) R) = !![0, 1; 1, 0] := rfl
private theorem aff_val {R : Type} [CommRing R] (y : Rˣ) (x : R) :
    (aff y x : Matrix (Fin 2) (Fin 2) R) = !![(y : R), x; 0, 1] := rfl

private theorem bor_val {K : Type} [Field K] (a d : Kˣ) (x : K) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(a : K), d * x; 0, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.scalar, aff_val, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply, mul_div_cancel₀]

private theorem dec1 {K : Type} [Field K] (g : GL (Fin 2) K) (h : g 1 1 ≠ 0) :
    ∃ (a d : Kˣ) (x : K), g = Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x * low (g 1 0 / g 1 1) := by
  have hd : (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := g.det_ne_zero
  rw [Matrix.det_fin_two] at hd
  obtain ⟨a, ha⟩ : ∃ a : Kˣ, (a : K) = (g 0 0 * g 1 1 - g 0 1 * g 1 0) / g 1 1 := ⟨Units.mk0 _ (div_ne_zero hd h), rfl⟩
  obtain ⟨d, hd'⟩ : ∃ a : Kˣ, (a : K) = g 1 1 := ⟨Units.mk0 _ h, rfl⟩
  refine ⟨a, d, g 0 1 / g 1 1, Units.ext ?_⟩
  rw [Units.val_mul, bor_val, low_val, Matrix.mul_fin_two, ha, hd']
  generalize (g : Matrix (Fin 2) (Fin 2) K) = M at h ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> (try field_simp) <;> (try ring)

private theorem dec2 {K : Type} [Field K] (g : GL (Fin 2) K) (h : g 1 0 ≠ 0) :
    ∃ (a d : Kˣ) (x : K), g = Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x * (sw K * aff 1 (g 1 1 / g 1 0)) := by
  have hd : (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := g.det_ne_zero
  rw [Matrix.det_fin_two] at hd
  obtain ⟨a, ha⟩ : ∃ a : Kˣ, (a : K) = -(g 0 0 * g 1 1 - g 0 1 * g 1 0) / g 1 0 := ⟨Units.mk0 _ (div_ne_zero (neg_ne_zero.2 hd) h), rfl⟩
  obtain ⟨d, hd'⟩ : ∃ a : Kˣ, (a : K) = g 1 0 := ⟨Units.mk0 _ h, rfl⟩
  refine ⟨a, d, g 0 0 / g 1 0, Units.ext ?_⟩
  rw [Units.val_mul, bor_val, Units.val_mul, sw_val, aff_val, Matrix.mul_fin_two, Matrix.mul_fin_two, ha, hd']
  generalize (g : Matrix (Fin 2) (Fin 2) K) = M at h ⊢
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> (try field_simp) <;> (try ring)

private theorem core {K : Type} [Field K] (A : ValuationSubring K) (p : Kˣ) (π : A) (hp : (π : K) = p)
    (hm : ∀ x : A, ¬ IsUnit x ↔ π ∣ x) (μ₁ μ₂ : Kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (Φ : GL (Fin 2) K → V) (hΦ : Φ ≠ 0)
    (hB : ∀ (a d : Kˣ) (x : K) g,
      Φ (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x * g) = ((μ₁ a * μ₂ d : ℂˣ) : ℂ) • Φ g)
    (c : ℕ) (lam : ℂ)
    (hlow : ∀ x : A, π ^ c ∣ x → ∀ g, Φ (g * low (x : K)) = Φ g)
    (haff : ∀ (a : Aˣ) (y : A) g, Φ (g * aff (Units.map A.subtype.toMonoidHom a) (y : K)) = Φ g)
    (hsw : c = 0 → ∀ g, Φ (g * sw K) = Φ g)
    (S : Finset A) (hS : Set.BijOn (IsLocalRing.residue _) (S : Set A) Set.univ)
    (hU : ∀ g, ∑ u ∈ S, Φ (g * aff p (u : K)) +
      (if c = 0 then Φ (g * (Matrix.GeneralLinearGroup.scalar (Fin 2) p * (aff p 0)⁻¹)) else 0) = lam • Φ g) :
    (c = 0 → (∀ x : Aˣ, μ₁ (Units.map A.subtype.toMonoidHom x) = 1 ∧ μ₂ (Units.map A.subtype.toMonoidHom x) = 1) ∧
      lam = (S.card : ℂ) * (μ₁ p : ℂ) + (μ₂ p : ℂ)) ∧
    (c ≠ 0 → lam = 0 ∨ ((∀ x : Aˣ, μ₁ (Units.map A.subtype.toMonoidHom x) = 1) ∧ lam = (S.card : ℂ) * (μ₁ p : ℂ)) ∨
      ((∀ x : Aˣ, μ₂ (Units.map A.subtype.toMonoidHom x) = 1) ∧ lam = (μ₂ p : ℂ))) := by
  classical
  have hπ : ¬ IsUnit π := (hm π).2 dvd_rfl
  have haff1 : ∀ (y : A) g, Φ (g * aff 1 (y : K)) = Φ g := fun y g => by simpa using haff 1 y g
  have hA : ∀ (a : Kˣ) (x : K), Φ (aff a x) = (μ₁ a : ℂ) • Φ 1 := fun a x => by simpa using hB a 1 x 1
  have hD : ∀ (d : Kˣ) g, Φ (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (1 / d) 0 * g) = (μ₂ d : ℂ) • Φ g :=
    fun d g => by simpa using hB 1 d 0 g
  have canc : ∀ {s t : ℂ} {v : V}, v ≠ 0 → s • v = t • v → s = t := fun hv h => smul_left_injective ℂ hv h
  have u1 : Φ 1 ≠ 0 → ∀ x : Aˣ, μ₁ (Units.map A.subtype.toMonoidHom x) = 1 := fun h x => by
    have := haff x 0 1
    rw [one_mul, hA] at this
    exact Units.ext (canc h (this.trans (one_smul _ _).symm))
  have u2 : Φ (sw K) ≠ 0 → ∀ x : Aˣ, μ₂ (Units.map A.subtype.toMonoidHom x) = 1 := fun h x => by
    have := haff x 0 (sw K)
    have e : ∀ d : Kˣ, sw K * aff d ((0 : A) : K) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (1 / d) 0 * sw K := fun d => by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul _ (sw K), bor_val, sw_val, aff_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
    rw [e, hD] at this
    exact Units.ext (canc h (this.trans (one_smul _ _).symm))
  have sum1 : ∑ u ∈ S, Φ (1 * aff p (u : K)) = ((S.card : ℂ) * (μ₁ p : ℂ)) • Φ 1 := by
    simp only [one_mul, hA, Finset.sum_const]
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
  have z1 : ∀ (g : GL (Fin 2) K) (x : A), g 1 1 ≠ 0 → g 1 0 = x * g 1 1 → Φ (low (x : K)) = 0 → Φ g = 0 := by
    intro g x h1 h2 h3
    obtain ⟨a, d, y, e⟩ := dec1 g h1
    rw [h2, mul_div_cancel_right₀ _ h1] at e
    rw [e, hB, h3, smul_zero]
  have iw : (∀ x : A, π ∣ x → Φ (low (x : K)) = 0) → Φ (sw K) ≠ 0 := by
    intro h hs
    apply hΦ
    funext g
    have z2 : ∀ y : A, g 1 0 ≠ 0 → g 1 1 = y * g 1 0 → Φ g = 0 := by
      intro y h1 h2
      obtain ⟨a, d, x, e⟩ := dec2 g h1
      rw [h2, mul_div_cancel_right₀ _ h1] at e
      rw [e, hB, haff1, hs, smul_zero]
    by_cases h0 : g 1 0 = 0
    · have h1 : g 1 1 ≠ 0 := fun h1 => g.det_ne_zero (by rw [Matrix.det_fin_two, h0, h1]; ring)
      exact z1 g 0 h1 (by simp [h0]) (h 0 (dvd_zero _))
    by_cases hy : g 1 1 / g 1 0 ∈ A
    · exact z2 ⟨_, hy⟩ h0 (div_mul_cancel₀ _ h0).symm
    · have h1 : g 1 1 ≠ 0 := fun h1 => hy (by rw [h1, zero_div]; exact A.zero_mem)
      have hx : g 1 0 / g 1 1 ∈ A := by
        have := (A.mem_or_inv_mem (g 1 1 / g 1 0)).resolve_left hy
        rwa [inv_div] at this
      refine z1 g ⟨_, hx⟩ h1 (div_mul_cancel₀ _ h1).symm (h _ ((hm _).1 ?_))
      intro hu
      obtain ⟨y, hy'⟩ := hu.exists_right_inv
      have hy2 : g 1 0 / g 1 1 * (y : K) = 1 := congrArg Subtype.val hy'
      apply hy
      have : g 1 1 / g 1 0 = y := by
        rw [← inv_div]; exact inv_eq_of_mul_eq_one_right hy2
      rw [this]; exact y.2
  constructor
  · intro hc
    have hs : Φ (sw K) = Φ 1 := by simpa using hsw hc 1
    have h1 : Φ 1 ≠ 0 := fun h1 => iw (fun x _ => by
      have := hlow x (by simp [hc]) 1
      rwa [one_mul, h1] at this) (hs.trans h1)
    refine ⟨fun x => ⟨u1 h1 x, u2 (hs ▸ h1) x⟩, ?_⟩
    have := hU 1
    have e : (1 : GL (Fin 2) K) * (Matrix.GeneralLinearGroup.scalar (Fin 2) p * (aff p 0)⁻¹) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) p * aff (1 / p) 0 * 1 := by
      rw [one_mul, mul_one]
      congr 1
      rw [inv_eq_iff_mul_eq_one]
      apply Units.ext
      rw [Units.val_mul, aff_val, aff_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
    rw [if_pos hc, sum1, e, hD, ← add_smul] at this
    exact (canc h1 this).symm
  · intro hc
    simp only [if_neg hc, add_zero] at hU
    by_cases hl : lam = 0
    · exact Or.inl hl
    right
    by_cases h1 : Φ 1 = 0
    swap
    · left
      refine ⟨u1 h1, ?_⟩
      have := hU 1
      rw [sum1] at this
      exact (canc h1 this).symm
    right
    have step : ∀ j : ℕ, (∀ x : A, π ^ (j + 2) ∣ x → Φ (low (x : K)) = 0) →
        ∀ x : A, π ^ (j + 1) ∣ x → Φ (low (x : K)) = 0 := by
      intro j ih x hx
      have := hU (low (x : K))
      rw [Finset.sum_eq_zero] at this
      · exact (smul_eq_zero.1 this.symm).resolve_left hl
      intro u _
      have hxu : ¬ IsUnit (x * u) := (hm _).2 (((dvd_pow_self π (Nat.succ_ne_zero j)).trans hx).mul_right u)
      have hu : IsUnit (x * u + 1) := by
        have := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(x * u))
        rw [IsUnit.neg_iff] at this
        have := this.resolve_left hxu
        rwa [sub_neg_eq_add, add_comm] at this
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      have hy2 : ((x : K) * u + 1) * y = 1 := congrArg Subtype.val hy
      have e11 : (low (x : K) * aff p (u : K)) 1 1 = x * u + 1 := by
        rw [Units.val_mul, low_val, aff_val]; simp [Matrix.mul_apply, Fin.sum_univ_succ]
      have e10 : (low (x : K) * aff p (u : K)) 1 0 = x * π := by
        rw [Units.val_mul, low_val, aff_val, hp]; simp [Matrix.mul_apply, Fin.sum_univ_succ]
      refine z1 _ (x * π * y) ?_ ?_ (ih _ ?_)
      · rw [e11]; exact left_ne_zero_of_mul_eq_one hy2
      · rw [e11, e10]; push_cast; linear_combination (-(x : K) * π) * hy2
      · rw [pow_succ π (j + 1)]
        exact (mul_dvd_mul hx dvd_rfl).mul_right y
    have down : ∀ j : ℕ, (∀ x : A, π ^ (j + 1) ∣ x → Φ (low (x : K)) = 0) →
        ∀ x : A, π ∣ x → Φ (low (x : K)) = 0 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => exact fun h => ih (step j h)
    have hz : ∀ x : A, π ∣ x → Φ (low (x : K)) = 0 := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc
      refine down j fun x hx => ?_
      have := hlow x hx 1
      rwa [one_mul, h1] at this
    have hs := iw hz
    refine ⟨u2 hs, ?_⟩
    obtain ⟨u₀, hu₀, hr⟩ := hS.surjOn (Set.mem_univ 0)
    have hnu : ∀ u : A, IsLocalRing.residue A u = 0 ↔ ¬ IsUnit u := fun u => by
      rw [IsLocalRing.residue_eq_zero_iff]; rfl
    have := hU (sw K)
    rw [Finset.sum_eq_single u₀] at this
    · obtain ⟨y, hy⟩ := (hm _).1 ((hnu _).1 hr)
      have e : sw K * aff p (u₀ : K) =
          Matrix.GeneralLinearGroup.scalar (Fin 2) p * aff (1 / p) 0 * (sw K * aff 1 (y : K)) := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul _ (sw K * _), bor_val, Units.val_mul, sw_val, aff_val, aff_val, hy]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, hp]
      rw [e, hD, haff1] at this
      exact (canc hs this).symm
    · intro u hu hne
      have hun : IsUnit u := by
        by_contra hn
        exact hne (hS.injOn hu hu₀ (((hnu u).2 hn).trans hr.symm))
      obtain ⟨y, hy⟩ := hun.exists_right_inv
      have hy2 : (u : K) * y = 1 := congrArg Subtype.val hy
      have e11 : (sw K * aff p (u : K)) 1 1 = u := by
        rw [Units.val_mul, sw_val, aff_val]; simp [Matrix.mul_apply, Fin.sum_univ_succ]
      have e10 : (sw K * aff p (u : K)) 1 0 = π := by
        rw [Units.val_mul, sw_val, aff_val, hp]; simp [Matrix.mul_apply, Fin.sum_univ_succ]
      refine z1 _ (π * y) ?_ ?_ (hz _ (dvd_mul_right _ _))
      · rw [e11]; exact left_ne_zero_of_mul_eq_one hy2
      · rw [e11, e10]; push_cast; linear_combination (-(π : K)) * hy2
    · exact fun h => absurd hu₀ h

private theorem mem_parahoricTimesPrincipalCongruence_iff {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (c : ℕ)
    (k : GL (Fin 2) (w.adicCompletionIntegers F))
    (h0 : k 1 0 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)
    (h1 : k 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)
    (g : GL (Fin 2) (w.adicCompletion F)) (hg : ∀ i j, g i j = (k i j : w.adicCompletion F)) : g ∈ K1 w c := by
  refine ⟨k, ?_, ?_⟩
  · change ![0, 1] ᵥ* _ = ![0, 1]
    ext j
    fin_cases j
    · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Ideal.Quotient.eq_zero_iff_mem] using h0
    · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using Ideal.Quotient.eq.2 h1
  · ext i j
    rw [hg]
    rfl

theorem locEig : UpperTheory.V.Sd.LocEig := by
  intro F _ _ w μ₁ μ₂ V _ _ Φ hΦ hB c lam hfix hU
  classical
  have hp : Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  let π : w.adicCompletionIntegers F := ⟨(atFin w (unif w) : (w.adicCompletion F)ˣ), by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hp]; exact hlt.le⟩
  have hm : ∀ x : w.adicCompletionIntegers F, ¬ IsUnit x ↔ π ∣ x := by
    intro x
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    constructor
    · intro h
      have h1 : Valued.v (x : w.adicCompletion F) < 1 := lt_of_le_of_ne x.2 h
      have h2 : Valued.v (x : w.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) := by
        by_cases hx : Valued.v (x : w.adicCompletion F) = 0
        · rw [hx]; exact zero_le
        · rw [← WithZero.exp_log hx] at h1 ⊢
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
          rw [WithZero.exp_le_exp]; omega
      refine ⟨⟨(x : w.adicCompletion F) / (π : w.adicCompletion F), ?_⟩, ?_⟩
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
        change _ / Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) ≤ 1
        rw [hp]
        exact div_le_one_of_le₀ h2 zero_le
      · apply Subtype.ext
        change (x : w.adicCompletion F) = (π : w.adicCompletion F) * (x / (π : w.adicCompletion F))
        rw [mul_div_cancel₀]
        exact (atFin w (unif w)).ne_zero
    · rintro ⟨y, rfl⟩
      apply ne_of_lt
      change Valued.v (((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) * y) < 1
      rw [map_mul, hp]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' y.2) hlt
  have hπ : π ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) := (hm π).2 dvd_rfl
  have hf : ∀ k ∈ K1 w c, ∀ g, Φ (g * k) = Φ g := fun k hk g => congrFun (hfix k hk) g
  obtain ⟨σ, hσ⟩ := (IsLocalRing.residue_surjective (R := w.adicCompletionIntegers F)).hasRightInverse
  have := Fintype.ofFinite (IsLocalRing.ResidueField (w.adicCompletionIntegers F))
  have hS : Set.BijOn (IsLocalRing.residue _) ((Finset.univ.image σ : Finset _) : Set (w.adicCompletionIntegers F)) Set.univ := by
    refine ⟨fun _ _ => trivial, ?_, fun y _ => ⟨σ y, by simp, hσ y⟩⟩
    intro a ha b hb h
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at ha hb
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    rw [hσ, hσ] at h
    rw [h]
  have hcard : (Finset.univ.image σ).card = normV w := by
    rw [Finset.card_image_of_injective _ hσ.injective, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact (Nat.card_congr (GroundTheory.Global.residueFieldEquiv w).toEquiv).symm
  have hun : ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x → ∃ y : (w.adicCompletionIntegers F)ˣ,
      x = Units.map (w.adicCompletionIntegers F).subtype.toMonoidHom y := by
    intro x hx
    have : IsUnit (⟨(x : w.adicCompletion F), le_of_eq hx⟩ : w.adicCompletionIntegers F) :=
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx
    exact ⟨this.unit, Units.ext rfl⟩
  have key := core (w.adicCompletionIntegers F) (atFin w (unif w)) π rfl hm μ₁ μ₂ Φ hΦ hB c lam
    (fun x hx => hf _ (mem_parahoricTimesPrincipalCongruence_iff w c (low x) (by
        obtain ⟨y, rfl⟩ := hx
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπ c)) (by simp [low_val])
      _ fun i j => by fin_cases i <;> fin_cases j <;> simp [low_val]))
    (fun a y => hf _ (mem_parahoricTimesPrincipalCongruence_iff w c (aff a y) (by simp [aff_val]) (by simp [aff_val])
      _ fun i j => by fin_cases i <;> fin_cases j <;> simp [aff_val]))
    (fun hc => hf _ (mem_parahoricTimesPrincipalCongruence_iff w c (sw _) (by simp [hc]) (by simp [hc])
      _ fun i j => by fin_cases i <;> fin_cases j <;> simp [sw_val]))
    _ hS (fun g => by
      have h := congrFun (((uopSum F w _ (Hi.rtr ℂ _ V) c Φ hfix).2 _ hS).symm.trans hU) g
      rw [Pi.add_apply, Finset.sum_apply, ite_apply] at h
      exact h)
  rw [hcard] at key
  refine ⟨fun hc => ⟨fun x hx => ?_, (key.1 hc).2⟩, fun hc => ?_⟩
  · obtain ⟨y, rfl⟩ := hun x hx
    exact (key.1 hc).1 y
  · rcases key.2 hc with h | ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨fun x hx => by obtain ⟨y, rfl⟩ := hun x hx; exact h y, h'⟩)
    · exact Or.inr (Or.inr ⟨fun x hx => by obtain ⟨y, rfl⟩ := hun x hx; exact h y, h'⟩)

end UpperTheory.V.Sd
