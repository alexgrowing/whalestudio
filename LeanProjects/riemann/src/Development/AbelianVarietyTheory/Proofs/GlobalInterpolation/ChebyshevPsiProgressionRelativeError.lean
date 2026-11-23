import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumRpowZerosLeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RepulsionStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaDirichletZerosRightHalfStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExceptionalDirichletZeroUniqueZeroFreeRegionStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.PsiRel

lemma orth (M : ℕ) [NeZero M] (b : ℕ) (hb : Nat.Coprime b M) (u : ℝ) :
    (((M.totient : ℝ) * psiAP M b u : ℝ) : ℂ) = ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M)⁻¹ *
      ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod M) := by
  have hu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold psiAP
  rw [Finset.sum_filter, Finset.mul_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (n : ZMod M)
  have h2 : ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M)⁻¹ * (((Λ n : ℝ) : ℂ) * χ (n : ZMod M)) =
      ((Λ n : ℝ) : ℂ) * ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M)⁻¹ * χ (n : ZMod M) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun χ _ => by ring
  rw [h2, h]
  by_cases hn : n ≡ b [MOD M]
  · have : (b : ZMod M) = n := (ZMod.natCast_eq_natCast_iff _ _ _).2 hn.symm
    rw [if_pos hn, if_pos this]; push_cast; ring
  · have : ¬ (b : ZMod M) = n := fun h => hn ((ZMod.natCast_eq_natCast_iff _ _ _).1 h).symm
    rw [if_neg hn, if_neg this]; simp

lemma zsum (s t : Set ℂ) (ht : t.Finite) (hst : s ⊆ t) (o : ℂ → ℕ) (u : ℝ) (hu : 0 < u)
    (h : ∀ ρ ∈ s, 1 / 2 ≤ ρ.re) :
    ‖∑ᶠ ρ ∈ s, (o ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ 2 * u * ∑ᶠ ρ ∈ t, (o ρ : ℝ) * u ^ (ρ.re - 1) := by
  have hs := ht.subset hst
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ ht, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (g := fun ρ : ℂ => 2 * u * ((o ρ : ℝ) * u ^ (ρ.re - 1))) ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg (by simpa using hst) fun ρ _ _ => by positivity)
  intro ρ hρ
  have h1 := h ρ (by simpa using hρ)
  have h2 : 1 / 2 ≤ ‖ρ‖ := h1.trans (Complex.re_le_norm ρ)
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu,
    Real.rpow_sub_one hu.ne']
  have h3 : 0 < u ^ ρ.re := Real.rpow_pos_of_pos hu _
  have h4 : u ^ ρ.re / ‖ρ‖ ≤ 2 * u ^ ρ.re := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  calc (o ρ : ℝ) * (u ^ ρ.re / ‖ρ‖) ≤ (o ρ : ℝ) * (2 * u ^ ρ.re) := by gcongr
    _ = _ := by field_simp

lemma combine (M : ℕ) [NeZero M] (b : ℕ) (hb : Nat.Coprime b M) (u E x : ℝ) (hE : 0 ≤ E)
    (Z e : DirichletCharacter ℂ M → ℂ) (B : DirichletCharacter ℂ M → ℝ)
    (h1 : ∀ χ : DirichletCharacter ℂ M, ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod M)) -
      (if χ = 1 then (u : ℂ) else 0) + Z χ‖ ≤ E)
    (h2 : ∀ χ, ‖Z χ - e χ‖ ≤ B χ)
    (h3 : ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M)⁻¹ * e χ = (x : ℂ)) :
    |(M.totient : ℝ) * psiAP M b u - (u - x)| ≤ M * E + ∑ χ, B χ := by
  have hu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
  have hui : IsUnit (b : ZMod M)⁻¹ :=
    IsUnit.of_mul_eq_one (b : ZMod M) (ZMod.inv_mul_of_unit _ hu)
  have h4 : ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M)⁻¹ * (if χ = 1 then (u : ℂ) else 0) = u := by
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), MulChar.one_apply hui, one_mul]
  have key : (((M.totient : ℝ) * psiAP M b u - (u - x) : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M)⁻¹ *
        (((∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod M)) -
          (if χ = 1 then (u : ℂ) else 0) + Z χ) - (Z χ - e χ)) := by
    rw [Complex.ofReal_sub, orth M b hb u, Complex.ofReal_sub, ← h3]
    conv_lhs => rw [← h4]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun χ _ => by ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, key]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun χ => E + B χ) fun χ _ => ?_).trans ?_
  · rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans ?_
    exact (norm_sub_le _ _).trans (add_le_add (h1 χ) (h2 χ))
  · rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      ← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    have : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
    gcongr

lemma struct (M : ℕ) [NeZero M] (b : ℕ) (hb : Nat.Coprime b M) (θ : ℤ) (β u T η E : ℝ) (hu : 0 < u) (hE : 0 ≤ E)
    (h1 : ∀ χ : DirichletCharacter ℂ M, (zerosBox χ (1 / 2) T).Finite ∧
      ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod M)) - (if χ = 1 then (u : ℂ) else 0) +
        ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ E)
    (h2 : (θ = 0 ∧ ∀ (χ : DirichletCharacter ℂ M), ∀ ρ ∈ zerosBox χ (1 / 2) T, ρ.re ≤ 1 - η) ∨
      ∃ χ₁ : DirichletCharacter ℂ M, χ₁ ^ 2 = 1 ∧ χ₁ (b : ZMod M) = θ ∧ (β : ℂ) ∈ zerosBox χ₁ (1 / 2) T ∧
        ord χ₁ β = 1 ∧ ∀ (χ : DirichletCharacter ℂ M), ∀ ρ ∈ zerosBox χ (1 / 2) T,
          (χ = χ₁ ∧ ρ = β) ∨ ρ.re ≤ 1 - η) :
    |(M.totient : ℝ) * psiAP M b u - (u - θ * (u ^ β / β))| ≤ M * E + 2 * u *
      ∑ χ : DirichletCharacter ℂ M, (∑ᶠ ρ ∈ zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η},
        (ord χ ρ : ℝ) * u ^ (ρ.re - 1)) := by
  have hbu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
  rw [Finset.mul_sum]
  rcases h2 with ⟨h0, h2⟩ | ⟨χ₁, hsq, hθ, hβ, ho, h2⟩
  · refine combine M b hb u E _ hE _ (fun _ => 0) _ (fun χ => (h1 χ).2) (fun χ => ?_) (by simp [h0])
    rw [sub_zero]
    exact zsum _ _ ((h1 χ).1.inter_of_left _) (fun ρ hρ => ⟨hρ, h2 χ ρ hρ⟩) _ u hu fun ρ hρ => hρ.1
  · refine combine M b hb u E _ hE _ (fun χ => if χ = χ₁ then (u : ℂ) ^ (β : ℂ) / β else 0) _
      (fun χ => (h1 χ).2) (fun χ => ?_) ?_
    · by_cases hχ : χ = χ₁
      · subst hχ
        have hi : zerosBox χ (1 / 2) T = insert (β : ℂ) (zerosBox χ (1 / 2) T \ {(β : ℂ)}) := by
          rw [Set.insert_diff_singleton, Set.insert_eq_of_mem hβ]
        have : ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) =
            (u : ℂ) ^ (β : ℂ) / β +
            ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T \ {(β : ℂ)}, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) := by
          conv_lhs => rw [hi]
          rw [finsum_mem_insert _ (by simp) ((h1 χ).1.diff), ho]; simp
        simp only [if_true]
        rw [this, add_sub_cancel_left]
        refine zsum _ _ ((h1 χ).1.inter_of_left _) (fun ρ hρ => ⟨hρ.1, ?_⟩) _ u hu fun ρ hρ => hρ.1.1
        rcases h2 χ ρ hρ.1 with h | h
        · exact absurd h.2 hρ.2
        · exact h
      · simp only [if_neg hχ]
        rw [sub_zero]
        refine zsum _ _ ((h1 χ).1.inter_of_left _) (fun ρ hρ => ⟨hρ, ?_⟩) _ u hu fun ρ hρ => hρ.1
        rcases h2 χ ρ hρ with h | h
        · exact absurd h.1 hχ
        · exact h
    · simp_rw [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      have ha : χ₁ (b : ZMod M) * χ₁ (b : ZMod M) = 1 := by
        have := congrArg (fun ψ : DirichletCharacter ℂ M => ψ (b : ZMod M)) hsq
        simp only [pow_two, MulChar.mul_apply, MulChar.one_apply hbu] at this
        exact this
      have hb' : χ₁ (b : ZMod M)⁻¹ * χ₁ (b : ZMod M) = 1 := by
        rw [← map_mul, ZMod.inv_mul_of_unit _ hbu, map_one]
      have hc : χ₁ (b : ZMod M)⁻¹ = θ := by
        rw [← hθ]; linear_combination (-(χ₁ (b : ZMod M)⁻¹)) * ha + χ₁ (b : ZMod M) * hb'
      rw [hc]; push_cast; rw [Complex.ofReal_cpow hu.le]

lemma mainLower (θ β V : ℝ) (hθ : θ ≤ 1) (h1 : 7 / 8 ≤ β) (h2 : β < 1) (hV : 8 ≤ V) :
    Real.exp V * min 1 ((1 - β) * V) / 4 ≤ Real.exp V - θ * ((Real.exp V) ^ β / β) := by
  set x := (1 - β) * V with hx
  have hx0 : 0 < x := by positivity
  have hb : 0 < β := by linarith
  have e1 : (Real.exp V) ^ β = Real.exp V * Real.exp (-x) := by
    rw [← Real.exp_mul, ← Real.exp_add]; congr 1; rw [hx]; ring
  have e2 : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, one_div]; exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp x])
  have e3 : 8 * (1 - β) ≤ x := by rw [hx]; nlinarith
  have e4 : Real.exp (-x) / β ≤ 1 - min 1 x / 4 := by
    rw [div_le_iff₀ hb]; refine e2.trans ?_
    rw [div_le_iff₀ (by linarith)]
    rcases le_total 1 x with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]
      have : 0 ≤ (1 - x / 4) * (1 + x) := by apply mul_nonneg <;> linarith
      have h5 : (1 - x / 4) * (1 + x) * (1 - x / 8) ≤ (1 - x / 4) * (1 + x) * β := by
        gcongr; linarith
      nlinarith [mul_nonneg hx0.le (sub_nonneg.2 h), mul_nonneg hx0.le (mul_nonneg hx0.le hx0.le)]
  have hu := Real.exp_pos V
  have e5 : 0 < Real.exp (-x) / β := by positivity
  rw [e1, mul_div_assoc (Real.exp V) (Real.exp (-x))]
  have : θ * (Real.exp V * (Real.exp (-x) / β)) ≤ 1 * (Real.exp V * (1 - min 1 x / 4)) := by
    refine (mul_le_mul_of_nonneg_right hθ (by positivity)).trans ?_
    gcongr
  linarith

lemma realEnd (Ce Ca η₀ c' K cw R₀ : ℝ) (hCe : 0 < Ce) (hCa : 0 < Ca) (hη : 0 < η₀) (hc : 0 < c') (hK : 0 < K)
    (hcw : 0 < cw) :
    ∃ c₂ c₃ C : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧ ∀ m V w : ℝ, 1 ≤ m → c₂ * m ≤ V →
      0 < V ∧ R₀ * (10 * m + √V) ≤ V ∧ (cw * Real.exp (-(3 * m)) ≤ w →
      Real.exp m * (Ce * (Real.exp (-(8 * m + √V)) + Real.exp (-(V / 2)) * Real.exp (3 * m)) *
        (m + V + (8 * m + √V)) ^ 2) + 2 * (Ca * (K * w * Real.exp (-(c' * (V / (10 * m + √V)))) +
          Real.exp (-(η₀ * V)))) ≤
        C * (Real.exp (-c₃ * V / m) + Real.exp (-√(c₃ * V))) * (w / 4)) := by
  set R := max (max R₀ 2) (1 / η₀) with hR
  have hR2 : 2 ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hR0 : R₀ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRη : 1 ≤ η₀ * R := by
    have : 1 / η₀ ≤ R := le_max_right _ _
    rw [div_le_iff₀ hη] at this; linarith
  set c₃ := min (min (1 / 4) (c' / 20)) (c' ^ 2 / 4) with hc₃
  have hc3 : 0 < c₃ := by positivity
  have hc3a : c₃ ≤ 1 / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hc3b : c₃ ≤ c' / 20 := (min_le_left _ _).trans (min_le_right _ _)
  have hc3c : c₃ ≤ c' ^ 2 / 4 := min_le_right _ _
  refine ⟨20 * R + 4 * R ^ 2, c₃, 4 * ((3072 * Ce + 2 * Ca) / cw + 2 * Ca * K), by positivity, hc3,
    by positivity, fun m V w hm hV => ?_⟩
  have hV1 : 20 * R * m ≤ V := by nlinarith [sq_nonneg R]
  have hV2 : 4 * R ^ 2 ≤ V := by nlinarith [sq_nonneg R]
  have hV0 : 0 < V := by nlinarith
  set s := √V with hs
  have hs2 : s * s = V := Real.mul_self_sqrt hV0.le
  have hsR : 2 * R ≤ s := Real.le_sqrt_of_sq_le (by linarith)
  have hL : R * (10 * m + s) ≤ V := by nlinarith
  have hL0 : 0 < 10 * m + s := by linarith
  refine ⟨hV0, le_trans (by gcongr) hL, fun hw => ?_⟩
  have hL2 : 2 * (10 * m + s) ≤ V := le_trans (by gcongr) hL
  have hLη : 10 * m + s ≤ η₀ * V := by
    have := mul_le_mul_of_nonneg_left hL hη.le
    nlinarith
  set P := Real.exp (-c₃ * V / m) + Real.exp (-√(c₃ * V)) with hP
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hsq : ∀ a : ℝ, 0 ≤ a → c₃ ≤ a ^ 2 → √(c₃ * V) ≤ a * s := fun a ha h => by
    apply Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_pow, pow_two s, hs2]; gcongr
  have p1 : Real.exp (-(s / 2)) ≤ P := by
    have := hsq (1 / 2) (by norm_num) (by linarith)
    have h : Real.exp (-(s / 2)) ≤ Real.exp (-√(c₃ * V)) := by gcongr; linarith
    linarith [Real.exp_pos (-c₃ * V / m)]
  have p2 : Real.exp (-(c' * (V / (10 * m + s)))) ≤ P := by
    rcases le_total s (10 * m) with h | h
    · have h1 : V / (20 * m) ≤ V / (10 * m + s) := by gcongr; linarith
      have h2 : c₃ * V / m ≤ c' * (V / (20 * m)) := by
        have : c' * (V / (20 * m)) = c' / 20 * V / m := by field_simp
        rw [this]; gcongr
      have h3 : Real.exp (-(c' * (V / (10 * m + s)))) ≤ Real.exp (-c₃ * V / m) := by
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left h1 hc.le
        rw [neg_mul, neg_div]; linarith
      linarith [Real.exp_pos (-√(c₃ * V))]
    · have h1 : s / 2 ≤ V / (10 * m + s) := by
        rw [le_div_iff₀ hL0]; nlinarith
      have h2 := hsq (c' / 2) (by positivity) (by linarith)
      have h3 : Real.exp (-(c' * (V / (10 * m + s)))) ≤ Real.exp (-√(c₃ * V)) := by
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left h1 hc.le
        linarith
      linarith [Real.exp_pos (-c₃ * V / m)]
  have hs0 : 0 ≤ s := by linarith
  have q1 : (m + V + (8 * m + s)) ^ 2 ≤ 1536 * Real.exp (s / 2) := by
    have h1 : (m + V + (8 * m + s)) ^ 2 ≤ (2 * V) ^ 2 := by gcongr; linarith
    have h2 := Real.pow_div_factorial_le_exp (s / 2) (by linarith) 4
    have h3 : (s / 2) ^ 4 / ((Nat.factorial 4 : ℕ) : ℝ) = V ^ 2 / 384 := by
      rw [← hs2]; norm_num [Nat.factorial]; ring
    rw [h3] at h2; linarith
  set X := Real.exp (-(3 * m)) with hX
  have q2 : Real.exp m * (Real.exp (-(8 * m + s)) + Real.exp (-(V / 2)) * Real.exp (3 * m)) *
      Real.exp (s / 2) ≤ 2 * (X * Real.exp (-(s / 2))) := by
    rw [mul_add, add_mul, hX]
    simp only [← Real.exp_add]
    rw [two_mul]; exact add_le_add (Real.exp_le_exp.2 (by linarith)) (Real.exp_le_exp.2 (by linarith))
  have q3 : Real.exp (-(η₀ * V)) ≤ X * Real.exp (-(s / 2)) := by
    rw [hX, ← Real.exp_add]; gcongr; linarith
  have q4 : X * Real.exp (-(s / 2)) ≤ w / cw * P := by
    have : X ≤ w / cw := by rw [le_div_iff₀ hcw]; linarith
    gcongr
  have q5 : Real.exp m * (Ce * (Real.exp (-(8 * m + s)) + Real.exp (-(V / 2)) * Real.exp (3 * m)) *
        (m + V + (8 * m + s)) ^ 2) ≤ 3072 * Ce * (w / cw * P) := by
    calc _ ≤ Real.exp m * (Ce * (Real.exp (-(8 * m + s)) + Real.exp (-(V / 2)) * Real.exp (3 * m)) *
        (1536 * Real.exp (s / 2))) := by gcongr
      _ = 1536 * Ce * (Real.exp m * (Real.exp (-(8 * m + s)) + Real.exp (-(V / 2)) * Real.exp (3 * m)) *
        Real.exp (s / 2)) := by ring
      _ ≤ 1536 * Ce * (2 * (w / cw * P)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  calc _ ≤ 3072 * Ce * (w / cw * P) + 2 * (Ca * (K * w * P + w / cw * P)) := by
        gcongr; exact q3.trans q4
    _ = _ := by field_simp; ring

lemma etaChoice (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    ∃ c' K R₁ : ℝ, 0 < c' ∧ c' ≤ c / 2 ∧ 1 ≤ K ∧ ∀ δ R : ℝ, 0 < δ → 0 ≤ R → R₁ ≤ R → ∃ a : ℝ, 0 ≤ a ∧
      (a = c ∨ a = d * Real.log (d / δ)) ∧
      Real.exp (-(a * R / 2)) ≤ K * min 1 δ * Real.exp (-(c' * R)) := by
  set d₀ := min 1 (d / Real.exp 1) with hd₀
  have h0 : 0 < d₀ := by positivity
  have h1 : d₀ ≤ 1 := min_le_left _ _
  have h2 : d₀ * Real.exp 1 ≤ d := by
    have : d₀ ≤ d / Real.exp 1 := min_le_right _ _
    rwa [le_div_iff₀ (Real.exp_pos 1)] at this
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have ha : min (c / 2) (d / 4) ≤ c / 2 := min_le_left _ _
  have hb : min (c / 2) (d / 4) ≤ d / 4 := min_le_right _ _
  refine ⟨min (c / 2) (d / 4), 1 / d₀, 4 / d, by positivity, ha, by rwa [le_div_iff₀ h0, one_mul],
    fun δ R hδ hR0 hR => ?_⟩
  rcases le_total d₀ δ with h | h
  · refine ⟨c, hc.le, Or.inl rfl, ?_⟩
    have h3 : 1 ≤ 1 / d₀ * min 1 δ := by
      rw [one_div_mul_eq_div, le_div_iff₀ h0, one_mul]; exact le_min h1 h
    refine le_trans ?_ (le_mul_of_one_le_left (Real.exp_pos _).le h3)
    apply Real.exp_le_exp.2
    nlinarith
  · have hl : 1 ≤ Real.log (d / δ) := by
      rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hδ]; nlinarith
    refine ⟨d * Real.log (d / δ), by positivity, Or.inr rfl, ?_⟩
    have h4 : 4 ≤ d * R := by rw [div_le_iff₀ hd] at hR; linarith
    rw [min_eq_right (h.trans h1)]
    have h5 : Real.exp (-Real.log (d / δ)) ≤ 1 / d₀ * δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity), inv_div, one_div_mul_eq_div]
      gcongr; nlinarith
    refine le_trans ?_ (mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hb hR0
    nlinarith [mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 hl)]

set_option maxHeartbeats 1000000 in

theorem psiAP_relative : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₀ → ∃ c₂ c₃ C : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧ ∀ (M : ℕ) [NeZero M] (b : ℕ) (θ : ℤ) (β u : ℝ), 3 ≤ M → Nat.Coprime b M → ExcData c₁ M b θ β → (M : ℝ) ^ c₂ ≤ u → |(M.totient : ℝ) * psiAP M b u - (u - θ * (u ^ β / β))| ≤ C * (Real.exp (-c₃ * Real.log u / Real.log M) + Real.exp (-Real.sqrt (c₃ * Real.log u))) * (u - θ * (u ^ β / β)) := by
  obtain ⟨c₀, hc₀, hX⟩ := GlobalTheory.T.exceptionalDirichletZero_unique_zeroFreeRegion
  refine ⟨c₀, hc₀, fun c₁ hc₁ hc₁' => ?_⟩
  obtain ⟨c, hc, hX⟩ := hX c₁ hc₁ hc₁'
  obtain ⟨d, hd, hD⟩ := GlobalTheory.T.one_sub_re_ge_of_exceptional_zero_repulsion
  obtain ⟨Ce, hCe, hE⟩ := GlobalTheory.T.explicit_formula_dirichlet_zeros_right_half
  obtain ⟨A, Ca, η₀, hA, hCa, hη₀, hZ⟩ := GlobalTheory.T.exists_sum_characters_finsum_zeros_rpow_re_sub_one_le
  obtain ⟨c', K, R₁, hc', hc'', hK, hη⟩ := etaChoice c d hc hd
  obtain ⟨c₂, c₃, C, hc₂, hc₃, hC, hR⟩ := realEnd Ce Ca η₀ c' K (min 1 c) (max (max R₁ A) 8) hCe hCa hη₀ hc'
    (by linarith) (by positivity)
  refine ⟨c₂, c₃, C, hc₂, hc₃, hC, fun M _ b θ β u hM hb hexc hu => ?_⟩
  obtain ⟨hX1, hX2, hX3⟩ := hX M hM
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hu0 : 0 < u := lt_of_lt_of_le (Real.rpow_pos_of_pos hM0 _) hu
  obtain ⟨V, rfl⟩ : ∃ V, u = Real.exp V := ⟨Real.log u, (Real.exp_log hu0).symm⟩
  rw [Real.log_exp]
  set m := Real.log M with hm
  have hMm : (M : ℝ) = Real.exp m := (Real.exp_log hM0).symm
  have hm1 : 1 ≤ m := by
    rw [hm, Real.le_log_iff_exp_le hM0]; linarith [Real.exp_one_lt_d9]
  have hV : c₂ * m ≤ V := by
    rw [hMm, ← Real.exp_mul, Real.exp_le_exp] at hu; linarith
  have hs0 : 0 ≤ √V := Real.sqrt_nonneg V
  have hL : max (max R₁ A) 8 * (10 * m + √V) ≤ V := (hR m V 1 hm1 hV).2.1
  have hV0 : 0 < V := (hR m V 1 hm1 hV).1
  have hfin := fun w => (hR m V w hm1 hV).2.2
  clear hR
  set L := 10 * m + √V with hLd
  have hL1 : 10 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hL8 : 8 * L ≤ V := le_trans (by gcongr; exact le_max_right _ _) hL
  have hLA : A * L ≤ V := le_trans (by gcongr; exact (le_max_right _ _).trans (le_max_left _ _)) hL
  have hLR : R₁ ≤ V / L := by
    rw [le_div_iff₀ hL0]
    exact le_trans (by gcongr; exact (le_max_left _ _).trans (le_max_left _ _)) hL
  set T := Real.exp (8 * m + √V) with hT
  have hT2 : 2 ≤ T := by linarith [Real.add_one_le_exp (8 * m + √V)]
  have hTu : T ≤ Real.exp V := Real.exp_le_exp.2 (by linarith)
  have hTA : ((M : ℝ) * T) ^ A ≤ Real.exp V := by
    rw [hMm, hT, ← Real.exp_add, ← Real.exp_mul, Real.exp_le_exp]; nlinarith
  have hlog : ∀ ρ : ℂ, |ρ.im| ≤ T → 0 < Real.log (M * (|ρ.im| + 2)) ∧ Real.log (M * (|ρ.im| + 2)) ≤ L := by
    intro ρ hρ
    have h0 := abs_nonneg ρ.im
    refine ⟨Real.log_pos (by nlinarith), ?_⟩
    rw [Real.log_le_iff_le_exp (by positivity)]
    have : Real.exp L = M * (M * T) := by
      rw [hMm, hT, ← Real.exp_add, ← Real.exp_add]; congr 1; rw [hLd]; ring
    rw [this]; gcongr; nlinarith
  have hzf : ∀ (χ : DirichletCharacter ℂ M), ∀ ρ ∈ zerosBox χ (1 / 2) T,
      (ρ.im = 0 ∧ IsExc c₁ χ ρ.re) ∨ ρ.re ≤ 1 - c / L := by
    intro χ ρ hρ
    refine (hX3 χ ρ hρ.2.1 hρ.2.2.2).imp_right fun h => h.trans ?_
    obtain ⟨h1, h2⟩ := hlog ρ hρ.2.2.1
    gcongr
  have core : ∀ a w : ℝ, 0 ≤ a → min 1 c * Real.exp (-(3 * m)) ≤ w →
      Real.exp (-(a * (V / L) / 2)) ≤ K * w * Real.exp (-(c' * (V / L))) →
      Real.exp V * w / 4 ≤ Real.exp V - θ * (Real.exp V ^ β / β) →
      ((θ = 0 ∧ ∀ (χ : DirichletCharacter ℂ M), ∀ ρ ∈ zerosBox χ (1 / 2) T, ρ.re ≤ 1 - a / L) ∨
      ∃ χ₁ : DirichletCharacter ℂ M, χ₁ ^ 2 = 1 ∧ χ₁ (b : ZMod M) = θ ∧ (β : ℂ) ∈ zerosBox χ₁ (1 / 2) T ∧
        ord χ₁ β = 1 ∧ ∀ (χ : DirichletCharacter ℂ M), ∀ ρ ∈ zerosBox χ (1 / 2) T,
          (χ = χ₁ ∧ ρ = β) ∨ ρ.re ≤ 1 - a / L) →
      |(M.totient : ℝ) * psiAP M b (Real.exp V) - (Real.exp V - θ * (Real.exp V ^ β / β))| ≤
        C * (Real.exp (-c₃ * V / m) + Real.exp (-√(c₃ * V))) * (Real.exp V - θ * (Real.exp V ^ β / β)) := by
    intro a w ha hw h1 h2 h3
    have s1 := struct M b hb θ β (Real.exp V) T (a / L) _ hu0 (by positivity)
      (fun χ => hE M χ (Real.exp V) T hT2 hTu) h3
    have s2 := hZ M T (Real.exp V) (a / L) hT2 hTA (by positivity)
    have s3 := hfin w hw
    have e1 : Real.log (M * Real.exp V * T) = m + V + (8 * m + √V) := by
      rw [hMm, hT, ← Real.exp_add, ← Real.exp_add, Real.log_exp]
    have e2 : Real.exp V / T = Real.exp V * Real.exp (-(8 * m + √V)) := by
      rw [Real.exp_neg, div_eq_mul_inv]
    have e3 : √(Real.exp V) * (M : ℝ) ^ 3 = Real.exp V * (Real.exp (-(V / 2)) * Real.exp (3 * m)) := by
      rw [← Real.exp_half, hMm, ← Real.exp_nat_mul]
      simp only [← Real.exp_add]; congr 1; push_cast; ring
    have e4 : Real.exp V ^ (-(a / L) / 2) = Real.exp (-(a * (V / L) / 2)) := by
      rw [← Real.exp_mul]; congr 1; ring
    have e5 : Real.exp V ^ (-η₀) = Real.exp (-(η₀ * V)) := by
      rw [← Real.exp_mul]; congr 1; ring
    rw [e1, e2, e3] at s1
    rw [e4, e5] at s2
    have s4 := s2.trans (mul_le_mul_of_nonneg_left (add_le_add h1 le_rfl) hCa.le)
    have s5 := mul_le_mul_of_nonneg_left s4 (show 0 ≤ 2 * Real.exp V by positivity)
    have s6 := mul_le_mul_of_nonneg_left s3 hu0.le
    have s7 := mul_le_mul_of_nonneg_left h2
      (show 0 ≤ C * (Real.exp (-c₃ * V / m) + Real.exp (-√(c₃ * V))) by positivity)
    rw [← hMm] at s6
    linarith
  have hx3 : Real.exp (-(3 * m)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hmin1 : min 1 c * Real.exp (-(3 * m)) ≤ 1 :=
    mul_le_one₀ (min_le_left _ _) (Real.exp_pos _).le hx3
  have hVL : 0 ≤ V / L := by positivity
  rcases hexc with ⟨h0, hno⟩ | ⟨χ₁, hχ₁, hθ⟩
  · refine core c 1 hc.le hmin1 ?_ ?_ (Or.inl ⟨h0, fun χ ρ hρ => (hzf χ ρ hρ).resolve_left fun h => hno _ _ h.2⟩)
    · rw [mul_one]
      refine le_trans ?_ (le_mul_of_one_le_left (Real.exp_pos _).le hK)
      apply Real.exp_le_exp.2; nlinarith
    · rw [h0]; simp only [Int.cast_zero, zero_mul]; linarith
  · obtain ⟨hne, hβ1, hz, ho, hlow⟩ := hX2 χ₁ β hχ₁
    have hβ2 : β < 1 := hχ₁.2.2.1
    obtain ⟨a, ha, hor, hexp⟩ := hη ((1 - β) * L) (V / L) (mul_pos (by linarith) hL0) hVL hLR
    have hθ1 : (θ : ℝ) ≤ 1 := by
      have := χ₁.norm_le_one (b : ZMod M)
      rw [hθ, Complex.norm_intCast] at this
      exact (le_abs_self _).trans this
    refine core a _ ha (le_min hmin1 ?_) hexp ?_ (Or.inr ⟨χ₁, hχ₁.1, hθ, ⟨?_, ?_, ?_, hz⟩, ho, ?_⟩)
    · have h1 : Real.exp (-(3 * m)) = 1 / (M : ℝ) ^ 3 := by
        rw [hMm, ← Real.exp_nat_mul, Real.exp_neg, one_div]; norm_num
      have h2 : m ≤ M := by rw [hMm]; linarith [Real.add_one_le_exp m]
      have h3 : c / (M : ℝ) ^ 3 ≤ c / ((M : ℝ) ^ 2 * m) := by
        rw [pow_succ (M : ℝ) 2]; gcongr
      have h4 : min 1 c * (1 / (M : ℝ) ^ 3) ≤ c / (M : ℝ) ^ 3 := by
        rw [mul_one_div]; gcongr; exact min_le_right _ _
      rw [h1]; nlinarith
    · refine le_trans ?_ (mainLower θ β V hθ1 hβ1 hβ2 (by linarith))
      gcongr; linarith
    · simp only [Complex.ofReal_re]; linarith
    · simpa using hβ2
    · simp only [Complex.ofReal_im, abs_zero]; linarith
    · intro χ ρ hρ
      rcases hor with rfl | rfl
      · refine (hzf χ ρ hρ).imp_left fun h => ?_
        obtain ⟨h1, h2⟩ := hX1 χ χ₁ _ _ h.2 hχ₁
        exact ⟨h1, Complex.ext (by simpa using h2) (by simpa using h.1)⟩
      · by_cases h : χ = χ₁ ∧ ρ = β
        · exact Or.inl h
        · right
          have := hD M χ₁ χ β L ρ hne hχ₁.1 hβ2 (by linarith) hz hρ.2.2.2 hρ.1 hρ.2.1
            (by tauto) (hlog ρ hρ.2.2.1).2
          linarith

end GlobalTheory.Lin.PsiRel
