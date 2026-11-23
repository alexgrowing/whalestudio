import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open Matrix GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhitU

open Ad3 Ad3.R

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def low (z : F) : GL (Fin 2) F :=
  ⟨!![1, 0; z, 1], !![1, 0; -z, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def Dp (j : ℤ) (z : F) : Prop := z = 0 ∨ j ≤ ord z

local macro "gl2" : tactic => `(tactic| (apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
  simp [uni2, dg2, low, w0, upm, Matrix.mul_apply, Fin.sum_univ_two]))

theorem low_neg_mul (z : F) : low (-z) * low z = 1 := by gl2

theorem uni_neg_mul (z : F) : uni2 (-z) * uni2 z = 1 := by gl2

theorem low_inv (z : F) : (low z)⁻¹ = low (-z) := by
  rw [inv_eq_iff_mul_eq_one]; gl2

theorem uni_inv (z : F) : (uni2 z)⁻¹ = uni2 (-z) := by
  rw [inv_eq_iff_mul_eq_one]; gl2

theorem mem_int {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← mem_valBall_iff_le_ord hx, mem_valBall_zero_iff]

theorem mem_int_of_Dp {x : F} (h : Dp 0 x) : x ∈ 𝒪[F] := by
  rcases h with rfl | h
  · exact zero_mem _
  · by_cases hx : x = 0
    · subst hx; exact zero_mem _
    · exact (mem_int hx).2 h

theorem ord_neg' (x : F) : ord (-x) = ord x := by
  simp [ord, Valuation.map_neg]

theorem one_add_ord {x : F} (h : Dp 1 x) : 1 + x ≠ 0 ∧ ord (1 + x) = 0 := by
  have hv : ValuativeRel.valuation F x < 1 := by
    rcases h with rfl | h
    · simp
    · by_cases hx : x = 0
      · subst hx; simp
      · exact mem_valBall_one_iff.1 ((mem_valBall_iff_le_ord hx).2 h)
  have h1 : ValuativeRel.valuation F (1 + x) = 1 := Valuation.map_one_add_of_lt _ hv
  have h0 : 1 + x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  exact ⟨h0, (valuation_eq_one_iff_ord_eq_zero h0).1 h1⟩

theorem low_int {z : F} (hz : z ∈ 𝒪[F]) : low z ∈ integralGL F 2 := by
  rw [mem_integralGL_iff, low_inv]
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> simp [low, zero_mem, one_mem, hz, neg_mem]

theorem uni_int {z : F} (hz : z ∈ 𝒪[F]) : uni2 z ∈ integralGL F 2 := by
  rw [mem_integralGL_iff, uni_inv]
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> simp [uni2, zero_mem, one_mem, hz, neg_mem]

theorem dg_int {a : Fˣ} (ha : ord (a : F) = 0) : dg2 a 1 ∈ integralGL F 2 := by
  have h1 : (a : F) ∈ 𝒪[F] := (mem_int a.ne_zero).2 ha.ge
  have h2 : ((a⁻¹ : Fˣ) : F) ∈ 𝒪[F] := (mem_int (a⁻¹).ne_zero).2 (by rw [ord_units_inv, ha]; simp)
  have h3 : (a : F)⁻¹ ∈ 𝒪[F] := by simpa using h2
  have e : (dg2 a 1)⁻¹ = dg2 a⁻¹ 1 := by rw [inv_eq_iff_mul_eq_one]; gl2
  rw [mem_integralGL_iff, e]
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> simp [dg2, zero_mem, one_mem, h1, h3]

theorem inK_low {n : ℕ} {z : F} (hz : Dp n z) : GammaZeroLevelMembership n (low z) 1 := by
  refine ⟨low_int (mem_int_of_Dp ?_), ?_, by simp [low]⟩
  · rcases hz with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by positivity) h)
  · rcases hz with rfl | h
    · simp [low, zero_mem]
    · by_cases hx : z = 0
      · subst hx; simp [low, zero_mem]
      · have e : (low z) 1 0 = z := by simp [low]
        rw [e]
        have hu : (((unifUnit F)⁻¹ ^ n : Fˣ) : F) ≠ 0 := Units.ne_zero _
        refine (mem_int (mul_ne_zero hu hx)).2 ?_
        have h2 : ord ((((unifUnit F)⁻¹ ^ n : Fˣ)) : F) = -(n : ℤ) := by
          have : ((unifUnit F)⁻¹ ^ n : Fˣ) = unifUnit F ^ (-(n : ℤ)) := by simp
          rw [this, ord_unifUnit_zpow]
        rw [ord_mul hu hx, h2]
        omega

theorem inK_uni {n : ℕ} {u : F} (hu : u ∈ 𝒪[F]) : GammaZeroLevelMembership n (uni2 u) 1 :=
  ⟨uni_int hu, by simp [uni2, zero_mem], by simp [uni2]⟩

theorem inK_dg {n : ℕ} {a : Fˣ} (ha : ord (a : F) = 0) : GammaZeroLevelMembership n (dg2 a 1) 1 :=
  ⟨dg_int ha, by simp [dg2, zero_mem], by simp [dg2]⟩

variable {ψ : AddChar F Circle} {ω : Fˣ →* ℂˣ} {n : ℕ} {lam : ℂ} {W : GL (Fin 2) F → ℂ}

theorem psi_int (hψ : IsStd ψ) {x : F} (hx : x ∈ 𝒪[F]) : ψ x = 1 := by
  obtain ⟨hc, h1, h0⟩ := hψ
  apply isTrivialOn_addCharConductor hc h1 x
  rw [h0]
  exact mem_valBall_zero_iff.2 hx

theorem psi_wit (hψ : IsStd ψ) : ∃ y : F, y ≠ 0 ∧ -1 ≤ ord y ∧ ψ y ≠ 1 := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have h := not_isTrivialOn_addCharConductor_sub_one hc h1
  rw [h0] at h
  simp only [IsTrivialOn, not_forall] at h
  obtain ⟨y, hy, hne⟩ := h
  have y0 : y ≠ 0 := by
    rintro rfl
    simp at hne
  exact ⟨y, y0, by simpa using (mem_valBall_iff_le_ord y0).1 hy, hne⟩

theorem tri (hL : Law ψ ω W) {κ : GL (Fin 2) F} (hV : ∀ a : Fˣ, W (dg2 a 1 * κ) = 0)
    (t : GL (Fin 2) F) (ht : t 1 0 = 0) : W (t * κ) = 0 := by
  have hdet : (t : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnits_det_units t).ne_zero)
  rw [Matrix.det_fin_two] at hdet
  have ht' : (t : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := ht
  rw [ht', mul_zero, sub_zero] at hdet
  have h0 : (t : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have h1 : (t : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have e : t = uni2 ((t : Matrix (Fin 2) (Fin 2) F) 0 1 / (t : Matrix (Fin 2) (Fin 2) F) 1 1) *
      (dg2 (Units.mk0 _ h1) (Units.mk0 _ h1) * dg2 (Units.mk0 _ h0 * (Units.mk0 _ h1)⁻¹) 1) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two, ht'] <;> field_simp
  rw [e, mul_assoc, hL.1, mul_assoc, hL.2, hV]
  simp

theorem rinv (hT : TypeU ω n lam W) {x : GL (Fin 2) F} (hx : GammaZeroLevelMembership n x 1) (g : GL (Fin 2) F) :
    W (g * x) = W g := by
  have := hT.1 x 1 hx g
  simpa using this

theorem torus_neg (hψ : IsStd ψ) (hL : Law ψ ω W) (hT : TypeU ω n lam W) (a : Fˣ)
    (ha : ord (a : F) < 0) : W (dg2 a 1) = 0 := by
  obtain ⟨y, y0, hy, hne⟩ := psi_wit hψ
  have ai : (a : F)⁻¹ ≠ 0 := inv_ne_zero a.ne_zero
  have hu : y * (a : F)⁻¹ ∈ 𝒪[F] := by
    refine (mem_int (mul_ne_zero y0 ai)).2 ?_
    rw [ord_mul y0 ai, ord_inv a.ne_zero]
    omega
  have e : dg2 a 1 * uni2 (y * (a : F)⁻¹) = uni2 y * dg2 a 1 := by
    gl2
    field_simp
  have h := rinv hT (inK_uni hu) (dg2 a 1)
  rw [e, hL.1] at h
  by_contra hf
  apply hne
  have h2 : (ψ y : ℂ) = 1 := mul_right_cancel₀ hf (by simpa using h)
  exact Circle.ext (by simpa using h2)

theorem torus_step (hψ : IsStd ψ) (hL : Law ψ ω W) (hT : TypeU ω n lam W) {ϖ : Fˣ} {B : Finset F}
    (hR : Reps ϖ B) (a : Fˣ) (ha : 0 ≤ ord (a : F)) :
    (B.card : ℂ) * W (dg2 (a * ϖ) 1) = lam * W (dg2 a 1) := by
  rw [← hT.2 ϖ B hR (dg2 a 1)]
  have : ∀ b ∈ B, W (dg2 a 1 * upm ϖ b) = W (dg2 (a * ϖ) 1) := by
    intro b hb
    have hb' := hR.2.1 b hb
    have hab : (a : F) * b ∈ 𝒪[F] := mul_mem ((mem_int a.ne_zero).2 ha) hb'
    have e : dg2 a 1 * upm ϖ b = uni2 ((a : F) * b) * dg2 (a * ϖ) 1 := by
      gl2
    rw [e, hL.1, psi_int hψ hab]
    simp
  rw [Finset.sum_congr rfl this]
  simp

theorem card_ne {ϖ : Fˣ} {B : Finset F} (hR : Reps ϖ B) : (B.card : ℂ) ≠ 0 := by
  obtain ⟨b, ⟨hb, -⟩, -⟩ := hR.2.2 0 (zero_mem _)
  have : B.card ≠ 0 := Finset.card_ne_zero.2 ⟨b, hb⟩
  exact_mod_cast this

theorem torus_zero (hψ : IsStd ψ) (hL : Law ψ ω W) (hT : TypeU ω n lam W) {ϖ : Fˣ} {B : Finset F}
    (hR : Reps ϖ B) (h1 : W 1 = 0) (a : Fˣ) : W (dg2 a 1) = 0 := by
  have key : ∀ k : ℕ, ∀ a : Fˣ, ord (a : F) = k → W (dg2 a 1) = 0 := by
    intro k
    induction k with
    | zero =>
      intro a ha
      have := rinv hT (inK_dg (n := n) (a := a) (by simpa using ha)) 1
      rw [one_mul] at this
      rw [this, h1]
    | succ k ih =>
      intro a ha
      have ho : ord ((a * ϖ⁻¹ : Fˣ) : F) = k := by
        rw [ord_units_mul, ord_units_inv, hR.1, ha]
        push_cast
        ring
      have h := torus_step hψ hL hT hR (a * ϖ⁻¹) (by rw [ho]; positivity)
      rw [ih _ ho, mul_zero, inv_mul_cancel_right] at h
      exact (mul_eq_zero.1 h).resolve_left (card_ne hR)
  by_cases ha : 0 ≤ ord (a : F)
  · exact key (ord (a : F)).toNat a (by omega)
  · exact torus_neg hψ hL hT a (by omega)

theorem low_zero (hl : lam ≠ 0) (hL : Law ψ ω W) (hT : TypeU ω n lam W) {ϖ : Fˣ} {B : Finset F}
    (hR : Reps ϖ B) (hV : ∀ a : Fˣ, W (dg2 a 1) = 0) (k : ℕ) :
    ∀ z : F, Dp ((n : ℤ) - k) z → Dp 1 z → ∀ a : Fˣ, W (dg2 a 1 * low z) = 0 := by
  induction k with
  | zero =>
    intro z h _ a
    rw [rinv hT (inK_low (n := n) (by simpa using h))]
    exact hV a
  | succ k ih =>
    intro z h h' a
    by_cases z0 : z = 0
    · subst z0
      exact ih 0 (Or.inl rfl) (Or.inl rfl) a
    have hz1 : 1 ≤ ord z := h'.resolve_left z0
    have hz : (n : ℤ) - (k + 1 : ℕ) ≤ ord z := h.resolve_left z0
    have hsum := hT.2 ϖ B hR (dg2 a 1 * low z)
    have hϖ : (ϖ : F) ≠ 0 := ϖ.ne_zero
    have hzero : ∑ b ∈ B, W (dg2 a 1 * low z * upm ϖ b) = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb' := hR.2.1 b hb
      have hzb : Dp 1 (z * b) := by
        by_cases b0 : b = 0
        · left; simp [b0]
        · right
          rw [ord_mul z0 b0]
          have := (mem_int b0).1 hb'
          omega
      obtain ⟨y0, yo⟩ := one_add_ord hzb
      have yi : (1 + z * b)⁻¹ ≠ 0 := inv_ne_zero y0
      have zw : z * ϖ ≠ 0 := mul_ne_zero z0 hϖ
      have oz : ord (z * ϖ * (1 + z * b)⁻¹) = ord z + 1 := by
        rw [ord_mul zw yi, ord_mul z0 hϖ, ord_inv y0, yo, hR.1]
        ring
      have e : dg2 a 1 * low z * upm ϖ b =
          (dg2 a 1 * (low z * upm ϖ b * low (-(z * ϖ * (1 + z * b)⁻¹)))) * low (z * ϖ * (1 + z * b)⁻¹) := by
        simp only [mul_assoc, low_neg_mul, mul_one]
      rw [e]
      refine tri hL (ih _ (Or.inr ?_) (Or.inr ?_)) _ ?_
      · rw [oz]; push_cast at hz ⊢; omega
      · rw [oz]; omega
      · simp [uni2, dg2, low, upm, Matrix.mul_apply, Fin.sum_univ_two]
        field_simp
        ring
    rw [hzero] at hsum
    exact (mul_eq_zero.1 hsum.symm).resolve_left hl

theorem low_zero' (hl : lam ≠ 0) (hL : Law ψ ω W) (hT : TypeU ω n lam W) {ϖ : Fˣ} {B : Finset F}
    (hR : Reps ϖ B) (hV : ∀ a : Fˣ, W (dg2 a 1) = 0) {z : F} (hz : Dp 1 z) (a : Fˣ) :
    W (dg2 a 1 * low z) = 0 := by
  refine low_zero hl hL hT hR hV n z ?_ hz a
  rcases hz with h | h
  · exact Or.inl h
  · right; omega

theorem weight_vector_zero_of_neg_det (hψ : IsStd ψ) (hL : Law ψ ω W) (hT : TypeU ω n lam W) (a : Fˣ)
    (ha : ord (a : F) + n < 0) : W (dg2 a 1 * w0) = 0 := by
  obtain ⟨y, y0, hy, hne⟩ := psi_wit hψ
  have ai : (a : F)⁻¹ ≠ 0 := inv_ne_zero a.ne_zero
  have hu : Dp (n : ℤ) (-(y * (a : F)⁻¹)) := by
    right
    rw [ord_neg', ord_mul y0 ai, ord_inv a.ne_zero]
    omega
  have e : dg2 a 1 * w0 * low (-(y * (a : F)⁻¹)) = uni2 y * (dg2 a 1 * w0) := by
    gl2
    all_goals field_simp
  have h := rinv hT (inK_low hu) (dg2 a 1 * w0)
  rw [e, hL.1] at h
  by_contra hf
  apply hne
  have h2 : (ψ y : ℂ) = 1 := mul_right_cancel₀ hf (by simpa using h)
  exact Circle.ext (by simpa using h2)

theorem whittaker_weyl_hecke_recursion (hL : Law ψ ω W) (hT : TypeU ω n lam W) {ϖ : Fˣ} {B : Finset F} (hR : Reps ϖ B)
    (hlow : ∀ z : F, Dp 1 z → ∀ a : Fˣ, W (dg2 a 1 * low z) = 0) (a : Fˣ) :
    lam * W (dg2 a 1 * w0) = ((ω ϖ : ℂˣ) : ℂ) * W (dg2 (a * ϖ⁻¹) 1 * w0) := by
  have hϖ : (ϖ : F) ≠ 0 := ϖ.ne_zero
  have hϖi : (ϖ : F)⁻¹ ≠ 0 := inv_ne_zero hϖ
  obtain ⟨b₀, ⟨hb₀, hb₀'⟩, huniq⟩ := hR.2.2 0 (zero_mem _)
  rw [← hT.2 ϖ B hR (dg2 a 1 * w0), Finset.sum_eq_single_of_mem b₀ hb₀]
  · have hy : (ϖ : F)⁻¹ * b₀ ∈ 𝒪[F] := by
      have := neg_mem hb₀'
      simpa using this
    have e : dg2 a 1 * w0 * upm ϖ b₀ = dg2 ϖ ϖ * (dg2 (a * ϖ⁻¹) 1 * w0) * uni2 ((ϖ : F)⁻¹ * b₀) := by
      gl2
      all_goals field_simp
    rw [e, rinv hT (inK_uni hy), hL.2]
  · intro b hb hne
    have hb' := hR.2.1 b hb
    have b0 : b ≠ 0 := by
      rintro rfl
      exact hne (huniq 0 ⟨hb, by simp [zero_mem]⟩)
    have hn : ¬ ((ϖ⁻¹ : Fˣ) : F) * (0 - b) ∈ 𝒪[F] := fun h => hne (huniq b ⟨hb, h⟩)
    have hord : ord b = 0 := by
      have h1 := (mem_int b0).1 hb'
      have h2 : ((ϖ⁻¹ : Fˣ) : F) * (0 - b) ≠ 0 := by simp [hϖ, b0]
      rw [mem_int h2, zero_sub, ord_mul (ϖ⁻¹).ne_zero (neg_ne_zero.2 b0), ord_units_inv, hR.1, ord_neg'] at hn
      omega
    have bi : b⁻¹ ≠ 0 := inv_ne_zero b0
    have hz : Dp 1 ((ϖ : F) * b⁻¹) := by
      right
      rw [ord_mul hϖ bi, ord_inv b0, hord, hR.1]
      simp
    have e : dg2 a 1 * w0 * upm ϖ b =
        (dg2 a 1 * (w0 * upm ϖ b * low (-((ϖ : F) * b⁻¹)))) * low ((ϖ : F) * b⁻¹) := by
      simp only [mul_assoc, low_neg_mul, mul_one]
    rw [e]
    refine tri hL (hlow _ hz) _ ?_
    simp [uni2, dg2, low, upm, w0, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring

theorem weight_zero_not_pos_det (hψ : IsStd ψ) (hl : lam ≠ 0) (hL : Law ψ ω W) (hT : TypeU ω n lam W) {ϖ : Fˣ}
    {B : Finset F} (hR : Reps ϖ B) (hlow : ∀ z : F, Dp 1 z → ∀ a : Fˣ, W (dg2 a 1 * low z) = 0)
    (a : Fˣ) : W (dg2 a 1 * w0) = 0 := by
  have key : ∀ k : ℕ, ∀ a : Fˣ, ord (a : F) + n < k → W (dg2 a 1 * w0) = 0 := by
    intro k
    induction k with
    | zero =>
      intro a ha
      exact weight_vector_zero_of_neg_det hψ hL hT a (by simpa using ha)
    | succ k ih =>
      intro a ha
      have ho : ord ((a * ϖ⁻¹ : Fˣ) : F) + n < k := by
        rw [ord_units_mul, ord_units_inv, hR.1]
        push_cast at ha
        omega
      have h := whittaker_weyl_hecke_recursion hL hT hR hlow a
      rw [ih _ ho, mul_zero] at h
      exact (mul_eq_zero.1 h).resolve_left hl
  exact key (ord (a : F) + n + 1).toNat a (by omega)

end

theorem eq_zero_of_eigen : C1 → U1 := by
  intro hC F _ _ _ _ _ _ ψ hψ ω n lam W _ hl hL hT h1
  obtain ⟨⟨ϖ, B, hR⟩, -, -⟩ := hC F ψ hψ
  have hV := torus_zero hψ hL hT hR h1
  have hlow : ∀ z : F, Dp 1 z → ∀ a : Fˣ, W (dg2 a 1 * low z) = 0 :=
    fun z hz a => low_zero' hl hL hT hR hV hz a
  have hw := weight_zero_not_pos_det hψ hl hL hT hR hlow
  funext g
  have hg : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  rw [Matrix.det_fin_two] at hg
  set c := (g : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  by_cases hlt : c = 0 ∨ (d ≠ 0 ∧ ord d < ord c)
  · have d0 : d ≠ 0 := by
      rcases hlt with h | h
      · intro hd0
        apply hg
        rw [h, hd0]
        simp
      · exact h.1
    have hz : Dp 1 (c * d⁻¹) := by
      rcases hlt with h | h
      · left; simp [h]
      · by_cases c0 : c = 0
        · left; simp [c0]
        · right
          rw [ord_mul c0 (inv_ne_zero d0), ord_inv d0]
          omega
    have e : g = (g * low (-(c * d⁻¹))) * low (c * d⁻¹) := by
      simp only [mul_assoc, low_neg_mul, mul_one]
    rw [e]
    refine tri hL (hlow _ hz) _ ?_
    simp [low, Matrix.mul_apply, Fin.sum_univ_two, ← hc, ← hd]
    field_simp
    ring
  · push_neg at hlt
    obtain ⟨c0, hlt⟩ := hlt
    have hy : d * c⁻¹ ∈ 𝒪[F] := by
      by_cases d0 : d = 0
      · simp [d0, zero_mem]
      · refine (mem_int (mul_ne_zero d0 (inv_ne_zero c0))).2 ?_
        have := hlt d0
        rw [ord_mul d0 (inv_ne_zero c0), ord_inv c0]
        omega
    have e : g = (g * uni2 (-(d * c⁻¹)) * w0⁻¹) * w0 * uni2 (d * c⁻¹) := by
      have : uni2 (-(d * c⁻¹)) * uni2 (d * c⁻¹) = (1 : GL (Fin 2) F) := uni_neg_mul _
      simp only [mul_assoc, inv_mul_cancel_left, this, mul_one]
    rw [e, rinv hT (inK_uni hy)]
    refine tri hL hw _ ?_
    have ei : (w0⁻¹ : GL (Fin 2) F) = ⟨!![0, -1; 1, 0], !![0, 1; -1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩ := rfl
    rw [ei]
    simp [uni2, Matrix.mul_apply, Fin.sum_univ_two, ← hc, ← hd]
    field_simp
    ring

end GlobalTheory.CompanionTheory.WhitU

end
