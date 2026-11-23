import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GLnLocal (integralGL mem_integralGL_iff uniformizer irreducible_uniformizer)
open ValuativeRel IsLocalRing
open scoped ValuativeRel
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RankinStepC

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

variable (F) in

def Pv : ValueGroupWithZero F := valuation F ((uniformizer F : 𝒪[F]) : F)

theorem Pv_lt_one : Pv F < 1 := by
  unfold Pv
  exact valuation_lt_one_of_mem_maximalIdeal
    (uniformizer_mem_maximalIdeal (irreducible_uniformizer F))

private theorem uniformizer_coe_ne_zero' : ((uniformizer F : 𝒪[F]) : F) ≠ 0 := fun h =>
  (irreducible_uniformizer F).ne_zero (Subtype.ext (by simpa using h))

theorem Pv_pos : 0 < Pv F := by
  unfold Pv
  exact (Valuation.pos_iff _).2 uniformizer_coe_ne_zero'

theorem val_of_ord {ϖ : Fˣ} (h : ord (ϖ : F) = 1) : valuation F (ϖ : F) = Pv F := by
  unfold Pv
  apply (normalizedValuation_eq_iff).1
  rw [normalizedValuation_eq_exp_ord ϖ.ne_zero, h,
    normalizedValuation_uniformizer (irreducible_uniformizer F)]

theorem mem_inv_mul {ϖ : Fˣ} (h : ord (ϖ : F) = 1) (y : F) :
    ((ϖ⁻¹ : Fˣ) : F) * y ∈ 𝒪[F] ↔ valuation F y ≤ Pv F := by
  rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, val_of_ord h]
  exact inv_mul_le_one₀ Pv_pos

theorem mem_pow_mul (n : ℕ) (y : F) :
    (((unifUnit F)⁻¹ ^ n : Fˣ) : F) * y ∈ 𝒪[F] ↔ valuation F y ≤ Pv F ^ n := by
  rw [Valuation.mem_integer_iff, map_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
    map_pow, map_inv₀, val_of_ord (ϖ := unifUnit F) ord_unifUnit, inv_pow]
  exact inv_mul_le_one₀ (pow_pos Pv_pos n)

private theorem mem_maximalIdeal_iff_valuation_le_Pv (z : 𝒪[F]) :
    z ∈ maximalIdeal 𝒪[F] ↔ valuation F (z : F) ≤ Pv F := by
  rw [mem_maximalIdeal_iff_dvd (irreducible_uniformizer F)]
  constructor
  · rintro ⟨c, rfl⟩
    unfold Pv
    rw [show ((GLnLocal.uniformizer F * c : 𝒪[F]) : F) = ((uniformizer F : 𝒪[F]) : F) * c from rfl, map_mul]
    exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 c.2)
  · intro h
    refine ⟨⟨((uniformizer F : 𝒪[F]) : F)⁻¹ * z, ?_⟩, ?_⟩
    · rw [Valuation.mem_integer_iff, map_mul, map_inv₀]
      exact (inv_mul_le_one₀ Pv_pos).2 h
    · apply Subtype.ext
      show (z : F) = ((uniformizer F : 𝒪[F]) : F) * (((uniformizer F : 𝒪[F]) : F)⁻¹ * z)
      rw [mul_inv_cancel_left₀ uniformizer_coe_ne_zero']

theorem residue_eq_iff (x y : 𝒪[F]) :
    residue 𝒪[F] x = residue 𝒪[F] y ↔ valuation F ((x : F) - y) ≤ Pv F := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff_valuation_le_Pv]
  exact Iff.rfl

theorem reps_exists : ∃ (ϖ : Fˣ) (B : Finset F), Reps ϖ B := by
  classical
  have hfin : Finite (ResidueField 𝒪[F]) :=
    Nat.finite_of_card_ne_zero (Nat.cast_pos.1 (residueCard_pos_real (K := F))).ne'
  have := Fintype.ofFinite (ResidueField 𝒪[F])
  have hs := IsLocalRing.residue_surjective (R := 𝒪[F])
  let s := Function.surjInv hs
  have hu : ord ((unifUnit F : Fˣ) : F) = 1 := ord_unifUnit
  refine ⟨unifUnit F, Finset.univ.image (fun r => (s r : F)), ?_⟩
  unfold Ad3.R.Reps
  refine ⟨hu, ?_, ?_⟩
  · intro b hb
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hb
    exact (s r).2
  · intro x hx
    let xo : 𝒪[F] := ⟨x, hx⟩
    refine ⟨(s (residue 𝒪[F] xo) : F), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · rw [mem_inv_mul hu]
      exact (residue_eq_iff xo _).1 (Function.surjInv_eq hs _).symm
    · rintro b ⟨hb, hb'⟩
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hb
      rw [mem_inv_mul hu] at hb'
      have := (residue_eq_iff xo (s r)).2 hb'
      rw [Function.surjInv_eq hs] at this
      rw [this]

theorem reps_eq {ϖ : Fˣ} {B : Finset F} (h : Reps ϖ B) {b b' : F} (hb : b ∈ B) (hb' : b' ∈ B)
    (hv : valuation F (b - b') ≤ Pv F) : b = b' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨c, -, hc⟩ := h3 b (h2 b hb)
  have e1 := hc b ⟨hb, by simp⟩
  have e2 := hc b' ⟨hb', (mem_inv_mul h1 _).2 hv⟩
  exact e1.trans e2.symm

theorem reps_rep {ϖ : Fˣ} {B : Finset F} (h : Reps ϖ B) {t : F} (ht : t ∈ 𝒪[F]) :
    ∃ b, b ∈ B ∧ valuation F (t - b) ≤ Pv F := by
  obtain ⟨h1, -, h3⟩ := h
  obtain ⟨b, ⟨hb, hb'⟩, -⟩ := h3 t ht
  exact ⟨b, hb, (mem_inv_mul h1 _).1 hb'⟩

theorem reps_card {ϖ : Fˣ} {B : Finset F} (h : Reps ϖ B) : B.card = residueCard F := by
  classical
  have h2 : ∀ b ∈ B, b ∈ 𝒪[F] := by
    obtain ⟨-, h2, -⟩ := h
    exact h2
  unfold residueCard
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.ofBijective
    (fun b : B => residue 𝒪[F] (⟨b.1, h2 b.1 b.2⟩ : 𝒪[F])) ⟨?_, ?_⟩)
  · rintro ⟨b, hb⟩ ⟨b', hb'⟩ e
    exact Subtype.ext (reps_eq h hb hb' ((residue_eq_iff _ _).1 e))
  · intro r
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨b, hb, hv⟩ := reps_rep h t.2
    exact ⟨⟨b, hb⟩, ((residue_eq_iff t ⟨b, h2 b hb⟩).2 hv).symm⟩

theorem mem_int (g : GL (Fin 2) F) (h : ∀ i j, g i j ∈ 𝒪[F])
    (hd : valuation F (g.val.det) = 1) : g ∈ integralGL F 2 := by
  rw [mem_integralGL_iff]
  refine ⟨h, ?_⟩
  have hadj : ∀ i j, (g.val.adjugate) i j ∈ 𝒪[F] := by
    intro i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [h, neg_mem_iff]
  intro i j
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    Valuation.mem_integer_iff, map_mul, map_inv₀, hd, inv_one, one_mul]
  exact (Valuation.mem_integer_iff _ _).1 (hadj i j)

theorem val_det {x : GL (Fin 2) F} (hx : x ∈ integralGL F 2) : valuation F (x.val.det) = 1 := by
  rw [mem_integralGL_iff] at hx
  obtain ⟨h1, h2⟩ := hx
  have m1 : (x.val).det ∈ 𝒪[F] := by
    rw [Matrix.det_fin_two]
    exact sub_mem (mul_mem (h1 0 0) (h1 1 1)) (mul_mem (h1 0 1) (h1 1 0))
  have m2 : ((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det ∈ 𝒪[F] := by
    rw [Matrix.det_fin_two]
    exact sub_mem (mul_mem (h2 0 0) (h2 1 1)) (mul_mem (h2 0 1) (h2 1 0))
  have hp : (x.val).det * ((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [Valuation.mem_integer_iff] at m1 m2
  have hv := congrArg (valuation F) hp
  rw [map_mul, map_one] at hv
  refine le_antisymm m1 ?_
  rw [← hv]
  exact mul_le_of_le_one_right' m2

section Main

private theorem upm_coe_matrix (ϖ : Fˣ) (b : F) :
    ((upm ϖ b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(ϖ : F), b; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upm, Ad3.uni2, Ad3.dg2, Matrix.mul_apply, Fin.sum_univ_two]

private theorem upm_inv_coe_matrix (ϖ : Fˣ) (b : F) :
    (((upm ϖ b)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((ϖ⁻¹ : Fˣ) : F), -(((ϖ⁻¹ : Fˣ) : F) * b); 0, 1] := by
  rw [Matrix.coe_units_inv, upm_coe_matrix]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem entries (ϖ ϖ' : Fˣ) (β β' : F) (x : GL (Fin 2) F) :
    (((upm ϖ' β')⁻¹ * x * upm ϖ β : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((ϖ'⁻¹ : Fˣ) : F) * ((x 0 0 - β' * x 1 0) * ϖ),
          ((ϖ'⁻¹ : Fˣ) : F) * (x 0 0 * β + x 0 1 - β' * (x 1 0 * β + x 1 1));
        x 1 0 * ϖ, x 1 0 * β + x 1 1] := by
  rw [Units.val_mul, Units.val_mul, upm_inv_coe_matrix, upm_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

theorem congruence_subgroup_entry_valuations {n : ℕ} (hn : 1 ≤ n) {x : GL (Fin 2) F} {d : Fˣ} (h : GammaZeroLevelMembership n x d) :
    valuation F (x 0 0) = 1 ∧ valuation F (x 1 1) = 1 ∧ valuation F (x 0 1) ≤ 1 ∧
      valuation F (x 1 0) ≤ Pv F ^ n ∧ valuation F (x 1 0) < 1 := by
  obtain ⟨hint, hlow, -⟩ := h
  have hdet := val_det hint
  have he := ((mem_integralGL_iff F 2).1 hint).1
  have e : ∀ i j, valuation F (x i j) ≤ 1 := fun i j => (Valuation.mem_integer_iff _ _).1 (he i j)
  have h10 : valuation F (x 1 0) ≤ Pv F ^ n := (mem_pow_mul n _).1 hlow
  have h10' : valuation F (x 1 0) < 1 :=
    h10.trans_lt (pow_lt_one₀ zero_le Pv_lt_one (by omega))
  have hsm : valuation F (x 0 1 * x 1 0) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (e 0 1)).trans_lt h10'
  have hprod : valuation F (x 0 0) * valuation F (x 1 1) = 1 := by
    rw [← map_mul]
    have hx : x 0 0 * x 1 1 = x.val.det + x 0 1 * x 1 0 := by
      rw [Matrix.det_fin_two]
      ring
    rw [hx, Valuation.map_add_eq_of_lt_left _ (by rw [hdet]; exact hsm), hdet]
  refine ⟨le_antisymm (e 0 0) ?_, le_antisymm (e 1 1) ?_, e 0 1, h10, h10'⟩
  · rw [← hprod]
    exact mul_le_of_le_one_right' (e 1 1)
  · rw [← hprod]
    exact mul_le_of_le_one_left' (e 0 0)

theorem val_den {n : ℕ} (hn : 1 ≤ n) {x : GL (Fin 2) F} {d : Fˣ} (h : GammaZeroLevelMembership n x d) {β : F}
    (hβ : β ∈ 𝒪[F]) : valuation F (x 1 0 * β + x 1 1) = 1 := by
  obtain ⟨-, h11, -, -, h10⟩ := congruence_subgroup_entry_valuations hn h
  rw [Valuation.map_add_eq_of_lt_right _ ?_, h11]
  rw [h11, map_mul]
  exact (mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 hβ)).trans_lt h10

theorem step (ω : Fˣ →* ℂˣ) {n : ℕ} (f : GL (Fin 2) F → ℂ) (hn : 1 ≤ n)
    (hker : unitFiltrationUnits F n ≤ ω.ker)
    (hf : ∀ x d, GammaZeroLevelMembership n x d → ∀ g, f (g * x) = ((ω d : ℂˣ) : ℂ) * f g)
    {ϖ ϖ' : Fˣ} (h1 : ord (ϖ : F) = 1) (h2 : ord (ϖ' : F) = 1) {β β' : F} {x : GL (Fin 2) F} {d : Fˣ}
    (hx : GammaZeroLevelMembership n x d) (hβ : β ∈ 𝒪[F]) (hβ' : β' ∈ 𝒪[F])
    (hc : valuation F (x 0 0 * β + x 0 1 - β' * (x 1 0 * β + x 1 1)) ≤ Pv F) (g : GL (Fin 2) F) :
    f (g * x * upm ϖ β) = ((ω d : ℂˣ) : ℂ) * f (g * upm ϖ' β') := by
  obtain ⟨-, h11, -, h10, -⟩ := congruence_subgroup_entry_valuations hn hx
  have hD := val_den hn hx hβ
  obtain ⟨hint, -, hd⟩ := id hx
  have hdetx := val_det hint
  have he := ((mem_integralGL_iff F 2).1 hint).1
  have hDne : x 1 0 * β + x 1 1 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hD
    exact zero_ne_one hD
  have h11ne : x 1 1 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h11
    exact zero_ne_one h11
  have hPv : valuation F ((ϖ : Fˣ) : F) = Pv F := val_of_ord h1
  have hPv' : valuation F ((ϖ' : Fˣ) : F) = Pv F := val_of_ord h2
  have hϖO : ((ϖ : Fˣ) : F) ∈ 𝒪[F] := by
    rw [Valuation.mem_integer_iff, hPv]
    exact Pv_lt_one.le
  have hy := entries ϖ ϖ' β β' x
  set y : GL (Fin 2) F := (upm ϖ' β')⁻¹ * x * upm ϖ β with hyd
  have y00 : y 0 0 = ((ϖ'⁻¹ : Fˣ) : F) * ((x 0 0 - β' * x 1 0) * ϖ) := by
    change (y : Matrix (Fin 2) (Fin 2) F) 0 0 = _
    rw [hy]
    rfl
  have y01 : y 0 1 = ((ϖ'⁻¹ : Fˣ) : F) * (x 0 0 * β + x 0 1 - β' * (x 1 0 * β + x 1 1)) := by
    change (y : Matrix (Fin 2) (Fin 2) F) 0 1 = _
    rw [hy]
    rfl
  have y10 : y 1 0 = x 1 0 * ϖ := by
    change (y : Matrix (Fin 2) (Fin 2) F) 1 0 = _
    rw [hy]
    rfl
  have y11 : y 1 1 = x 1 0 * β + x 1 1 := by
    change (y : Matrix (Fin 2) (Fin 2) F) 1 1 = _
    rw [hy]
    rfl
  have hyent : ∀ i j, y i j ∈ 𝒪[F] := by
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [y00, mem_inv_mul h2, map_mul, hPv]
      exact mul_le_of_le_one_left'
        ((Valuation.mem_integer_iff _ _).1 (sub_mem (he 0 0) (mul_mem hβ' (he 1 0))))
    · rw [y01, mem_inv_mul h2]
      exact hc
    · rw [y10]
      exact mul_mem (he 1 0) hϖO
    · rw [y11]
      exact add_mem (mul_mem (he 1 0) hβ) (he 1 1)
  have hdety : valuation F (y.val.det) = 1 := by
    have hdy : y.val.det = ((ϖ'⁻¹ : Fˣ) : F) * ϖ * x.val.det := by
      rw [show y.val = (y : Matrix (Fin 2) (Fin 2) F) from rfl, hy, Matrix.det_fin_two_of,
        Matrix.det_fin_two]
      ring
    rw [hdy, map_mul, map_mul, hdetx, Units.val_inv_eq_inv_val, map_inv₀, hPv, hPv', mul_one,
      inv_mul_cancel₀ Pv_pos.ne']
  let d' : Fˣ := Units.mk0 _ hDne
  have hyK : GammaZeroLevelMembership n y d' := by
    unfold Ad3.R.GammaZeroLevelMembership
    refine ⟨mem_int y hyent hdety, ?_, ?_⟩
    · rw [mem_pow_mul]
      change valuation F (y 1 0) ≤ Pv F ^ n
      rw [y10, map_mul, hPv]
      exact (mul_le_of_le_one_right' Pv_lt_one.le).trans h10
    · change x 1 0 * β + x 1 1 = y 1 1
      rw [y11]
  have hu : d⁻¹ * d' ∈ unitFiltrationUnits F n := by
    rw [mem_unitFiltrationUnits_iff hn (irreducible_uniformizer F)]
    have hval : ((d⁻¹ * d' : Fˣ) : F) - 1 = x 1 0 * β * (x 1 1)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hd, Units.val_mk0]
      field_simp
      ring
    rw [hval, map_mul, map_mul, map_inv₀, h11, inv_one, mul_one]
    change valuation F (x 1 0) * valuation F β ≤ Pv F ^ n
    exact (mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 hβ)).trans h10
  have hω : ω d' = ω d := by
    have hk : ω (d⁻¹ * d') = 1 := hker hu
    rw [map_mul, map_inv] at hk
    exact (inv_mul_eq_one.1 hk).symm
  have hmul : g * x * upm ϖ β = g * upm ϖ' β' * y := by
    rw [hyd]
    group
  rw [hmul, hf y d' hyK, hω]

theorem sum_step (ω : Fˣ →* ℂˣ) {n : ℕ} (f : GL (Fin 2) F → ℂ) (hn : 1 ≤ n)
    (hker : unitFiltrationUnits F n ≤ ω.ker)
    (hf : ∀ x d, GammaZeroLevelMembership n x d → ∀ g, f (g * x) = ((ω d : ℂˣ) : ℂ) * f g)
    {ϖ ϖ' : Fˣ} {B B' : Finset F} (hB : Reps ϖ B) (hB' : Reps ϖ' B') {x : GL (Fin 2) F} {d : Fˣ}
    (hx : GammaZeroLevelMembership n x d) (g : GL (Fin 2) F) :
    ∑ b ∈ B, f (g * x * upm ϖ b) = ((ω d : ℂˣ) : ℂ) * ∑ b ∈ B', f (g * upm ϖ' b) := by
  classical
  have hBO : ∀ b ∈ B, b ∈ 𝒪[F] := by
    obtain ⟨-, h2, -⟩ := hB
    exact h2
  have hB'O : ∀ b ∈ B', b ∈ 𝒪[F] := by
    obtain ⟨-, h2, -⟩ := hB'
    exact h2
  have h1 : ord ((ϖ : Fˣ) : F) = 1 := by
    obtain ⟨h1, -, -⟩ := hB
    exact h1
  have h2 : ord ((ϖ' : Fˣ) : F) = 1 := by
    obtain ⟨h2, -, -⟩ := hB'
    exact h2
  obtain ⟨hint, -, -⟩ := id hx
  have hdetx := val_det hint
  have he := ((mem_integralGL_iff F 2).1 hint).1
  have hD : ∀ b ∈ B, valuation F (x 1 0 * b + x 1 1) = 1 := fun b hb => val_den hn hx (hBO b hb)
  have hDne : ∀ b ∈ B, x 1 0 * b + x 1 1 ≠ 0 := by
    intro b hb h0
    have := hD b hb
    rw [h0, map_zero] at this
    exact zero_ne_one this
  let t : F → F := fun b => (x 0 0 * b + x 0 1) * (x 1 0 * b + x 1 1)⁻¹
  have ht : ∀ b ∈ B, t b ∈ 𝒪[F] := by
    intro b hb
    rw [Valuation.mem_integer_iff, map_mul, map_inv₀, hD b hb, inv_one, mul_one]
    exact (Valuation.mem_integer_iff _ _).1 (add_mem (mul_mem (he 0 0) (hBO b hb)) (he 0 1))
  let φ : F → F := fun b =>
    if h : ∃ c, c ∈ B' ∧ valuation F (t b - c) ≤ Pv F then h.choose else 0
  have hφ : ∀ b ∈ B, φ b ∈ B' ∧ valuation F (t b - φ b) ≤ Pv F := by
    intro b hb
    have hex : ∃ c, c ∈ B' ∧ valuation F (t b - c) ≤ Pv F := reps_rep hB' (ht b hb)
    simp only [φ, dif_pos hex]
    exact hex.choose_spec
  have hkey : ∀ b ∈ B, ∀ c : F,
      x 0 0 * b + x 0 1 - c * (x 1 0 * b + x 1 1) = (t b - c) * (x 1 0 * b + x 1 1) := by
    intro b hb c
    simp only [t]
    rw [sub_mul, mul_assoc, inv_mul_cancel₀ (hDne b hb), mul_one]
  have hstep : ∀ b ∈ B, f (g * x * upm ϖ b) = ((ω d : ℂˣ) : ℂ) * f (g * upm ϖ' (φ b)) := by
    intro b hb
    refine step ω f hn hker hf h1 h2 hx (hBO b hb) (hB'O _ (hφ b hb).1) ?_ g
    rw [hkey b hb, map_mul, hD b hb, mul_one]
    exact (hφ b hb).2
  have hinj : Set.InjOn φ B := by
    intro b1 hb1 b2 hb2 e
    have k1 := (hφ b1 hb1).2
    have k2 := (hφ b2 hb2).2
    rw [e] at k1
    have k : valuation F (t b1 - t b2) ≤ Pv F := by
      have : t b1 - t b2 = (t b1 - φ b2) - (t b2 - φ b2) := by ring
      rw [this]
      exact Valuation.map_sub_le _ k1 k2
    have ht12 : t b1 - t b2 =
        x.val.det * (b1 - b2) * ((x 1 0 * b1 + x 1 1) * (x 1 0 * b2 + x 1 1))⁻¹ := by
      have hD1 := hDne b1 hb1
      have hD2 := hDne b2 hb2
      have hnum : (x 0 0 * b1 + x 0 1) * (x 1 0 * b2 + x 1 1) -
          (x 0 0 * b2 + x 0 1) * (x 1 0 * b1 + x 1 1) = x.val.det * (b1 - b2) := by
        rw [Matrix.det_fin_two]
        ring
      rw [← hnum]
      simp only [t]
      generalize x 1 0 * b1 + x 1 1 = D1 at hD1 ⊢
      generalize x 1 0 * b2 + x 1 1 = D2 at hD2 ⊢
      field_simp <;> ring
    rw [ht12, map_mul, map_mul, hdetx, one_mul, map_inv₀, map_mul, hD b1 hb1, hD b2 hb2,
      mul_one, inv_one, mul_one] at k
    exact reps_eq hB hb1 hb2 k
  have himg : B.image φ = B' := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hc
      exact (hφ b hb).1
    · rw [Finset.card_image_of_injOn hinj, reps_card hB, reps_card hB']
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, ← himg, Finset.sum_image hinj]

end Main

theorem c1 : Ad3.R.C1 := by
  unfold Ad3.R.C1 Ad3.R.ForF
  intro F _ _ _ _ _ _ ψ _
  beta_reduce
  refine ⟨reps_exists, fun ϖ B hB => reps_card hB, ?_⟩
  intro ω n f hn hker hf ϖ B ϖ' B' hB hB' x d hx g
  exact sum_step ω f hn hker hf hB hB' hx g

end GlobalTheory.CompanionTheory.RankinStepC

end
