import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.HeckeCosets

open Ad3 Ad3.R

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mem_integer_iff {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  change ValuativeRel.valuation F x ≤ 1 ↔ _
  rw [← map_one (ValuativeRel.valuation F), ← normalizedValuation_le_iff, map_one,
    normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem ord_one' : ord (1 : F) = 0 := by simp [ord]

theorem ord_inv' {x : F} (hx : x ≠ 0) : ord x⁻¹ = - ord x := by
  have h := ord_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ord_one'] at h
  omega

theorem valuation_eq_one {x : F} (hx : x ≠ 0) (h : ord x = 0) : ValuativeRel.valuation F x = 1 := by
  rw [← map_one (ValuativeRel.valuation F), ← normalizedValuation_eq_iff, map_one,
    normalizedValuation_eq_exp_ord hx, h]
  simp

theorem dvd_or_unit {p y : F} (hp : p ≠ 0) (hp1 : ord p = 1) (hy : y ∈ 𝒪[F]) :
    p⁻¹ * y ∈ 𝒪[F] ∨ (y ≠ 0 ∧ y⁻¹ ∈ 𝒪[F]) := by
  by_cases h0 : y = 0
  · left; simp [h0, (𝒪[F]).zero_mem]
  have h1 := (mem_integer_iff h0).1 hy
  by_cases h2 : ord y = 0
  · right
    refine ⟨h0, (mem_integer_iff (inv_ne_zero h0)).2 ?_⟩
    rw [ord_inv' h0]; omega
  · left
    rw [mem_integer_iff (mul_ne_zero (inv_ne_zero hp) h0), ord_mul (inv_ne_zero hp) h0, ord_inv' hp]
    omega

def cos (ϖ : Fˣ) : Option F → GL (Fin 2) F
  | some b => upm ϖ b
  | none => dg2 1 ϖ

theorem cos_some_inv_mul (ϖ : Fˣ) (b : F) (M : GL (Fin 2) F) :
    (((cos ϖ (some b))⁻¹ * M : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(ϖ : F)⁻¹ * (M 0 0 - b * M 1 0), (ϖ : F)⁻¹ * (M 0 1 - b * M 1 1); M 1 0, M 1 1] := by
  have h1 : (((uni2 b)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, -b; 0, 1] := rfl
  have h2 : (((dg2 ϖ 1)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(((ϖ⁻¹ : Fˣ)) : F), 0; 0, ((1⁻¹ : Fˣ) : F)] := rfl
  simp only [cos, upm, _root_.mul_inv_rev, Units.val_mul, h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem cos_none_inv_mul (ϖ : Fˣ) (M : GL (Fin 2) F) :
    (((cos ϖ none)⁻¹ * M : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![M 0 0, M 0 1; (ϖ : F)⁻¹ * M 1 0, (ϖ : F)⁻¹ * M 1 1] := by
  have h2 : (((dg2 1 ϖ)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![((1⁻¹ : Fˣ) : F), 0; 0, (((ϖ⁻¹ : Fˣ)) : F)] := rfl
  simp only [cos, Units.val_mul, h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_cos_inv_mul (ϖ : Fˣ) (i : Option F) (M : GL (Fin 2) F) :
    (((cos ϖ i)⁻¹ * M : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (ϖ : F)⁻¹ * (M : Matrix (Fin 2) (Fin 2) F).det := by
  cases i with
  | none => rw [cos_none_inv_mul, Matrix.det_fin_two_of, Matrix.det_fin_two]; ring
  | some b => rw [cos_some_inv_mul, Matrix.det_fin_two_of, Matrix.det_fin_two]; ring

theorem of2 {a b c d : F} (ha : a ∈ 𝒪[F]) (hb : b ∈ 𝒪[F]) (hc : c ∈ 𝒪[F]) (hd : d ∈ 𝒪[F]) :
    ∀ i j, (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F] := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

theorem det_mem {M : Matrix (Fin 2) (Fin 2) F} (hM : ∀ i j, M i j ∈ 𝒪[F]) : M.det ∈ 𝒪[F] := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM _ _) (hM _ _)) (mul_mem (hM _ _) (hM _ _))

theorem exists_cos {ϖ : Fˣ} {B : Finset F} (hR : Reps ϖ B) (M : GL (Fin 2) F)
    (hM : ∀ i j, M i j ∈ 𝒪[F]) (hd : ord (M : Matrix (Fin 2) (Fin 2) F).det = 1) :
    ∃ i : Option B, (cos ϖ (i.map Subtype.val))⁻¹ * M ∈ integralGL F 2 := by
  obtain ⟨hϖ1, hB, hu⟩ := hR
  have hp : (ϖ : F) ≠ 0 := ϖ.ne_zero
  have hdet0 : (M : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have := M.isUnit.map (Matrix.detMonoidHom (n := Fin 2) (R := F))
    exact this.ne_zero
  have hDq : (ϖ : F)⁻¹ * (M : Matrix (Fin 2) (Fin 2) F).det ∈ 𝒪[F] := by
    rw [mem_integer_iff (mul_ne_zero (inv_ne_zero hp) hdet0), ord_mul (inv_ne_zero hp) hdet0,
      ord_inv' hp, hd, hϖ1]
    norm_num
  have hval : ∀ i, ValuativeRel.valuation F
      (((cos ϖ i)⁻¹ * M : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := fun i => by
    rw [det_cos_inv_mul]
    refine valuation_eq_one (mul_ne_zero (inv_ne_zero hp) hdet0) ?_
    rw [ord_mul (inv_ne_zero hp) hdet0, ord_inv' hp, hd, hϖ1]
    norm_num
  have hsome : ∀ β ∈ B, (ϖ : F)⁻¹ * (M 0 0 - β * M 1 0) ∈ 𝒪[F] →
      (ϖ : F)⁻¹ * (M 0 1 - β * M 1 1) ∈ 𝒪[F] →
      ∃ i : Option B, (cos ϖ (i.map Subtype.val))⁻¹ * M ∈ integralGL F 2 := fun β hβ h0 h1 => by
    refine ⟨some ⟨β, hβ⟩, Spherical.mem_integralGL_of_forall_mem (fun i j => ?_) (hval _)⟩
    change (((cos ϖ (some β))⁻¹ * M : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F]
    rw [cos_some_inv_mul]
    exact of2 h0 h1 (hM 1 0) (hM 1 1) i j
  by_cases hc : (ϖ : F)⁻¹ * M 1 0 ∈ 𝒪[F] ∧ (ϖ : F)⁻¹ * M 1 1 ∈ 𝒪[F]
  · refine ⟨none, Spherical.mem_integralGL_of_forall_mem (fun i j => ?_) (hval _)⟩
    change (((cos ϖ none)⁻¹ * M : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F]
    rw [cos_none_inv_mul]
    exact of2 (hM 0 0) (hM 0 1) hc.1 hc.2 i j
  have hor : (M 1 0 ≠ 0 ∧ (M 1 0)⁻¹ ∈ 𝒪[F]) ∨ (M 1 1 ≠ 0 ∧ (M 1 1)⁻¹ ∈ 𝒪[F]) := by
    rcases dvd_or_unit hp hϖ1 (hM 1 0) with h | h
    · rcases dvd_or_unit hp hϖ1 (hM 1 1) with h' | h'
      · exact absurd ⟨h, h'⟩ hc
      · exact Or.inr h'
    · exact Or.inl h
  rw [Matrix.det_fin_two] at hDq
  rcases hor with ⟨h0, hi⟩ | ⟨h0, hi⟩
  · obtain ⟨β, ⟨hβ, hβx⟩, -⟩ := hu (M 0 0 * (M 1 0)⁻¹) (mul_mem (hM 0 0) hi)
    rw [Units.val_inv_eq_inv_val] at hβx
    refine hsome β hβ ?_ ?_
    · have e : (ϖ : F)⁻¹ * (M 0 0 - β * M 1 0) = ((ϖ : F)⁻¹ * (M 0 0 * (M 1 0)⁻¹ - β)) * M 1 0 := by
        field_simp
      rw [e]
      exact mul_mem hβx (hM 1 0)
    · have e : (ϖ : F)⁻¹ * (M 0 1 - β * M 1 1) =
          ((ϖ : F)⁻¹ * (M 0 0 * (M 1 0)⁻¹ - β)) * M 1 1 -
            ((ϖ : F)⁻¹ * (M 0 0 * M 1 1 - M 0 1 * M 1 0)) * (M 1 0)⁻¹ := by
        field_simp
        ring
      rw [e]
      exact sub_mem (mul_mem hβx (hM 1 1)) (mul_mem hDq hi)
  · obtain ⟨β, ⟨hβ, hβx⟩, -⟩ := hu (M 0 1 * (M 1 1)⁻¹) (mul_mem (hM 0 1) hi)
    rw [Units.val_inv_eq_inv_val] at hβx
    refine hsome β hβ ?_ ?_
    · have e : (ϖ : F)⁻¹ * (M 0 0 - β * M 1 0) =
          ((ϖ : F)⁻¹ * (M 0 0 * M 1 1 - M 0 1 * M 1 0)) * (M 1 1)⁻¹ +
            ((ϖ : F)⁻¹ * (M 0 1 * (M 1 1)⁻¹ - β)) * M 1 0 := by
        field_simp
        ring
      rw [e]
      exact add_mem (mul_mem hDq hi) (mul_mem hβx (hM 1 0))
    · have e : (ϖ : F)⁻¹ * (M 0 1 - β * M 1 1) = ((ϖ : F)⁻¹ * (M 0 1 * (M 1 1)⁻¹ - β)) * M 1 1 := by
        field_simp
      rw [e]
      exact mul_mem hβx (hM 1 1)

theorem upm_val (ϖ : Fˣ) (b : F) :
    (upm ϖ b : Matrix (Fin 2) (Fin 2) F) = !![(ϖ : F), b; 0, 1] := by
  simp only [upm, Units.val_mul]
  change (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) F) * !![(ϖ : F), 0; 0, ((1 : Fˣ) : F)] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem hecke_diagonal_val (ϖ : Fˣ) :
    (dg2 1 ϖ : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, (ϖ : F)] := by
  change !![((1 : Fˣ) : F), 0; 0, (ϖ : F)] = _
  simp

theorem cos_inj {ϖ : Fˣ} {B : Finset F} (hR : Reps ϖ B) {i j : Option B}
    (h : (cos ϖ (i.map Subtype.val))⁻¹ * cos ϖ (j.map Subtype.val) ∈ integralGL F 2) : i = j := by
  obtain ⟨hϖ1, hB, hu⟩ := hR
  have hp : (ϖ : F) ≠ 0 := ϖ.ne_zero
  have hent := ((GLnLocal.mem_integralGL_iff F 2).1 h).1
  have hninv : (ϖ : F)⁻¹ ∉ 𝒪[F] := fun h => by
    have := (mem_integer_iff (inv_ne_zero hp)).1 h
    rw [ord_inv' hp, hϖ1] at this
    omega
  rcases i with _ | ⟨β, hβ⟩ <;> rcases j with _ | ⟨β', hβ'⟩
  · rfl
  · exfalso
    have h11 := hent 1 1
    change (((cos ϖ none)⁻¹ * cos ϖ (some β') : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 ∈ 𝒪[F] at h11
    rw [cos_none_inv_mul] at h11
    simp [cos, upm_val] at h11
    exact hninv h11
  · exfalso
    have h00 := hent 0 0
    change (((cos ϖ (some β))⁻¹ * cos ϖ none : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 ∈ 𝒪[F] at h00
    rw [cos_some_inv_mul] at h00
    simp [cos, hecke_diagonal_val] at h00
    exact hninv h00
  · have h01 := hent 0 1
    change (((cos ϖ (some β))⁻¹ * cos ϖ (some β') : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 ∈ 𝒪[F] at h01
    rw [cos_some_inv_mul] at h01
    simp [cos, upm_val] at h01
    have := (hu β' (hB β' hβ')).unique (y₁ := β) (y₂ := β')
      ⟨hβ, by rw [Units.val_inv_eq_inv_val]; exact h01⟩ ⟨hβ', by simp [(𝒪[F]).zero_mem]⟩
    subst this
    rfl

theorem cos_mem {ϖ : Fˣ} {B : Finset F} (hR : Reps ϖ B) (i : Option B) :
    ∀ a b, (cos ϖ (i.map Subtype.val)) a b ∈ 𝒪[F] := by
  have hϖ : (ϖ : F) ∈ 𝒪[F] := by
    rw [mem_integer_iff ϖ.ne_zero, hR.1]
    norm_num
  rcases i with _ | ⟨β, hβ⟩
  · intro a b
    change (dg2 1 ϖ : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]
    rw [hecke_diagonal_val]
    exact of2 (one_mem _) (zero_mem _) (zero_mem _) hϖ a b
  · intro a b
    change (upm ϖ β : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]
    rw [upm_val]
    exact of2 hϖ (hR.2.1 β hβ) (zero_mem _) (one_mem _) a b

theorem det_cos (ϖ : Fˣ) (i : Option F) :
    ((cos ϖ i : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = ϖ := by
  cases i with
  | none => simp only [cos]; rw [hecke_diagonal_val, Matrix.det_fin_two_of]; ring
  | some b => simp only [cos]; rw [upm_val, Matrix.det_fin_two_of]; ring

theorem ord_det_eq_zero {y : GL (Fin 2) F} (hy : y ∈ integralGL F 2) :
    ord (y : Matrix (Fin 2) (Fin 2) F).det = 0 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hy
  have hm : (y : Matrix (Fin 2) (Fin 2) F).det * ((y⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have n1 := left_ne_zero_of_mul_eq_one hm
  have n2 := right_ne_zero_of_mul_eq_one hm
  have o1 := (mem_integer_iff n1).1 (det_mem h1)
  have o2 := (mem_integer_iff n2).1 (det_mem h2)
  have o3 := ord_mul n1 n2
  rw [hm, ord_one'] at o3
  omega

theorem exists_match {ϖ₁ ϖ₂ : Fˣ} {B₁ B₂ : Finset F} (h₁ : Reps ϖ₁ B₁) (h₂ : Reps ϖ₂ B₂)
    {y : GL (Fin 2) F} (hy : y ∈ integralGL F 2) (i : Option B₁) :
    ∃ j : Option B₂, (cos ϖ₂ (j.map Subtype.val))⁻¹ * (y * cos ϖ₁ (i.map Subtype.val)) ∈
      integralGL F 2 := by
  refine exists_cos h₂ _ (fun a b => ?_) ?_
  · have hy1 := ((GLnLocal.mem_integralGL_iff F 2).1 hy).1
    have hc := cos_mem h₁ i
    change ((y : Matrix (Fin 2) (Fin 2) F) * (cos ϖ₁ (i.map Subtype.val) : Matrix (Fin 2) (Fin 2) F)) a b ∈ 𝒪[F]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem (mul_mem (hy1 _ _) (hc _ _)) (mul_mem (hy1 _ _) (hc _ _))
  · have hyd : (y : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
      (y.isUnit.map (Matrix.detMonoidHom (n := Fin 2) (R := F))).ne_zero
    rw [Units.val_mul, Matrix.det_mul, det_cos, ord_mul hyd ϖ₁.ne_zero, ord_det_eq_zero hy, h₁.1]
    norm_num

theorem sum_cos (ϖ : Fˣ) (B : Finset F) (G : GL (Fin 2) F → ℂ) :
    ∑ i : Option B, G (cos ϖ (i.map Subtype.val)) = ∑ b ∈ B, G (upm ϖ b) + G (dg2 1 ϖ) := by
  rw [Fintype.sum_option, add_comm]
  congr 1
  exact Finset.sum_coe_sort B (fun b => G (upm ϖ b))

theorem sum_eq {ϖ ϖ' : Fˣ} {B B' : Finset F} (hR : Reps ϖ B) (hR' : Reps ϖ' B')
    (f : GL (Fin 2) F → ℂ) (hf : ∀ x ∈ integralGL F 2, ∀ g, f (g * x) = f g)
    {x : GL (Fin 2) F} (hx : x ∈ integralGL F 2) (g : GL (Fin 2) F) :
    ∑ b ∈ B, f (g * x * upm ϖ b) + f (g * x * dg2 1 ϖ) =
      ∑ b ∈ B', f (g * upm ϖ' b) + f (g * dg2 1 ϖ') := by
  rw [← sum_cos ϖ B (fun h => f (g * x * h)), ← sum_cos ϖ' B' (fun h => f (g * h))]
  choose e he using fun i : Option B => exists_match hR hR' hx i
  have hinj : Function.Injective e := by
    intro i i' hii
    have h1 := he i
    have h2 := he i'
    rw [← hii] at h2
    have h3 := mul_mem (inv_mem h1) h2
    have h4 : ((cos ϖ' ((e i).map Subtype.val))⁻¹ * (x * cos ϖ (i.map Subtype.val)))⁻¹ *
        ((cos ϖ' ((e i).map Subtype.val))⁻¹ * (x * cos ϖ (i'.map Subtype.val))) =
        (cos ϖ (i.map Subtype.val))⁻¹ * cos ϖ (i'.map Subtype.val) := by group
    rw [h4] at h3
    exact cos_inj hR h3
  have hsurj : Function.Surjective e := by
    intro j
    obtain ⟨i, hi⟩ := exists_match hR' hR (inv_mem hx) j
    refine ⟨i, ?_⟩
    have h3 := mul_mem (he i) hi
    have h4 : ((cos ϖ' ((e i).map Subtype.val))⁻¹ * (x * cos ϖ (i.map Subtype.val))) *
        ((cos ϖ (i.map Subtype.val))⁻¹ * (x⁻¹ * cos ϖ' (j.map Subtype.val))) =
        (cos ϖ' ((e i).map Subtype.val))⁻¹ * cos ϖ' (j.map Subtype.val) := by group
    rw [h4] at h3
    exact cos_inj hR' h3
  refine Fintype.sum_bijective e ⟨hinj, hsurj⟩ _ _ fun i => ?_
  have h5 : g * x * cos ϖ (i.map Subtype.val) = g * cos ϖ' ((e i).map Subtype.val) *
      ((cos ϖ' ((e i).map Subtype.val))⁻¹ * (x * cos ϖ (i.map Subtype.val))) := by group
  rw [h5, hf _ (he i)]

theorem heckeSum_invariant : Ad3.R.C0 := by
  intro F _ _ _ _ _ _ _ _ f hf ϖ B ϖ' B' hR hR' x hx g
  exact sum_eq hR hR' f hf hx g

end GlobalTheory.CompanionTheory.HeckeCosets
