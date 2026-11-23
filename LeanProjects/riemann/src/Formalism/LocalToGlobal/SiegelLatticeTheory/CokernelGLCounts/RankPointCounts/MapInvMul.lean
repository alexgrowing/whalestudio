import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CloseOfTarget

noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount

section Comp

variable {E : Type*} [Field E] {K : Type*} [CommRing K] (ψ : E →+* K) {r : ℕ}

def cP (cv : Fin (r + 1) → K) (L₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal cv * L₁.map ψ

def cP' (cv' : Fin (r + 1) → K) (L₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  L₁⁻¹.map ψ * Matrix.diagonal cv'

def cQ (cv : Fin (r + 1) → K) (U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  U₁.map ψ * Matrix.diagonal cv

def cQ' (cv' : Fin (r + 1) → K) (U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.diagonal cv' * U₁⁻¹.map ψ

theorem diag_one {cv cv' : Fin (r + 1) → K} (h : ∀ a, cv a * cv' a = 1) :
    Matrix.diagonal cv * Matrix.diagonal cv' = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg Matrix.diagonal (funext h)

theorem map_one' : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E).map ψ = 1 := Matrix.map_one _ ψ.map_zero ψ.map_one

theorem map_inv_mul {L : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : L.det = 1) : L⁻¹.map ψ * L.map ψ = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (by rw [h]; exact isUnit_one), map_one']

theorem map_mul_inv {L : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : L.det = 1) : L.map ψ * L⁻¹.map ψ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (by rw [h]; exact isUnit_one), map_one']

theorem mono_map (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) :
    (mono σ ν).map ψ = mono σ (fun a => ψ (ν a)) := by
  ext a b
  simp only [Matrix.map_apply, mono, Matrix.of_apply]
  split_ifs <;> simp

theorem inv_eq_map {x : E} (hx : x ≠ 0) : Ring.inverse (ψ x) = ψ x⁻¹ := by
  have h1 : ψ x * ψ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  calc Ring.inverse (ψ x) = Ring.inverse (ψ x) * (ψ x * ψ x⁻¹) := by rw [h1, mul_one]
    _ = ψ x⁻¹ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ ⟨⟨ψ x, ψ x⁻¹, h1, by rw [mul_comm]; exact h1⟩, rfl⟩, one_mul]

theorem hcv'_of {cv cv' : Fin (r + 1) → K} (hcv : ∀ a, cv a * cv' a = 1) : ∀ a, cv' a * cv a = 1 :=
  fun a => by rw [mul_comm]; exact hcv a

variable {cv cv' : Fin (r + 1) → K} (hcv : ∀ a, cv a * cv' a = 1) {L₁ U₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
include hcv hL₁ hU₁

theorem conjPrime_conjPrime₂ : cP ψ cv L₁ * cP' ψ cv' L₁ = 1 := by
  unfold cP cP'
  rw [show Matrix.diagonal cv * L₁.map ψ * (L₁⁻¹.map ψ * Matrix.diagonal cv') =
      Matrix.diagonal cv * (L₁.map ψ * L₁⁻¹.map ψ) * Matrix.diagonal cv' by simp only [Matrix.mul_assoc],
    map_mul_inv ψ (det_lo hL₁), Matrix.mul_one, diag_one hcv]

theorem cP'_cP : cP' ψ cv' L₁ * cP ψ cv L₁ = 1 := by
  unfold cP cP'
  rw [show L₁⁻¹.map ψ * Matrix.diagonal cv' * (Matrix.diagonal cv * L₁.map ψ) =
      L₁⁻¹.map ψ * (Matrix.diagonal cv' * Matrix.diagonal cv) * L₁.map ψ by simp only [Matrix.mul_assoc],
    diag_one (hcv'_of hcv), Matrix.mul_one, map_inv_mul ψ (det_lo hL₁)]

theorem cQ_cQ' : cQ ψ cv U₁ * cQ' ψ cv' U₁ = 1 := by
  unfold cQ cQ'
  rw [show U₁.map ψ * Matrix.diagonal cv * (Matrix.diagonal cv' * U₁⁻¹.map ψ) =
      U₁.map ψ * (Matrix.diagonal cv * Matrix.diagonal cv') * U₁⁻¹.map ψ by simp only [Matrix.mul_assoc],
    diag_one hcv, Matrix.mul_one, map_mul_inv ψ (det_up hU₁)]

theorem cQ'_cQ : cQ' ψ cv' U₁ * cQ ψ cv U₁ = 1 := by
  unfold cQ cQ'
  rw [show Matrix.diagonal cv' * U₁⁻¹.map ψ * (U₁.map ψ * Matrix.diagonal cv) =
      Matrix.diagonal cv' * (U₁⁻¹.map ψ * U₁.map ψ) * Matrix.diagonal cv by simp only [Matrix.mul_assoc],
    map_inv_mul ψ (det_up hU₁), Matrix.mul_one, diag_one (hcv'_of hcv)]

theorem cP_lo {k : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hk : IsLo k) : IsLo (cP' ψ cv' L₁ * k * cP ψ cv L₁) := by
  unfold cP cP'
  rw [show L₁⁻¹.map ψ * Matrix.diagonal cv' * k * (Matrix.diagonal cv * L₁.map ψ) =
      L₁⁻¹.map ψ * (Matrix.diagonal cv' * k * Matrix.diagonal cv) * L₁.map ψ by simp only [Matrix.mul_assoc]]
  exact isLo_mul (isLo_mul (isLo_map ψ (isLo_inv hL₁)) (isLo_conj hk cv' cv (hcv'_of hcv))) (isLo_map ψ hL₁)

theorem cQ_up {k : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hk : IsUp k) : IsUp (cQ ψ cv U₁ * k * cQ' ψ cv' U₁) := by
  unfold cQ cQ'
  rw [show U₁.map ψ * Matrix.diagonal cv * k * (Matrix.diagonal cv' * U₁⁻¹.map ψ) =
      U₁.map ψ * (Matrix.diagonal cv * k * Matrix.diagonal cv') * U₁⁻¹.map ψ by simp only [Matrix.mul_assoc]]
  exact isUp_mul (isUp_mul (isUp_map ψ hU₁) (isUp_conj hk cv cv' hcv)) (isUp_map ψ (isUp_inv hU₁))

theorem cW_eq (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) (s e : K) :
    s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r =
      s • (cP ψ cv L₁ * mono σ (fun a => ψ (ν a)) * cQ ψ cv U₁) - e • Ecorner r := by
  unfold cP cQ
  rw [Matrix.map_mul, Matrix.map_mul, mono_map]
  simp only [Matrix.mul_assoc]

theorem cG_eq (X' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    cP' ψ cv' L₁ * (Matrix.diagonal cv * (L₁ * X' * L₁⁻¹).map ψ * Matrix.diagonal cv') * cP ψ cv L₁ = X'.map ψ := by
  have e : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Matrix.diagonal cv' * (Matrix.diagonal cv * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, diag_one (hcv'_of hcv), Matrix.one_mul]
  have f : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) K, L₁⁻¹.map ψ * (L₁.map ψ * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, map_inv_mul ψ (det_lo hL₁), Matrix.one_mul]
  unfold cP cP'
  rw [Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc, e, f, map_inv_mul ψ (det_lo hL₁), Matrix.mul_one]

theorem conj_mul {P P' A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hPP : P * P' = 1) :
    P' * (A * B) * P = (P' * A * P) * (P' * B * P) := by
  rw [show P' * A * P * (P' * B * P) = P' * A * (P * P') * B * P by simp only [Matrix.mul_assoc], hPP,
    Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem comp_target {σ : Fin (r + 1) → Fin (r + 1)} (hσ : ∀ a, σ (σ a) = a) {ν : Fin (r + 1) → E}
    (hν : ∀ a, ν a ≠ 0) {s e : K} (hs : IsUnit s) {kL kR : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hkL : IsLo kL)
    (hkR : IsUp kR)
    (hk : kL * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * kR =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) :
    IsLo (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ ∧ (∀ i j, σ j < σ i → (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ i j = 0) ∧
      (cP' ψ cv' L₁ * kL * cP ψ cv L₁) * (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹ = 1 := by
  have hν' : ∀ x, IsUnit (ψ (ν x)) := fun x => by
    have hu : ψ (ν x) * ψ (ν x)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ (hν x), map_one]
    exact ⟨⟨ψ (ν x), ψ (ν x)⁻¹, hu, by rw [mul_comm, hu]⟩, rfl⟩
  rw [cW_eq ψ hcv hL₁ hU₁] at hk
  have hfix := stab_core hs (cP'_cP ψ hcv hL₁ hU₁) (cQ_cQ' ψ hcv hL₁ hU₁) hkL hkR hk
  exact fix_inv hσ hν' (cP_lo ψ hcv hL₁ hU₁ hkL) (cQ_up ψ hcv hL₁ hU₁ hkR) hfix

theorem comp_main {σ : Fin (r + 1) → Fin (r + 1)} (hσ : ∀ a, σ (σ a) = a) {ν : Fin (r + 1) → E}
    (hν : ∀ a, ν a ≠ 0) {s e : K} (hs : IsUnit s) {I : Subring K} {kL kR a b : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hkL : IsLo kL) (hkR : IsUp kR)
    (hk : kL * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * kR =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r)
    (ha : IsLo a) (hb : IsUp b)
    (hab : a * (s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r) * b =
      s • (Matrix.diagonal cv * (L₁ * mono σ ν * U₁).map ψ * Matrix.diagonal cv) - e • Ecorner r)
    {X' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (haX : a = kL * (Matrix.diagonal cv * (L₁ * X' * L₁⁻¹).map ψ * Matrix.diagonal cv'))
    {t c : K} (ht : t ∈ I) (hc : c ∈ I) (hbν : ∀ a, t * ψ (ν a) ∈ I) (hbν' : ∀ a, t * ψ (ν a)⁻¹ ∈ I)
    (bP : ∀ i j, t * cP ψ cv L₁ i j ∈ I) (bP' : ∀ i j, t * cP' ψ cv' L₁ i j ∈ I)
    (bQ : ∀ i j, t * cQ ψ cv U₁ i j ∈ I) (bQ' : ∀ i j, t * cQ' ψ cv' U₁ i j ∈ I)
    (bx : ∀ i j, t * (cP' ψ cv' L₁ * kL * cP ψ cv L₁) i j ∈ I)
    (hG : EntIn (lat I (t * (t * (t * (t * (t * c)))))) (X'.map ψ - (cP' ψ cv' L₁ * kL * cP ψ cv L₁)⁻¹)) :
    EntIn (lat I c) (a - 1) ∧ EntIn (lat I c) (b - 1) := by
  have hν' : ∀ x, IsUnit (ψ (ν x)) := fun x => by
    have hu : ψ (ν x) * ψ (ν x)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ (hν x), map_one]
    exact ⟨⟨ψ (ν x), ψ (ν x)⁻¹, hu, by rw [mul_comm, hu]⟩, rfl⟩
  have hinv : ∀ x, t * Ring.inverse (ψ (ν x)) ∈ I := fun x => by
    rw [inv_eq_map ψ (hν x)]
    exact hbν' x
  have hT := (comp_target ψ hcv hL₁ hU₁ hσ hν hs hkL hkR hk).2.2
  have hA : cP' ψ cv' L₁ * a * cP ψ cv L₁ = (cP' ψ cv' L₁ * kL * cP ψ cv L₁) * X'.map ψ := by
    rw [haX, conj_mul hcv hL₁ hU₁ (conjPrime_conjPrime₂ ψ hcv hL₁ hU₁), cG_eq ψ hcv hL₁ hU₁]
  have hE := close_of_target hT bx hG
  rw [← hA] at hE
  rw [cW_eq ψ hcv hL₁ hU₁] at hab
  exact close_pair hσ hν' ht hc hbν hinv (conjPrime_conjPrime₂ ψ hcv hL₁ hU₁) (cP'_cP ψ hcv hL₁ hU₁)
    (cQ_cQ' ψ hcv hL₁ hU₁) (cQ'_cQ ψ hcv hL₁ hU₁) bP bP' bQ bQ' hs ha hb hab (cP_lo ψ hcv hL₁ hU₁ ha)
    (cQ_up ψ hcv hL₁ hU₁ hb) hE

end Comp

end Formalism.L2.SG.Pf.TupGlobApprox
