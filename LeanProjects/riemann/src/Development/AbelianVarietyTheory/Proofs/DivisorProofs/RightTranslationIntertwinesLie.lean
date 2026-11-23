import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad

open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TorFin.RightTr

variable {n : ℕ} {G : Type} [Group G] {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}

theorem isUni_exp (hJ : IsUnit J.det) {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsSkew J X) :
    IsUni J (NormedSpace.exp X) := by
  have h1 : Xᴴ = J * (-X) * J⁻¹ := by
    rw [mul_neg, ← eq_neg_of_add_eq_zero_left hX, mul_nonsing_inv_cancel_right _ _ hJ]
  change (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det J).2 hJ),
    nonsing_inv_mul_cancel_right _ _ hJ, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left,
    neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem isSkew_smul {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (t : ℝ) : IsSkew J (t • Z) := by
  unfold IsSkew at *
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hZ, smul_zero]

theorem isUnit_det_of_isUni (hJ : IsUnit J.det) {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) : IsUnit u.det := by
  have h : (uᴴ * J * u).det = J.det := congrArg Matrix.det hu
  rw [det_mul] at h
  exact isUnit_of_mul_isUnit_right (h ▸ hJ)

theorem isSkew_conj_of {u Z W : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) (h : W * u = u * Z) :
    uᴴ * (Wᴴ * J + J * W) * u = Zᴴ * J + J * Z := by
  have h' : uᴴ * Wᴴ = Zᴴ * uᴴ := by rw [← conjTranspose_mul, h, conjTranspose_mul]
  unfold IsUni at hu
  calc uᴴ * (Wᴴ * J + J * W) * u = (uᴴ * Wᴴ) * J * u + uᴴ * J * (W * u) := by noncomm_ring
    _ = Zᴴ * (uᴴ * J * u) + (uᴴ * J * u) * Z := by rw [h, h']; noncomm_ring
    _ = _ := by rw [hu]

theorem isSkew_inv_conj (hJ : IsUnit J.det) {u Z : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) (hZ : IsSkew J Z) :
    IsSkew J (u⁻¹ * Z * u) := by
  have hd := isUnit_det_of_isUni hJ hu
  have := isSkew_conj_of (W := Z) (Z := u⁻¹ * Z * u) hu
    (by rw [mul_assoc, mul_nonsing_inv_cancel_left _ _ hd])
  unfold IsSkew at *
  rw [← this, hZ, mul_zero, zero_mul]

theorem isSkew_conj (hJ : IsUnit J.det) {u Z : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) (hZ : IsSkew J Z) :
    IsSkew J (u * Z * u⁻¹) := by
  have hd := isUnit_det_of_isUni hJ hu
  have hd' : IsUnit uᴴ.det := by rw [det_conjTranspose]; exact hd.star
  have := isSkew_conj_of (W := u * Z * u⁻¹) (Z := Z) hu
    (by rw [nonsing_inv_mul_cancel_right _ _ hd])
  unfold IsSkew at *
  rw [hZ] at this
  have h2 := congrArg (fun M => (uᴴ)⁻¹ * M * u⁻¹) this
  simp only [mul_zero, zero_mul] at h2
  rwa [mul_assoc uᴴ, nonsing_inv_mul_cancel_left _ _ hd', mul_nonsing_inv_cancel_right _ _ hd] at h2

theorem lineOf_zero (hs : IsMulOn J s) (Z : Matrix (Fin n) (Fin n) ℂ) : lineOf s Z 0 = 1 := by
  have h1 : IsUni J 1 := by simp [IsUni]
  have := hs 1 1 h1 h1
  rw [mul_one] at this
  rw [lineOf, zero_smul, NormedSpace.exp_zero]
  exact left_eq_mul.1 this

theorem lineOf_mul (hJ : IsUnit J.det) (hs : IsMulOn J s) {u : Matrix (Fin n) (Fin n) ℂ} {b : G} (hu : IsUni J u)
    (hb : ∀ v, IsUni J v → b * s v = s v * b) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (t : ℝ) :
    lineOf s Z t * (s u * b) = (s u * b) * lineOf s (u⁻¹ * Z * u) t := by
  have hd := isUnit_det_of_isUni hJ hu
  have h1 := isUni_exp hJ (isSkew_smul hZ t)
  have h2 := isUni_exp hJ (isSkew_smul (isSkew_inv_conj hJ hu hZ) t)
  have e : t • (u⁻¹ * Z * u) = u⁻¹ * (t • Z) * u := by rw [mul_smul_comm, smul_mul_assoc]
  unfold lineOf
  rw [mul_assoc (s u), hb _ h2, ← mul_assoc, ← mul_assoc, ← hs _ _ h1 hu, ← hs _ _ hu h2, e,
    Matrix.exp_conj' _ _ ((isUnit_iff_isUnit_det u).2 hd), mul_assoc u⁻¹, mul_nonsing_inv_cancel_left _ _ hd]

theorem prod_ofFn_mul (c : G) : ∀ (k : ℕ) (x y : Fin k → G), (∀ i, x i * c = c * y i) →
    (List.ofFn x).prod * c = c * (List.ofFn y).prod := by
  intro k
  induction k with
  | zero => intro x y _; simp
  | succ k ih =>
    intro x y h
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      ih _ _ (fun i => h i.succ), ← mul_assoc, h, mul_assoc]

theorem exists_skew_add (hH : Jᴴ = J) (hJ : IsUnit J.det) (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ A B, IsSkew J A ∧ IsSkew J B ∧ Y = A + Complex.I • B := by
  have e1 : (J⁻¹ * Yᴴ * J)ᴴ * J = J * Y := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hH,
      ← mul_assoc, nonsing_inv_mul_cancel_right _ _ hJ]
  have e2 : J * (J⁻¹ * Yᴴ * J) = Yᴴ * J := by
    rw [mul_assoc, mul_nonsing_inv_cancel_left _ _ hJ]
  generalize J⁻¹ * Yᴴ * J = Y' at e1 e2
  refine ⟨(1 / 2 : ℂ) • (Y - Y'), (-Complex.I / 2) • (Y + Y'), ?_, ?_, ?_⟩
  · unfold IsSkew
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [conjTranspose_smul, this, conjTranspose_sub, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, e1, e2]
    module
  · unfold IsSkew
    have : star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2) := by simp; ring
    rw [conjTranspose_smul, this, conjTranspose_add, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, e1, e2]
    module
  · have : Complex.I * (-Complex.I / 2) = 1 / 2 := by
      linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
    rw [smul_smul, this]
    module

theorem exists_rightTranslation : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ (u : Matrix (Fin n) (Fin n) ℂ) (b : G), IsUni J u → (∀ v, IsUni J v → b * s v = s v * b) → ∃ r : Module.End ℂ (smLoc J s), (∀ (f : smLoc J s) (g : G), (r f).1 g = f.1 (g * (s u * b))) ∧ ∀ Y, r * ρ Y = ρ (u * Y * u⁻¹) * r := by
  intro n G _ J s hH hJ hs ρ hρ u b hu hb
  have hd := isUnit_det_of_isUni hJ hu
  let r : Module.End ℂ (smLoc J s) :=
    { toFun := fun f => ⟨fun g => f.1 (g * (s u * b)), fun k Z hZ g => by
        have h := f.2 k (fun i => u⁻¹ * Z i * u) (fun i => isSkew_inv_conj hJ hu (hZ i)) (g * (s u * b))
        convert h using 2 with t
        beta_reduce
        rw [mul_assoc g, mul_assoc g, prod_ofFn_mul _ _ _ _ fun i => lineOf_mul hJ hs hu hb (hZ i) (t i)]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have key : ∀ Z, IsSkew J Z → r * ρ Z = ρ (u * Z * u⁻¹) * r := by
    intro Z hZ
    refine LinearMap.ext fun f => Subtype.ext (funext fun g => ?_)
    have h1 := hρ Z hZ f (g * (s u * b)) 0
    have h2 := hρ _ (isSkew_conj hJ hu hZ) (r f) g 0
    rw [lineOf_zero hs, mul_one] at h1 h2
    refine h1.unique ?_
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
    change f.1 (g * (s u * b) * lineOf s Z τ) = f.1 (g * lineOf s (u * Z * u⁻¹) τ * (s u * b))
    rw [mul_assoc g (lineOf _ _ _), lineOf_mul hJ hs hu hb (isSkew_conj hJ hu hZ), ← mul_assoc u⁻¹,
      nonsing_inv_mul_cancel_right _ _ hd, nonsing_inv_mul_cancel_left _ _ hd, mul_assoc g]
  refine ⟨r, fun _ _ => rfl, fun Y => ?_⟩
  obtain ⟨A, B, hA, hB, rfl⟩ := exists_skew_add hH hJ Y
  rw [mul_add u, add_mul, mul_smul_comm, smul_mul_assoc, map_add, map_add, map_smul, map_smul, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, key A hA, key B hB]

end GlobalTheory.TorFin.RightTr
