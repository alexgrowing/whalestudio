import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardLiftMatrix

namespace Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame

open Matrix

section Lift

variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem isUnit_of_map (π : A →+* A') (hπ : Function.Surjective π)
    (h2 : ∀ a ∈ RingHom.ker π, ∀ b ∈ RingHom.ker π, a * b = 0) {u : A} (hu : IsUnit (π u)) :
    IsUnit u := by
  obtain ⟨w, hw⟩ := hu
  obtain ⟨z, hz⟩ := hπ (↑w⁻¹ : A')
  have hker : u * z - 1 ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, hz, ← hw, Units.mul_inv, sub_self]
  have hsq := h2 _ hker _ hker
  have h1 : u * (z * (1 - (u * z - 1))) = 1 := by linear_combination -hsq
  exact ⟨⟨u, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

theorem card_lift_unimod [Finite A] (π : A →+* A') (hπ : Function.Surjective π)
    (hπs : ∀ a, π (star a) = star (π a))
    (h2 : ∀ a ∈ RingHom.ker π, ∀ b ∈ RingHom.ker π, a * b = 0) {θ e : A}
    (he : (θ - star θ) * e = 1) (H : Matrix m m A) (hH : Hᴴ = H) (hu : IsUnit H.det) :
    Nat.card {X : Matrix m m A // Xᴴ * H * X = H} * Nat.card (HermitianSublattices.hermSub m (RingHom.ker π)) =
      Nat.card (HermitianSublattices.entSub m m (RingHom.ker π)) *
        Nat.card {X' : Matrix m m A' // X'ᴴ * (H.map π) * X' = H.map π} := by
  classical
  have hJs : ∀ a ∈ RingHom.ker π, star a ∈ RingHom.ker π := fun a ha => by
    rw [RingHom.mem_ker] at ha ⊢
    rw [hπs, ha, star_zero]
  have h' : star e * (star θ - θ) = 1 := by
    have h3 := congrArg star he
    rwa [star_mul, star_sub, star_star, star_one] at h3
  have hs : star e = -e := by
    calc star e = star e * ((θ - star θ) * e) := by rw [he, mul_one]
      _ = -(star e * (star θ - θ)) * e := by ring
      _ = -e := by rw [h']; ring
  have hc : θ * e + star (θ * e) = 1 := by
    rw [star_mul, hs]
    linear_combination he
  have key := HermitianSublattices.card_lift_matrix π hπ hπs (RingHom.ker π) hJs h2 H hH H hH (fun _ => True)
    (fun _ _ _ => Iff.rfl) (fun X _ hX S hS => by
      have hXm : (Xᴴ * H * X).map π = H.map π := by
        ext i j
        have h4 := hX i j
        rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero] at h4
        simpa [Matrix.map_apply] using h4
      have hdetπ : IsUnit (π (Xᴴ * H * X).det) := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, hXm, ← RingHom.mapMatrix_apply,
          ← RingHom.map_det]
        exact hu.map π
      rw [Matrix.det_mul, Matrix.det_mul, map_mul] at hdetπ
      have hXu : IsUnit X.det := isUnit_of_map π hπ h2 (isUnit_of_mul_isUnit_right hdetπ)
      have hXHu : IsUnit (Xᴴ * H).det := by
        rw [Matrix.det_mul, Matrix.det_conjTranspose]
        exact hXu.star.mul hu
      refine ⟨(Xᴴ * H)⁻¹ * ((θ * e) • S), ?_, ?_⟩
      · rw [HermitianSublattices.mem_entSub]
        intro i j
        rw [Matrix.mul_apply]
        refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ?_
        rw [Matrix.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_left _ _ ((HermitianSublattices.mem_hermSub.1 hS).2 k j)
      · have hZ : Xᴴ * H * ((Xᴴ * H)⁻¹ * ((θ * e) • S)) = (θ * e) • S := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXHu, Matrix.one_mul]
        have hZ' : ((Xᴴ * H)⁻¹ * ((θ * e) • S))ᴴ * H * X = star (θ * e) • S := by
          have h5 : ((Xᴴ * H)⁻¹ * ((θ * e) • S))ᴴ * H * X =
              (Xᴴ * H * ((Xᴴ * H)⁻¹ * ((θ * e) • S)))ᴴ := by
            simp only [Matrix.conjTranspose_mul, hH, Matrix.conjTranspose_conjTranspose,
              Matrix.mul_assoc]
          rw [h5, hZ, Matrix.conjTranspose_smul, (HermitianSublattices.mem_hermSub.1 hS).1]
        rw [hZ, hZ', ← add_smul, hc, one_smul])
  have e1 : Nat.card {X : Matrix m m A // (fun _ => True) (X.map π) ∧ Xᴴ * H * X = H} =
      Nat.card {X : Matrix m m A // Xᴴ * H * X = H} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun X => by simp)
  have e2 : Nat.card {X' : Matrix m m A' // (fun _ => True) X' ∧ X'ᴴ * (H.map π) * X' = H.map π} =
      Nat.card {X' : Matrix m m A' // X'ᴴ * (H.map π) * X' = H.map π} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun X => by simp)
  rw [e1, e2] at key
  exact key

theorem card_lift_unimod' [Finite A] (π : A →+* A') (hπ : Function.Surjective π)
    (hπs : ∀ a, π (star a) = star (π a))
    (h2 : ∀ a ∈ RingHom.ker π, ∀ b ∈ RingHom.ker π, a * b = 0) {θ e : A}
    (he : (θ - star θ) * e = 1) (H : Matrix m m A) (hH : Hᴴ = H) (hu : IsUnit H.det) (q : ℕ)
    (hq : Nat.card (RingHom.ker π) = q ^ 2) :
    Nat.card {X : Matrix m m A // Xᴴ * H * X = H} =
      q ^ (Fintype.card m ^ 2) * Nat.card {X' : Matrix m m A' // X'ᴴ * (H.map π) * X' = H.map π} := by
  have h1 := card_lift_unimod π hπ hπs h2 he H hH hu
  have hJ : ∀ a ∈ RingHom.ker π, star a ∈ RingHom.ker π := fun a ha => by
    rw [RingHom.mem_ker] at ha ⊢
    rw [hπs, ha, star_zero]
  have hE : Nat.card (HermitianSublattices.entSub m m (RingHom.ker π)) = q ^ (2 * Fintype.card m ^ 2) := by
    rw [HermitianSublattices.card_entSub, hq, ← pow_mul]
    ring
  have hHs : Nat.card (HermitianSublattices.hermSub m (RingHom.ker π)) = q ^ (Fintype.card m ^ 2) := by
    have h3 := HermitianSublattices.card_hermSub_sq (r := m) hJ he
    rw [hE] at h3
    have e2 : q ^ (2 * Fintype.card m ^ 2) = (q ^ (Fintype.card m ^ 2)) ^ 2 := by
      rw [← pow_mul]
      ring
    rw [e2] at h3
    exact Nat.pow_left_injective two_ne_zero h3
  rw [hHs, hE] at h1
  have hq0 : 0 < q := by
    have h4 : 0 < Nat.card (RingHom.ker π) := Nat.card_pos
    rw [hq] at h4
    exact Nat.pos_of_ne_zero fun h => by simp [h] at h4
  have e3 : q ^ (2 * Fintype.card m ^ 2) = q ^ (Fintype.card m ^ 2) * q ^ (Fintype.card m ^ 2) := by
    rw [← pow_add]
    ring
  rw [e3] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hq0 _) (by rw [h1]; ring)

end Lift

end Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame
