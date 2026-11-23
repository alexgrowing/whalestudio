import Mathlib
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

open Matrix

noncomputable section

namespace PI.MirrorSection₂

open Formalism.FourierDecayAlt.C2

variable {m : ℕ}

theorem ut_mul {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ UTset m) (hb : b ∈ UTset m) : a * b ∈ UTset m := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l < i
    · rw [ha.1 i l hl, zero_mul]
    · rw [hb.1 l j (lt_of_lt_of_le hji (not_lt.mp hl)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [ha.2, hb.2, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [ha.1 i l h, zero_mul]
      · rw [hb.1 l i h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem lt_mul {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ LTset m) (hb : b ∈ LTset m) : a * b ∈ LTset m := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : i < l
    · rw [ha.1 i l hl, zero_mul]
    · rw [hb.1 l j (lt_of_le_of_lt (not_lt.mp hl) hji), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [ha.2, hb.2, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hb.1 l i h, mul_zero]
      · rw [ha.1 i l h, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem det_ut {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) : u.det = 1 := by
  rw [det_of_upperTriangular (fun i j h => hu.1 i j h)]
  simp [hu.2]

theorem ut_conjTranspose {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) : uᴴ ∈ LTset m := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conjTranspose_apply, hu.1 j i hij, star_zero]
  · rw [conjTranspose_apply, hu.2, star_one]

theorem lt_conjTranspose {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ LTset m) : lᴴ ∈ UTset m := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conjTranspose_apply, hl.1 j i hij, star_zero]
  · rw [conjTranspose_apply, hl.2, star_one]

theorem ut_inv {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) :
    u * u⁻¹ = 1 ∧ u⁻¹ * u = 1 ∧ u⁻¹ ∈ UTset m := by
  have hd : IsUnit u.det := by rw [det_ut hu]; exact isUnit_one
  have h1 : u * u⁻¹ = 1 := mul_nonsing_inv u hd
  have h2 : u⁻¹ * u = 1 := nonsing_inv_mul u hd
  have hbt : BlockTriangular u id := fun i j h => hu.1 i j h
  haveI := u.invertibleOfIsUnitDet hd
  have hbti : BlockTriangular u⁻¹ id := blockTriangular_inv_of_blockTriangular hbt
  refine ⟨h1, h2, fun i j hji => hbti hji, fun i => ?_⟩
  have e := congrFun (congrFun h1 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hu.2, one_mul, Matrix.one_apply_eq] at e
  · exact e
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hu.1 i l h, zero_mul]
    · rw [hbti h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem lt_inv {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ LTset m) :
    l * l⁻¹ = 1 ∧ l⁻¹ * l = 1 ∧ l⁻¹ ∈ LTset m := by
  have hu := ut_inv (lt_conjTranspose hl)
  have hd : IsUnit l.det := by
    have := det_ut (lt_conjTranspose hl)
    rw [det_conjTranspose] at this
    have h2 : l.det = 1 := by simpa using congrArg star this
    rw [h2]; exact isUnit_one
  refine ⟨mul_nonsing_inv l hd, nonsing_inv_mul l hd, ?_⟩
  have := ut_conjTranspose hu.2.2
  rwa [conjTranspose_nonsing_inv, conjTranspose_conjTranspose] at this

theorem ut_lt_eq_one {x : Matrix (Fin m) (Fin m) ℂ} (hu : x ∈ UTset m) (hl : x ∈ LTset m) : x = 1 := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · rw [hl.1 i j h, Matrix.one_apply_ne (ne_of_lt h)]
  · subst h; rw [hu.2, Matrix.one_apply_eq]
  · rw [hu.1 i j h, Matrix.one_apply_ne (ne_of_gt h)]

theorem monomialMatrix_conjTranspose (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) :
    (monoP w d)ᴴ = monoP w.symm (fun a => star (d (w.symm a))) := by
  ext i a
  simp only [conjTranspose_apply, monoP, of_apply]
  by_cases h : a = w i
  · rw [if_pos h, if_pos (by rw [h, Equiv.symm_apply_apply])]
    rw [h, Equiv.symm_apply_apply]
  · rw [if_neg h, star_zero, if_neg]
    intro h'
    exact h (by rw [h', Equiv.apply_symm_apply])

theorem isMonomial_conjTranspose {P : Matrix (Fin m) (Fin m) ℂ} (hP : IsMonomial P) : IsMonomial Pᴴ := by
  obtain ⟨w, d, hd, rfl⟩ := hP
  exact ⟨w.symm, fun a => star (d (w.symm a)), fun a => by simpa using hd (w.symm a),
    monomialMatrix_conjTranspose w d⟩

theorem split_unique {P : Matrix (Fin m) (Fin m) ℂ} (hP : IsUnit P.det)
    {a₁ a₂ v₁ v₂ : Matrix (Fin m) (Fin m) ℂ}
    (ha₁ : P * a₁ * P⁻¹ ∈ LTset m) (ha₂ : P * a₂ * P⁻¹ ∈ LTset m)
    (hv₁ : P * v₁ * P⁻¹ ∈ UTset m) (hv₂ : P * v₂ * P⁻¹ ∈ UTset m)
    (h : a₁ * v₁ = a₂ * v₂) : a₁ = a₂ := by
  set A₁ := P * a₁ * P⁻¹
  set A₂ := P * a₂ * P⁻¹
  set V₁ := P * v₁ * P⁻¹
  set V₂ := P * v₂ * P⁻¹
  have hPP : P⁻¹ * P = 1 := nonsing_inv_mul P hP
  have hPP' : P * P⁻¹ = 1 := mul_nonsing_inv P hP
  have hAV : A₁ * V₁ = A₂ * V₂ := by
    have e1 : A₁ * V₁ = P * (a₁ * v₁) * P⁻¹ := by
      simp only [A₁, V₁, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]
    have e2 : A₂ * V₂ = P * (a₂ * v₂) * P⁻¹ := by
      simp only [A₂, V₂, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]
    rw [e1, e2, h]
  have iA := lt_inv ha₂
  have iV := ut_inv hv₁
  have hx : A₂⁻¹ * A₁ = V₂ * V₁⁻¹ := by
    calc A₂⁻¹ * A₁ = A₂⁻¹ * (A₁ * V₁) * V₁⁻¹ := by
          rw [Matrix.mul_assoc A₂⁻¹, Matrix.mul_assoc A₁, iV.1, Matrix.mul_one]
      _ = A₂⁻¹ * (A₂ * V₂) * V₁⁻¹ := by rw [hAV]
      _ = V₂ * V₁⁻¹ := by rw [← Matrix.mul_assoc A₂⁻¹, iA.2.1, Matrix.one_mul]
  have h1 : A₂⁻¹ * A₁ = 1 := ut_lt_eq_one (hx ▸ ut_mul hv₂ iV.2.2) (lt_mul iA.2.2 ha₁)
  have hA : A₁ = A₂ := by
    calc A₁ = A₂ * (A₂⁻¹ * A₁) := by rw [← Matrix.mul_assoc, iA.1, Matrix.one_mul]
      _ = A₂ := by rw [h1, Matrix.mul_one]
  have back : ∀ x : Matrix (Fin m) (Fin m) ℂ, x = P⁻¹ * (P * x * P⁻¹) * P := by
    intro x
    simp only [Matrix.mul_assoc]
    rw [hPP, Matrix.mul_one, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  rw [back a₁, back a₂]
  exact congrArg (fun y => P⁻¹ * y * P) hA

theorem split_exists (hLS : LowSplit) {P : Matrix (Fin m) (Fin m) ℂ} (hP : IsMonomial P) (hPd : IsUnit P.det)
    {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) :
    ∃ a v : Matrix (Fin m) (Fin m) ℂ, a ∈ UTset m ∧ v ∈ UTset m ∧ P * a * P⁻¹ ∈ LTset m ∧
      P * v * P⁻¹ ∈ UTset m ∧ u = a * v := by
  obtain ⟨⟨l₁, l₂⟩, ⟨h1, h2, he⟩, -⟩ := hLS m Pᴴ (isMonomial_conjTranspose hP) uᴴ (ut_conjTranspose hu)
  have key : ∀ l : Matrix (Fin m) (Fin m) ℂ, ((Pᴴ)⁻¹ * l * Pᴴ)ᴴ = P * lᴴ * P⁻¹ := by
    intro l
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv,
      conjTranspose_conjTranspose, Matrix.mul_assoc]
  refine ⟨l₂ᴴ, l₁ᴴ, lt_conjTranspose h2.1, lt_conjTranspose h1.1, ?_, ?_, ?_⟩
  · rw [← key]; exact ut_conjTranspose h2.2
  · rw [← key]; exact lt_conjTranspose h1.2
  · have := congrArg conjTranspose he
    simp only [conjTranspose_conjTranspose, conjTranspose_mul] at this
    exact this

end PI.MirrorSection₂
