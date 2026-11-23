import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical AddMonoidAlgebra Matrix

namespace Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2

theorem sum_Icc_telescope (f : ℤ → ℂ) (lo hi : ℤ) (h : lo ≤ hi + 1) :
    ∑ k ∈ Finset.Icc lo hi, (f k - f (k + 1)) = f lo - f (hi + 1) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  have e : ∀ i : ℕ, f (lo + (i : ℤ) + 1) = f (lo + ((i + 1 : ℕ) : ℤ)) := fun i => by
    push_cast; ring_nf
  simp_rw [e]
  rw [Finset.sum_range_sub' (fun i : ℕ => f (lo + (i : ℤ)))]
  simp only [Nat.cast_zero, add_zero]
  rw [Int.toNat_of_nonneg (by omega)]
  ring_nf

theorem evalAt_schur_two (w : Fin 2 → ℂˣ) (l : Fin 2 → ℤ) (hl : l 1 ≤ l 0) :
    evalAt w (schur l) =
      ∑ j ∈ Finset.Icc (-l 0) (-l 1), ((w 0 : ℂ)) ^ (-j) * ((w 1 : ℂ)) ^ (l 0 + l 1 + j) := by
  set P : LaurentRing 2 := ∑ j ∈ Finset.Icc (-l 0) (-l 1), monomial ![-j, l 0 + l 1 + j] with hP
  have hev : ∀ v : Fin 2 → ℂˣ, evalAt v P =
      ∑ j ∈ Finset.Icc (-l 0) (-l 1), ((v 0 : ℂ)) ^ (-j) * ((v 1 : ℂ)) ^ (l 0 + l 1 + j) := by
    intro v
    simp [hP, map_sum, evalAt_single, monomialChar_apply, Fin.prod_univ_two,
      Units.val_zpow_eq_zpow_val]
  have key : schur l = P := by
    refine mul_left_cancel₀ (alternant_staircase_ne_zero (n := 2)) ?_
    rw [alternant_mul_schur]
    refine eq_of_forall_evalAt fun v => ?_
    rw [map_mul, hev, alternant_eq_det, alternant_eq_det, AlgHom.map_det, AlgHom.map_det,
      det_fin_two, det_fin_two]
    simp [AlgHom.mapMatrix_apply, evalAt_single, monomialChar_apply, Fin.prod_univ_two, staircase,
      Units.val_zpow_eq_zpow_val, Pi.single_apply]
    set x : ℂ := (v 0 : ℂ)
    set y : ℂ := (v 1 : ℂ)
    have hx : x ≠ 0 := Units.ne_zero _
    have hy : y ≠ 0 := Units.ne_zero _
    set f : ℤ → ℂ := fun k => x ^ (1 - k) * y ^ (l 0 + l 1 + k) with hf
    have e : ∀ k : ℤ, (x - y) * ((x ^ k)⁻¹ * y ^ (l 0 + l 1 + k)) = f k - f (k + 1) := by
      intro k
      simp only [hf, zpow_add₀ hx, zpow_add₀ hy, zpow_sub₀ hx, zpow_one]
      field_simp
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun k _ => e k), sum_Icc_telescope f _ _ (by omega)]
    have e1 : (1:ℤ) - -l 0 = l 0 + 1 := by ring
    have e2 : l 0 + l 1 + -l 0 = l 1 := by ring
    have e3 : (1:ℤ) - (-l 1 + 1) = l 1 := by ring
    have e4 : l 0 + l 1 + (-l 1 + 1) = l 0 + 1 := by ring
    simp only [hf, e1, e2, e3, e4]
  rw [key, hev]

end Ad3.SchwartzSpaceL2.UnramifiedWhittakerGL2
