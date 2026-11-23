import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MatGstar
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjugateStarMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjTor

open Matrix UpperTheory.V.U3

private theorem offdiag_zero {κ : Type} [Field κ] (M : Matrix (Fin 3) (Fin 3) κ) (z z' : κ)
    (hz : z ≠ 0) (hz' : z' ≠ 0) (hne : z' ≠ -z)
    (h : M * Matrix.diagonal ![z, 0, -z] = Matrix.diagonal ![z', 0, -z'] * M) :
    ∀ i j, i ≠ j → M i j = 0 := by
  intro i j hij
  have e := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm] at e
  by_contra hM
  have e' := mul_right_cancel₀ hM e
  have hne' : z ≠ -z' := fun h => hne (by rw [h, neg_neg])
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

private theorem free_etale_sheaf_zmod_exists_hom_sending_generator {κ ι : Type} [Field κ] [IsAlgClosed κ] (m : Fin 3 → κ) (hm : ∀ i, m i ≠ 0)
    (a a' : ι → Matrix (Fin 3) (Fin 3) κ)
    (h1 : ∀ g i j, m i * a g i j = a' g i j * m j)
    (h2 : ∀ g i j, m j.rev * a g i j = a' g i j * m i.rev) :
    ∃ t : κˣ, ∀ g i j, a' g i j = ((t ^ wt i j : κˣ) : κ) * a g i j := by
  have h0 := hm 0
  have h1' := hm 1
  have h2' := hm 2
  have ha : ∀ g i j, a' g i j = m i / m j * a g i j := by
    intro g i j
    have := hm j
    field_simp
    linear_combination -h1 g i j
  by_cases hd : m 0 * m 2 = m 1 * m 1
  · refine ⟨Units.mk0 (m 0 / m 1) (div_ne_zero h0 h1'), fun g i j => ?_⟩
    rw [ha]
    congr 1
    have e2 : m 2 = m 1 * m 1 / m 0 := by field_simp; linear_combination hd
    fin_cases i <;> fin_cases j <;> simp [wt, wt1, e2, zpow_ofNat, h0, h1'] <;> field_simp
  · obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (m 0 / m 2)
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact div_ne_zero h0 h2' (by simpa using hs)
    have hz : ∀ g i j, (m i * m i.rev - m j * m j.rev) * a g i j = 0 := by
      intro g i j
      linear_combination m i.rev * h1 g i j - m j * h2 g i j
    have hd1 : m 0 * m 2 - m 1 * m 1 ≠ 0 := sub_ne_zero.2 hd
    have hd2 : m 2 * m 0 - m 1 * m 1 ≠ 0 := by rwa [mul_comm (m 2)]
    have hd3 : m 1 * m 1 - m 0 * m 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hd)
    have hd4 : m 1 * m 1 - m 2 * m 0 ≠ 0 := by rwa [mul_comm (m 2)]
    refine ⟨Units.mk0 s hs0, fun g i j => ?_⟩
    have z01 : a g 0 1 = 0 := (mul_eq_zero.1 (hz g 0 1)).resolve_left hd1
    have z21 : a g 2 1 = 0 := (mul_eq_zero.1 (hz g 2 1)).resolve_left hd2
    have z10 : a g 1 0 = 0 := (mul_eq_zero.1 (hz g 1 0)).resolve_left hd3
    have z12 : a g 1 2 = 0 := (mul_eq_zero.1 (hz g 1 2)).resolve_left hd4
    have e0 : m 0 = s * s * m 2 := by rw [← hs]; field_simp
    rw [ha]
    fin_cases i <;> fin_cases j <;>
      simp [wt, wt1, z01, z21, z10, z12, e0, zpow_ofNat, h1', h2', hs0] <;> left <;> field_simp

theorem UpperTheory.V.U3.conjBy_tor_of_iso :
    ∀ {G κ : Type} [Group G] [Field κ] [IsAlgClosed κ] (η : G →* ℤˣ) (r r' : G →* GG 3 κ) (c g₁ : G), (2 : κ) ≠ 0 → HasMult η r → HasMult η r' →
      η c = -1 → η g₁ = 1 → Normalised c g₁ r → Normalised c g₁ r' → zeta c g₁ r ≠ 0 → zeta c g₁ r' ≠ 0 → zeta c g₁ r' ≠ -zeta c g₁ r →
      (TypeI η r ∨ TypeII η r) → MatIso η.ker (mats r) (mats r') → ∃ t : κˣ, r' = conjBy (tor κ t) r := by
  intro G κ _ _ _ η r r' c g₁ h2 hr hr' hc hg hN hN' hz hz' hne _ hiso
  obtain ⟨M, hM⟩ := hiso
  have hstar : ∀ g, η g = 1 → η (gstar c g) = 1 := by
    intro g h
    simp [gstar, hc, h]
  have hZ : (M : Matrix (Fin 3) (Fin 3) κ) * zmat c g₁ r = zmat c g₁ r' * M := by
    have e1 := hM g₁ hg
    have e2 := hM (gstar c g₁) (hstar g₁ hg)
    unfold mats at e1 e2
    rw [zmat, zmat, Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  rw [zmat_diag r c g₁ h2.isUnit ((hr c).trans hc) ((hr g₁).trans hg) hN,
    zmat_diag r' c g₁ h2.isUnit ((hr' c).trans hc) ((hr' g₁).trans hg) hN'] at hZ
  have hoff := offdiag_zero _ _ _ hz hz' hne hZ
  have hdiag : (M : Matrix (Fin 3) (Fin 3) κ) = Matrix.diagonal fun i => M i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  have hm : ∀ i, (M : Matrix (Fin 3) (Fin 3) κ) i i ≠ 0 := by
    have hdet : (M : Matrix (Fin 3) (Fin 3) κ).det ≠ 0 := M.det_ne_zero
    rw [hdiag, Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hdet
    exact fun i => hdet i (Finset.mem_univ i)
  have h1 : ∀ g, η g = 1 → ∀ i j, M i i * (r g).mat i j = (r' g).mat i j * M j j := by
    intro g h i j
    have e := hM g h
    rw [hdiag] at e
    have e' := congrFun (congrFun e i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at e'
  have hJ : ∀ (X : Matrix (Fin 3) (Fin 3) κ) (i j : Fin 3),
      (Jmat κ 3 * Xᵀ * Jmat κ 3) j.rev i.rev = X i j := by
    intro X i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]
  have h2' : ∀ g, η g = 1 → ∀ i j : Fin 3,
      M j.rev j.rev * (r g).mat i j = (r' g).mat i j * M i.rev i.rev := by
    intro g h i j
    have e := h1 _ (hstar g h) j.rev i.rev
    rwa [(mat_gstar r c g hN.atc ((hr c).trans hc) ((hr g).trans h)).1,
      (mat_gstar r' c g hN'.atc ((hr' c).trans hc) ((hr' g).trans h)).1, hJ, hJ] at e
  obtain ⟨t, ht⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator (ι := η.ker) (fun i => M i i) hm (fun g => (r g).mat)
    (fun g => (r' g).mat) (fun g => h1 g g.2) (fun g => h2' g g.2)
  obtain ⟨k1, k2, k3, -⟩ := conjBy_tor r t
  refine ⟨t, ?_⟩
  have hker : ∀ g, η g = 1 → r' g = conjBy (tor κ t) r g := by
    intro g h
    refine SemidirectProduct.ext (Units.ext ?_) (by rw [k2, hr g, hr' g])
    ext i j
    exact (ht ⟨g, h⟩ i j).trans (k1 g i j).symm
  have hcc : r' c = conjBy (tor κ t) r c :=
    SemidirectProduct.ext (Units.ext (hN'.atc.trans (k3 c g₁ hN).atc.symm))
      (by rw [k2, hr c, hr' c])
  refine MonoidHom.ext fun g => ?_
  rcases Int.units_eq_one_or (η g) with h | h
  · exact hker g h
  · have e : g = g * c⁻¹ * c := by simp
    rw [e, map_mul r' _ c, map_mul _ _ c, hcc, hker (g * c⁻¹) (by simp [h, hc])]
