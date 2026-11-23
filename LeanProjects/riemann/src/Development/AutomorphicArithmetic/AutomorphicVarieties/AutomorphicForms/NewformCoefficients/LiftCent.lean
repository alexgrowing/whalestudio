import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.IntOfIntegers
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DvdOfOhat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslInv

open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af.Nf Matrix
open scoped MatrixGroups

private theorem idele_split (x : Ideles ℚ) :
    TR.infId ℚ (Units.map (TR.pInf ℚ).toMonoidHom x) * finId ℚ (Units.map (pFin ℚ).toMonoidHom x) = x := by
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  have h2 : ∀ x, TR.pInf ℚ (sFin ℚ x) = 0 := fun x => map_zero (TR.infEq ℚ).symm
  have h3 : ∀ x, pFin ℚ (TR.sInf ℚ x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin ℚ (sFin ℚ x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _
    simp [h, h2]
  · change pFin ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _
    simp [h3, h4]

private theorem corner_sc {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (u : Rˣ) :
    cornerGL 2 s (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (Units.map (corner s) u) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (Matrix.scalar (Fin 2) u.val i j) =
    Matrix.scalar (Fin 2) (1 - s 1 + s u.val) i j
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem idele_dec (z : Ideles ℚ) : ∃ (r : ℚˣ) (t : (TR.Rinf ℚ)ˣ) (u : (Af ℚ)ˣ), (∀ v, 0 < t.val v) ∧ IsZU u ∧
    z = Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r * (TR.infId ℚ t * finId ℚ u) := by
  obtain ⟨r, u, -, hu, e⟩ := ratAd.1 (Units.map (pFin ℚ).toMonoidHom z)
  set w : Ideles ℚ := (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r)⁻¹ * z with hw
  have hz : z = Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r * w := by rw [hw, mul_inv_cancel_left]
  have e1 : Units.map (pFin ℚ).toMonoidHom w = u := by
    rw [hw, map_mul, map_inv, e]
    exact inv_mul_cancel_left _ _
  have h0 := TR.unit_ne_zero (Units.map (TR.pInf ℚ).toMonoidHom w) Rat.infinitePlace
  rcases lt_or_gt_of_ne h0 with h | h
  · refine ⟨-r, Units.map (TR.pInf ℚ).toMonoidHom (-w), Units.map (pFin ℚ).toMonoidHom (-w), fun v => ?_, ?_, ?_⟩
    · rw [Subsingleton.elim v Rat.infinitePlace]
      change 0 < TR.pInf ℚ (-w.val) Rat.infinitePlace
      rw [map_neg]
      exact neg_pos.2 h
    · have : Units.map (pFin ℚ).toMonoidHom (-w) = -u := by
        rw [← e1]
        exact Units.ext (map_neg (pFin ℚ) w.val)
      rw [this]
      exact ⟨neg_mem hu.1, neg_mem hu.2⟩
    · rw [idele_split]
      refine hz.trans (Units.ext ?_)
      simp
  · refine ⟨r, Units.map (TR.pInf ℚ).toMonoidHom w, Units.map (pFin ℚ).toMonoidHom w, fun v => ?_, e1 ▸ hu, ?_⟩
    · rw [Subsingleton.elim v Rat.infinitePlace]
      exact h
    · rw [idele_split]
      exact hz

theorem UpperTheory.V.Af.Nf.liftCent :
    UpperTheory.V.Af.Nf.LiftCent := by
  intro k M hM χ ω hω f hf φ hφ z g
  obtain ⟨r, t, u, ht, hu, rfl⟩ := idele_dec z
  obtain ⟨γ, h, κ, hκ, rfl⟩ := decomp M hM g
  obtain ⟨δ, β, hδ, hβ, hK, hd⟩ := (ratK M hM).2 u hu
  have h1 : ω.1 (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r) = 1 := ω.2.2 r
  have h2 := hω.unit u hu _ hd
  have s1 : GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r) =
      ratGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) r) := by
    ext i j
    by_cases e : i = j <;> simp [ratGL, Matrix.diagonal_apply, e, Matrix.algebraMap_matrix_apply]
  set T : GL (Fin 2) ℝ := GeneralLinearGroup.map ev (GeneralLinearGroup.scalar (Fin 2) t) with hT
  have s2 : GeneralLinearGroup.scalar (Fin 2) (TR.infId ℚ t) = upR T := by
    rw [hT, upR_ev]
    exact (corner_sc _ t).symm
  have s3 : GeneralLinearGroup.scalar (Fin 2) (finId ℚ u) = finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) u) :=
    (corner_sc _ u).symm
  have e : GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r * (TR.infId ℚ t * finId ℚ u)) *
      (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 κ)) = ratGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) r * γ * β) *
        (upR ((toR β)⁻¹ * (T * h)) * finGL ℚ 2 ((toF β)⁻¹ * GeneralLinearGroup.scalar (Fin 2) u * κ)) := by
    have c : ∀ (x : GL (Fin 2) ℝ) (y : GL (Fin 2) (Af ℚ)) (w : GA ℚ 2), finGL ℚ 2 y * (upR x * w) = upR x * (finGL ℚ 2 y * w) :=
      fun x y w => by rw [← mul_assoc, ← upR_comm, mul_assoc]
    rw [map_mul, mul_assoc, ← mul_assoc _ (ratGL ℚ 2 γ),
      GeneralLinearGroup.scalar_commute (TR.infId ℚ t * finId ℚ u) (ratGL ℚ 2 γ), map_mul, s1, s2, s3,
      map_mul (ratGL ℚ 2), map_mul (ratGL ℚ 2), ratGL_eq β]
    simp only [mul_assoc, c]
    simp only [mul_assoc, map_mul, map_inv, mul_inv_cancel_left]
  have hβ' : (toR β).val = δ.1.map (Int.cast : ℤ → ℝ) := by
    ext i j
    have := congrFun (congrFun hβ i) j
    change (Rat.castHom ℝ) (β.val i j) = _
    rw [this]
    simp
  have e2 : ((toR β)⁻¹ * (T * h)).val = t.val Rat.infinitePlace • ((toR β)⁻¹ * h).val := by
    have : T.val = t.val Rat.infinitePlace • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      by_cases e : i = j <;> simp [hT, ev, Matrix.diagonal_apply, e]
    simp only [Units.val_mul, this, Matrix.smul_mul, Matrix.mul_smul, one_mul]
  have e3 := ((nslInv k M f ((toR β)⁻¹ * h).val ((toR β)⁻¹ * h).det_ne_zero).2 χ hf δ hδ)
  rw [← hβ', ← Units.val_mul, mul_inv_cancel_left] at e3
  rw [e, hφ _ _ _ (mul_mem hK hκ), hφ _ _ _ hκ, e2, (nslMul k f).2.2.1 _ _ (ht _), e3, map_mul, map_mul, h1, hω.pos t ht,
    one_mul, one_mul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, h2, one_mul]
