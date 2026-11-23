import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SmallOperatorExistence
import ReciprocityTheory.SemistableReduction.LatAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMajorantFlags

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

private lemma sum_pi_single_one_smul {n : ℕ} (j : Fin n) (y : Fin n → Fin n → ℂ) :
    ∑ k, (Pi.single j (1 : ℂ) : Fin n → ℂ) k • y k = y j := by
  simp [Pi.single_apply]

theorem latticeBoundAtMaximum_of_transference (hD5 : CoveringRadiusStatement) : LatticeBoundAtMaximum (E := E) := by
  unfold LatticeBoundAtMaximum
  intro r X z0 x0 laStar ρ hz0 hx0 hortho hflag hla0 hla1 hρ0 hρ1 hshort
  rcases Nat.eq_zero_or_pos r with hr0 | hr
  ·
    subst hr0
    have hp : X.p0 = 0 := Nat.le_zero.mp X.p0_le
    haveI : IsEmpty (Fin X.p0) := by rw [hp]; infer_instance
    refine ⟨fun j => j.elim0, 0, ?_, ?_⟩
    · show (⨆ τ : X.Ψ, Data.opN (Matrix.of ((0 : X.Coord) τ))) ≤ ρ / 3
      refine Real.iSup_le (fun τ => ?_) (by linarith)
      refine SmallOperatorExistence.opN_le _ (by linarith) (fun w => ?_)
      have h0 : Matrix.of ((0 : X.Coord) τ) *ᵥ w = 0 := by
        funext i
        exact absurd i.2 (by omega)
      rw [h0, OrthonormalChartBounds.nsq_zero']
      exact mul_nonneg (sq_nonneg _) (OrthonormalChartBounds.nsq_nonneg w)
    · unfold LamBasis
      refine ⟨fun j => j.elim0, linearIndependent_empty_type, fun j => j.elim0,
        fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun τ => ?_⟩
      simp only [Set.range_eq_empty]
  ·
    have hcard : Fintype.card X.Ψ = fdeg E := by
      first
      | exact QuadraticCoefficientForms.card_Psi
      | exact QuadraticCoefficientForms.card_Psi (X := X.toData)
      | exact QuadraticCoefficientForms.card_Psi X.toData
    have hcardpos : 0 < Fintype.card X.Ψ := by
      first
      | exact QuadraticCoefficientForms.card_Psi_pos
      | exact QuadraticCoefficientForms.card_Psi_pos (X := X.toData)
      | exact QuadraticCoefficientForms.card_Psi_pos X.toData
    haveI : Nonempty X.Ψ := Fintype.card_pos_iff.mp hcardpos
    have hdet : ∀ τ : X.Ψ, (mat x0 τ).det ≠ 0 := fun τ => (hx0 τ).1
    have hc0 : (0 : ℝ) < Fintype.card X.Ψ := by exact_mod_cast hcardpos
    have hc1 : (1 : ℝ) ≤ Fintype.card X.Ψ := by exact_mod_cast hcardpos
    have hcne : (Fintype.card X.Ψ : ℝ) ≠ 0 := hc0.ne'
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hsq1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card X.Ψ) := by
      have h := Real.sqrt_le_sqrt hc1
      rwa [Real.sqrt_one] at h
    have hsr : (1 : ℝ) ≤ Real.sqrt r := by
      have h := Real.sqrt_le_sqrt hr1
      rwa [Real.sqrt_one] at h
    have hsq0 : (0 : ℝ) < Real.sqrt (Fintype.card X.Ψ) := by linarith
    have hl0 : 0 < laStar / Real.sqrt (Fintype.card X.Ψ) := div_pos hla0 hsq0
    have hl1 : laStar / Real.sqrt (Fintype.card X.Ψ) ≤ 1 := by
      rw [div_le_one hsq0]; linarith
    have hd : (1 : ℝ) ≤ |(NumberField.discr E : ℝ)| := by
      rw [← Int.cast_abs]
      first
      | exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero E)
      | exact_mod_cast Int.one_le_abs NumberField.discr_ne_zero

    have hmaj : ∀ (τ : X.Ψ) (w : Fin r → ℂ),
        X.maj z0 τ w = ReciprocityTheory.MultiplicativeHeights.normSq ((mat x0 τ)⁻¹ *ᵥ w) := by
      intro τ w
      rw [← MajorantOrthogonality.maj_ortho X.toData hx0 hortho τ w]
      first
      | exact (FlowMajorantFlags.maj_flag hz0 hx0 hflag τ w).symm
      | exact (FlowMajorantFlags.maj_flag X.toData hz0 hx0 hflag τ w).symm
      | exact (FlowMajorantFlags.maj_flag (X := X.toData) hz0 hx0 hflag τ w).symm
    have hconst : ∑ _τ : X.Ψ, (laStar / Real.sqrt (Fintype.card X.Ψ)) ^ 2 = laStar ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_pow, Real.sq_sqrt hc0.le]
      field_simp
      try ring

    have hsv : ∀ v ∈ X.L', v ≠ 0 → ∃ τ : X.Ψ,
        (laStar / Real.sqrt (Fintype.card X.Ψ)) ^ 2 ≤
          ReciprocityTheory.MultiplicativeHeights.normSq ((mat x0 τ)⁻¹ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 v) := by
      intro v hv hv0
      by_contra hcon
      push_neg at hcon
      have hlt : ∑ τ : X.Ψ, X.maj z0 τ (Data.emb τ.1 v) <
          ∑ _τ : X.Ψ, (laStar / Real.sqrt (Fintype.card X.Ψ)) ^ 2 := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro τ _
        rw [hmaj τ]
        exact hcon τ
      linarith [hshort v hv hv0]
    have hform : ∀ (i : X.Ψ) (x y : Fin r → E),
        i.1 ((MajorantOrthogonality.pform X.toData).h x y) =
          ReciprocityTheory.MultiplicativeHeights.jForm X.p0 ((mat x0 i)⁻¹ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec i.1 x)
            ((mat x0 i)⁻¹ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec i.1 y) := by
      intro i x y
      rw [MajorantOrthogonality.pform_h]
      exact MajorantOrthogonality.herm_coord X.toData hx0 hortho i y x
    have hQdet : ∀ i : X.Ψ, ((mat x0 i)⁻¹).det ≠ 0 := by
      intro i
      first
      | (rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero (hdet i))
      | simp [Matrix.det_nonsing_inv, hdet i]
    have hcm : ∀ τ : E →+* ℂ, (∃ i : X.Ψ, i.1 = τ) ↔
        ¬ ∃ i : X.Ψ, i.1 = ComplexEmbedding.conjugate τ := by
      intro τ
      constructor
      · rintro ⟨i, rfl⟩ ⟨j, hj⟩
        exact (X.cmType i.1).mp i.2 (hj ▸ j.2)
      · intro hn
        have hmem : τ ∈ X.Ψ := (X.cmType τ).mpr (fun h => hn ⟨⟨_, h⟩, rfl⟩)
        exact ⟨⟨τ, hmem⟩, rfl⟩

    unfold CoveringRadiusStatement at hD5
    have h5 := hD5 E ↥X.Ψ r X.p0 (MajorantOrthogonality.pform X.toData) (fun τ => τ.1)
      (fun τ => (mat x0 τ)⁻¹) X.L' (laStar / Real.sqrt (Fintype.card X.Ψ))
      Subtype.val_injective hcm X.p0_le hl0 hQdet hform (MajorantOrthogonality.isLattice X)
      (MajorantOrthogonality.selfDual X) hsv
    obtain ⟨hcov, v, hvL, hvli, hvmaj⟩ := h5
    set μ : ℝ := d5mu (Fintype.card X.Ψ) r |(NumberField.discr E : ℝ)|
      (laStar / Real.sqrt (Fintype.card X.Ψ)) with hμdef
    have hμ4 : 4 ≤ μ := by
      have hfr : (1 : ℝ) ≤ (Fintype.card X.Ψ : ℝ) * r := one_le_mul_of_one_le_of_one_le hc1 hr1
      have h2 : (1 : ℝ) ≤ ((Fintype.card X.Ψ : ℝ) * r) * ((Fintype.card X.Ψ : ℝ) * r) :=
        one_le_mul_of_one_le_of_one_le hfr hfr
      have h3 : (1 : ℝ) ≤ ((Fintype.card X.Ψ : ℝ) * r) ^ 3 := by
        have h := one_le_mul_of_one_le_of_one_le h2 hfr
        calc (1 : ℝ) ≤ _ := h
          _ = ((Fintype.card X.Ψ : ℝ) * r) ^ 3 := by ring
      have h4 : (1 : ℝ) ≤ ((Fintype.card X.Ψ : ℝ) * r) ^ 3 * |(NumberField.discr E : ℝ)| :=
        one_le_mul_of_one_le_of_one_le h3 hd
      rw [hμdef]
      unfold d5mu
      first | rw [le_div_iff₀ hl0] | rw [le_div_iff hl0]
      nlinarith [h4, hl1]
    have hμ0 : 0 ≤ μ := by linarith

    have happ := ReciprocityTheory.MultiplicativeHeights.Closed.approx
    unfold ReciprocityTheory.MultiplicativeHeights.ApproxStatement at happ
    obtain ⟨la, hlaL, hlali, horth, hpos, hneg, hbd1, hbd2⟩ :=
      happ E ↥X.Ψ r X.p0 (MajorantOrthogonality.pform X.toData) (fun τ => τ.1)
        (fun τ => (mat x0 τ)⁻¹) X.L' v μ ρ X.p0_le (by linarith) hρ0 hρ1 hQdet hform
        (MajorantOrthogonality.selfDual X).1 hcov hvL hvli hvmaj

    have hZ := fun τ : X.Ψ => SmallOperatorExistence.exists_Z X.toData hx0 τ (fun j => Data.emb τ.1 (la j))
      (δ := ρ / 3) (by linarith) (fun w hw => hpos τ w hw)
    choose Zf hZn hZs using hZ
    refine ⟨la, fun τ => Zf τ, ?_, ?_⟩
    · show (⨆ τ : X.Ψ, Data.opN (Matrix.of (Zf τ))) ≤ ρ / 3
      exact Real.iSup_le (fun τ => hZn τ) (by linarith)
    · unfold LamBasis
      refine ⟨hlaL, hlali, ?_, ?_, ?_, ?_, fun τ => hZs τ (fun τ => Zf τ) rfl⟩
      · intro j k hj hk
        have h0 := horth j k hj hk
        rw [MajorantOrthogonality.pform_h] at h0
        rw [← HermitianPairingAlgebra.herm_symm X.Gm_herm, h0]
        simp [cc]
      · intro j hj τ
        have hw : ∀ k : Fin r, X.p0 ≤ (k : ℕ) → (Pi.single j (1 : ℂ) : Fin r → ℂ) k = 0 := by
          intro k hk
          have hkj : k ≠ j := fun h => by rw [h] at hk; omega
          first
          | exact Pi.single_eq_of_ne hkj 1
          | simp [Pi.single_apply, hkj]
        have hw0 : (Pi.single j (1 : ℂ) : Fin r → ℂ) ≠ 0 := by
          intro h
          have h' := congrFun h j
          simp at h'
        have h := (hpos τ _ hw).2 hw0
        simp only [sum_pi_single_one_smul] at h
        rw [MajorantOrthogonality.herm_coord X.toData hx0 hortho τ]
        exact h
      · intro j hj τ
        have hw : ∀ k : Fin r, (k : ℕ) < X.p0 → (Pi.single j (1 : ℂ) : Fin r → ℂ) k = 0 := by
          intro k hk
          have hkj : k ≠ j := fun h => by rw [h] at hk; omega
          first
          | exact Pi.single_eq_of_ne hkj 1
          | simp [Pi.single_apply, hkj]
        have hw0 : (Pi.single j (1 : ℂ) : Fin r → ℂ) ≠ 0 := by
          intro h
          have h' := congrFun h j
          simp at h'
        have h := hneg τ _ hw hw0
        simp only [sum_pi_single_one_smul] at h
        rw [MajorantOrthogonality.herm_coord X.toData hx0 hortho τ]
        exact h
      · intro j τ
        have hA : 4 * μ ≤ ReciprocityTheory.MultiplicativeHeights.approxR r μ ρ := by
          unfold ReciprocityTheory.MultiplicativeHeights.approxR
          first | rw [le_div_iff₀ hρ0] | rw [le_div_iff hρ0]
          nlinarith [mul_le_mul_of_nonneg_left hρ1 hμ0, mul_le_mul_of_nonneg_right hsr hμ0]
        have hT : (1 : ℝ) ≤ 2 * ReciprocityTheory.MultiplicativeHeights.approxR r μ ρ := by linarith
        have hTμ : 2 * μ ^ 2 ≤ (2 * ReciprocityTheory.MultiplicativeHeights.approxR r μ ρ) ^ 2 := by
          nlinarith [mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ 8 * μ)
            (by linarith : 8 * μ ≤ 2 * ReciprocityTheory.MultiplicativeHeights.approxR r μ ρ)]
        have hLa : frameBasisRadius r X.p0 (fdeg E) (dE E) laStar ρ =
            (2 * ReciprocityTheory.MultiplicativeHeights.approxR r μ ρ) ^ (2 * (X.p0 + 1) - 1) := by
          rw [show 2 * (X.p0 + 1) - 1 = 2 * X.p0 + 1 by omega]
          unfold frameBasisRadius
          rw [← hcard] <;> rfl
        rw [hLa, ← MajorantOrthogonality.pform_h]
        refine IsotropicCombinations.la_bound (p0 := X.p0 + 1) hT hTμ (by omega) ?_
        by_cases hj : (j : ℕ) < X.p0
        · exact Or.inl (hbd1 τ j hj)
        · right
          rw [Nat.add_sub_cancel]
          exact hbd2 τ j (by omega)

end ReciprocityTheory.ChartRestriction.G.FD
