import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.CoefFam

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.WyKR

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem klf_stepCoef_apply (X : GMod n) (z : ℂ) (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (j : Fin n)
    (u : (step X z).V) (g : Matrix (Fin n) (Fin n) ℂ) :
    stepCoef X z c j u g = ∑ i, g j i * c ((Subtype.val u : Fin n → X.V) i) g := rfl

theorem klf_contFam_step {ε : Fin n → Bool} {X : GMod n} {I : Type} {c : CoefFam X I} (h : ContFam ε c) (z : ℂ) :
    ContFam ε (X := step X z) (fun p : I × Fin n => stepCoef X z (c p.1) p.2) := by
  rintro ⟨i, j⟩ v
  simp only [klf_stepCoef_apply]
  exact continuous_finsetSum _ fun a _ => ((S7.continuous_toM ε).matrix_elem j a).mul (h i _)

theorem leftExp_step {ε : Fin n → Bool} {X : GMod n} {I : Type} {c : CoefFam X I} (h : LeftExp ε c) (z : ℂ) :
    LeftExp ε (X := step X z) (fun p : I × Fin n => stepCoef X z (c p.1) p.2) := by
  rintro ⟨i, j⟩
  obtain ⟨r, is, β, B, hB, hc⟩ := h i
  refine ⟨n * r, fun m => (is (finProdFinEquiv.symm m).2, (finProdFinEquiv.symm m).1),
    fun m k => S7.toMK k j (finProdFinEquiv.symm m).1 * β (finProdFinEquiv.symm m).2 k, |B|, ?_, ?_⟩
  · intro m k
    rw [norm_mul]
    have h1 : ‖S7.toMK k j (finProdFinEquiv.symm m).1‖ ≤ 1 :=
      entry_norm_bound_of_unitary (U := S7.toMK k) k.2.1 _ _
    calc _ ≤ 1 * |B| := mul_le_mul h1 ((hB _ _).trans (le_abs_self B)) (norm_nonneg _) zero_le_one
      _ = |B| := one_mul _
  · intro v g k
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, klf_stepCoef_apply, hc, Matrix.mul_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

theorem leftExp_path {ε : Fin n → Bool} {X : GMod n} {I : Type} {c : CoefFam X I} (h : LeftExp ε c)
    (χ : Fin n → ℂ) (ss : List (Fin n)) :
    LeftExp ε (X := path X χ ss) (fun p : I × List (Fin n) => pathCoef X (c p.1) χ ss p.2) := by
  induction ss generalizing X I χ with
  | nil =>
    rintro ⟨i, js⟩
    obtain ⟨r, is, β, B, hB, hc⟩ := h i
    exact ⟨r, fun l => (is l, js), β, B, hB, hc⟩
  | cons s ss ih =>
    rintro ⟨i, js⟩
    obtain ⟨r, is, β, B, hB, hc⟩ := ih (leftExp_step h (χ s)) (χ + Pi.single s 1) ((i, js.headD s), js.tail)
    exact ⟨r, fun l => ((is l).1.1, (is l).1.2 :: (is l).2), β, B, hB, hc⟩

theorem contFam_path {ε : Fin n → Bool} {X : GMod n} {I : Type} {c : CoefFam X I} (h : ContFam ε c)
    (χ : Fin n → ℂ) (ss : List (Fin n)) :
    ContFam ε (X := path X χ ss) (fun p : I × List (Fin n) => pathCoef X (c p.1) χ ss p.2) := by
  induction ss generalizing X I χ with
  | nil => exact fun p => h p.1
  | cons s ss ih =>
    rintro ⟨i, js⟩
    exact ih (klf_contFam_step h (χ s)) (χ + Pi.single s 1) ((i, js.headD s), js.tail)

theorem leftExp_base {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    LeftExp ε (X := ⟨D, E, hK.gl⟩) (fun ξ : D => baseCoef σ D (ξ : H)) := by
  intro ξ
  obtain ⟨S, hfin, hξ, hS⟩ := (hK.mem _).1 ξ.2
  have hSD : ∀ x ∈ S, x ∈ D := fun x hx => (hK.mem _).2 ⟨S, hfin, hx, hS⟩
  let b := stdOrthonormalBasis ℂ S
  have hmem : ∀ k : S7.KG ε, σ (S7.toMK k⁻¹) (ξ : H) ∈ S := fun k => hS _ (k⁻¹).2 _ hξ
  have hUJ : ∀ g : S7.UJ ε, S7.toM g ∈ Formalism.MainNotions.S.UJset ε := fun g => g.2
  refine ⟨Module.finrank ℂ S, fun l => ⟨(b l : H), hSD _ (b l).2⟩,
    fun l k => ⟪σ (S7.toMK k⁻¹) (ξ : H), (b l : H)⟫_ℂ, ‖(ξ : H)‖, ?_, ?_⟩
  · intro l k
    refine (norm_inner_le_norm _ _).trans ?_
    have h1 : ‖(b l : H)‖ = 1 := b.orthonormal.1 l
    rw [h1, mul_one, hU.2.1 _ (hUJ _)]
  · intro v g k
    show ⟪(ξ : H), σ (S7.toMK k * S7.toM g) (v : H)⟫_ℂ =
      ∑ l, ⟪σ (S7.toMK k⁻¹) (ξ : H), (b l : H)⟫_ℂ * ⟪(b l : H), σ (S7.toM g) (v : H)⟫_ℂ
    have hkg : S7.toMK k * S7.toM g = S7.toM ((k : S7.UJ ε) * g) := rfl
    let L : H →ₗᵢ[ℂ] H := ⟨(σ (S7.toMK k⁻¹)).toLinearMap, hU.2.1 _ (hUJ _)⟩
    have e1 := L.inner_map_map (ξ : H) (σ (S7.toMK k * S7.toM g) (v : H))
    have e2 : L (σ (S7.toMK k * S7.toM g) (v : H)) = σ (S7.toM g) (v : H) := by
      have h3 := hU.1.2 (S7.toMK k⁻¹) (hUJ _) (S7.toMK k * S7.toM g) (hkg ▸ hUJ _)
      have h4 : S7.toMK k⁻¹ * (S7.toMK k * S7.toM g) = S7.toM g := by
        show S7.toM (((k : S7.UJ ε))⁻¹ * ((k : S7.UJ ε) * g)) = S7.toM g
        rw [inv_mul_cancel_left]
      rw [h4] at h3
      rw [h3]
      rfl
    rw [← e1, e2]
    have e3 : σ (S7.toMK k⁻¹) (ξ : H) =
        ∑ l, ⟪(b l : H), σ (S7.toMK k⁻¹) (ξ : H)⟫_ℂ • (b l : H) := by
      have := congrArg (Subtype.val : S → H) (b.sum_repr' ⟨_, hmem k⟩)
      simpa using this.symm
    show ⟪σ (S7.toMK k⁻¹) (ξ : H), _⟫_ℂ = _
    conv_lhs => rw [e3]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_left, inner_conj_symm]

theorem contFam_base {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    ContFam ε (X := ⟨D, E, hK.gl⟩) (fun ξ : D => baseCoef σ D (ξ : H)) := by
  intro ξ v
  have h : Continuous fun g : S7.UJ ε => σ (S7.toM g) (v : H) :=
    (hU.2.2 (v : H)).comp_continuous (S7.continuous_toM ε) fun g => g.2
  exact continuous_const.inner h

end CompanionTheory.RgExh.Dec.L.WyKR
