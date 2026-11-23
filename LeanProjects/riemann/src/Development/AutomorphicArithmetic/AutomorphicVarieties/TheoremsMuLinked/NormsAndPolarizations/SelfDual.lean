import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.Midpoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.SgConjConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IntModel

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

namespace UpperTheory.V.Th.Nm

private theorem sd_norm {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) : ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  haveI := c.fin
  have hx : IsIntegral ℤ_[l] (x : PadicAlgCl l) := (Algebra.IsIntegral.isIntegral x).map c.O.val
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hx,
    spectralValue_le_one_iff ((minpoly.monic hx).map _)]
  intro n
  rw [Polynomial.coeff_map]
  exact ((minpoly ℤ_[l] (x : PadicAlgCl l)).coeff n).2

private theorem sd_eps {l : ℕ} [Fact l.Prime] (F : GFrame l) (c : Coef l) (g : F.G₀) (z : ℤ) :
    ‖((F.eps c.O (Qbar l) g ^ z : (Qbar l)ˣ) : Qbar l)‖ ≤ 1 := by
  have h1 : ‖((F.eps c.O (Qbar l) g : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
    simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.coe_comp,
      Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact (PadicAlgCl.norm_extends l _).trans (PadicInt.norm_units _)
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, h1, _root_.one_zpow]

private theorem sd_conj_conj {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : F.conj (F.conj g) = g := by
  apply Subtype.ext
  show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = g
  rw [inv_eq_of_mul_eq_one_right F.c_sq, mul_assoc, mul_assoc, mul_assoc, F.c_sq, mul_one, ← mul_assoc, F.c_sq, one_mul]

private theorem sd_sgn {K : Type} [CommRing K] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) K) (h : Pᵀ = P ∨ Pᵀ = -P) :
    (Qᵀ * P * Q)ᵀ = Qᵀ * P * Q ∨ (Qᵀ * P * Q)ᵀ = -(Qᵀ * P * Q) := by
  have e : (Qᵀ * P * Q)ᵀ = Qᵀ * Pᵀ * Q := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rcases h with h | h
  · left
    rw [e, h]
  · right
    rw [e, h, Matrix.mul_neg, Matrix.neg_mul]

private theorem sd_form {K : Type} [CommRing K] {n : ℕ} (A B P Q P₀ : GL (Fin n) K) (e : K)
    (hP : (P₀ : Matrix (Fin n) (Fin n) K) = (Q : Matrix (Fin n) (Fin n) K)ᵀ * P * Q)
    (h : (A : Matrix (Fin n) (Fin n) K)ᵀ * P * B = e • (P : Matrix (Fin n) (Fin n) K)) :
    ((P₀ * (Q⁻¹ * B * Q) * P₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      e • ((Q⁻¹ * A⁻¹ * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := by
  have hPB : (P : Matrix (Fin n) (Fin n) K) * B = e • ((↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * P) := by
    calc (P : Matrix (Fin n) (Fin n) K) * B
        = ((↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * (A : Matrix (Fin n) (Fin n) K)ᵀ) * P * B := by
          rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
      _ = (↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * ((A : Matrix (Fin n) (Fin n) K)ᵀ * P * B) := by
          simp only [Matrix.mul_assoc]
      _ = e • ((↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * P) := by
          rw [h, Matrix.mul_smul]
  have hQ : ∀ X : Matrix (Fin n) (Fin n) K,
      (↑Q⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * ((Q : Matrix (Fin n) (Fin n) K)ᵀ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
  have key : (P₀ : Matrix (Fin n) (Fin n) K) *
      ((↑Q⁻¹ : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) * (Q : Matrix (Fin n) (Fin n) K)) =
      (e • ((↑Q⁻¹ : Matrix (Fin n) (Fin n) K) * (↑A⁻¹ : Matrix (Fin n) (Fin n) K) *
        (Q : Matrix (Fin n) (Fin n) K))ᵀ) * (P₀ : Matrix (Fin n) (Fin n) K) := by
    rw [hP, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left, hQ]
    rw [← Matrix.mul_assoc (P : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin n) (Fin n) K), hPB]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  simp only [Units.val_mul]
  rw [key, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end UpperTheory.V.Th.Nm

theorem UpperTheory.V.Th.Nm.selfDual :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)), Continuous ρ → Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → F.IsForm c.O n ρ P → ∃ Q P' : GL (Fin n) (Qbar l), (P' : Matrix (Fin n) (Fin n) (Qbar l)) = (Q : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P * Q ∧ ((P' : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P' ∨ (P' : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P') ∧ IntM (P' : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((P'⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ ∀ g, IntM (mat (cj Q ρ) g) := by
  intro l hl n F c ρ P hρ hspan hform
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  obtain ⟨c', Q₀, ρ₀, -, hQ₀, -⟩ := Ws.Eb.intModel c ρ hρ
  have hint : ∀ g, IntM ((cj Q₀ ρ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    intro g i j
    rw [cj_apply, mul_assoc, hQ₀ g, inv_mul_cancel_left]
    exact sd_norm c' ((ρ₀ g : Matrix (Fin n) (Fin n) c'.O) i j)
  let Qt : GL (Fin n) (Qbar l) :=
    ⟨(Q₀ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ, (↑Q₀⁻¹ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ,
      by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : GL (Fin n) (Qbar l),
      (P₁ : Matrix (Fin n) (Fin n) (Qbar l)) = (Q₀ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P * Q₀ :=
    ⟨Qt * P * Q₀, rfl⟩
  have hsP₁ : (P₁ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P₁ ∨
      (P₁ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -(P₁ : Matrix (Fin n) (Fin n) (Qbar l)) := by
    rw [hP₁]
    exact sd_sgn _ _ (sign F c ρ P hspan hform)
  have hconj : ∀ g, IntM ((P₁ * cj Q₀ ρ (F.conj g) * P₁⁻¹ : GL (Fin n) (Qbar l)) :
      Matrix (Fin n) (Fin n) (Qbar l)) := by
    intro g
    have key := sd_form (ρ g) (ρ (F.conj g)) P Q₀ P₁ _ hP₁ (hform g)
    rw [cj_apply, key]
    intro i j
    have hinv : (Q₀⁻¹ * (ρ g)⁻¹ * Q₀ : GL (Fin n) (Qbar l)) = cj Q₀ ρ g⁻¹ := by
      rw [cj_apply, map_inv]
    rw [hinv, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, norm_mul]
    exact mul_le_one₀ (sd_eps F c g _) (norm_nonneg _) (hint _ j i)
  obtain ⟨Q₂, P', hP', hP'int, hP'inv, hQ₂⟩ := midpoint (Set.range (cj Q₀ ρ)) P₁ hsP₁ (by
    rintro _ ⟨h, rfl⟩
    refine ⟨hint h, ?_⟩
    have := hconj (F.conj h)
    rwa [sd_conj_conj] at this)
  refine ⟨Q₀ * Q₂, P', ?_, ?_, hP'int, hP'inv, ?_⟩
  · rw [hP', hP₁]
    simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  · rw [hP']
    exact sd_sgn _ _ hsP₁
  · intro g
    have := hQ₂ _ ⟨g, rfl⟩
    rw [cj_apply] at this
    show IntM ((cj (Q₀ * Q₂) ρ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))
    rw [cj_apply, _root_.mul_inv_rev]
    simpa only [mul_assoc] using this
