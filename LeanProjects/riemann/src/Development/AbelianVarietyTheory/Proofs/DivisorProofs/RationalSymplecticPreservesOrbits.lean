import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.SymplecticOrbit

variable {g : ℕ}

def cmat (γ : Sp g) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ :=
  γ.mat.map (fun t : ℝ => (t : ℂ))

theorem cmat_eq (γ : Sp g) : cmat γ = γ.mat.map Complex.ofRealHom := rfl

theorem cmat_inv_mul (γ : Sp g) : cmat γ⁻¹ * cmat γ = 1 := by
  rw [cmat_eq, cmat_eq, ← Matrix.map_mul]
  have : (γ⁻¹).mat * γ.mat = 1 := congrArg Subtype.val (inv_mul_cancel γ)
  rw [this]
  simp

theorem cmat_symp (γ : Sp g) : (cmat γ)ᵀ * J (Fin g) ℂ * cmat γ = J (Fin g) ℂ := by
  have h : γ.matᵀ * J (Fin g) ℝ * γ.mat = J (Fin g) ℝ := SymplecticGroup.mem_iff'.1 γ.2
  have hJ : (J (Fin g) ℝ).map Complex.ofRealHom = J (Fin g) ℂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [J, Matrix.one_apply, apply_ite]
  have := congrArg (fun A => A.map Complex.ofRealHom) h
  simp only [Matrix.map_mul, hJ] at this
  exact this

theorem cmat_mul_fromRows (γ : Sp g) (τ : Matrix (Fin g) (Fin g) ℂ) :
    cmat γ * fromRows τ (1 : Matrix (Fin g) (Fin g) ℂ) =
      fromRows (γ.mat.toBlocks₁₁.map (fun t : ℝ => (t : ℂ)) * τ +
        γ.mat.toBlocks₁₂.map (fun t : ℝ => (t : ℂ))) (den γ τ) := by
  have : cmat γ = fromBlocks (γ.mat.toBlocks₁₁.map (fun t : ℝ => (t : ℂ)))
      (γ.mat.toBlocks₁₂.map (fun t : ℝ => (t : ℂ))) (γ.mat.toBlocks₂₁.map (fun t : ℝ => (t : ℂ)))
      (γ.mat.toBlocks₂₂.map (fun t : ℝ => (t : ℂ))) := by
    rw [← fromBlocks_map, fromBlocks_toBlocks]; rfl
  rw [this, fromBlocks_mul_fromRows, den]
  simp

theorem im_form {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm) (v : Fin g → ℂ) :
    (star v ⬝ᵥ (τ *ᵥ v)).im =
      (fun i => (v i).re) ⬝ᵥ (τ.map Complex.im *ᵥ fun i => (v i).re) +
      (fun i => (v i).im) ⬝ᵥ (τ.map Complex.im *ᵥ fun i => (v i).im) := by
  have h : ∑ i, ∑ j, (v i).re * (τ i j).re * (v j).im =
      ∑ i, ∑ j, (v i).im * (τ i j).re * (v j).re := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hτ.apply i j]; ring
  have e : (star v ⬝ᵥ (τ *ᵥ v)).im = ∑ i, ∑ j, ((v i).re * (τ i j).re * (v j).im -
      (v i).im * (τ i j).re * (v j).re + (v i).re * ((τ i j).im * (v j).re) +
      (v i).im * ((τ i j).im * (v j).im)) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, Complex.im_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp
    ring
  rw [e]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, h, dotProduct, mulVec,
    Finset.mul_sum, map_apply]
  ring

theorem form_J (a b c d : Fin g → ℂ) :
    Sum.elim a b ⬝ᵥ (J (Fin g) ℂ *ᵥ Sum.elim c d) = b ⬝ᵥ c - a ⬝ᵥ d := by
  simp [J, fromBlocks_mulVec, Matrix.neg_mulVec]
  ring

theorem isUnit_den (γ : Sp g) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : IsSiegel τ) :
    IsUnit (den γ τ) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  suffices H : ∀ v, den γ τ *ᵥ v = 0 → v = 0 by
    intro v w hvw
    exact sub_eq_zero.1 (H _ (by rw [mulVec_sub, hvw, sub_self]))
  intro v hv
  obtain ⟨u, hu⟩ : ∃ u : Fin g → ℂ,
      cmat γ *ᵥ Sum.elim (τ *ᵥ v) v = Sum.elim u (0 : Fin g → ℂ) := by
    have := congrArg (· *ᵥ v) (cmat_mul_fromRows γ τ)
    simp only [← mulVec_mulVec, fromRows_mulVec, one_mulVec, hv] at this
    exact ⟨_, this⟩
  have hu' : cmat γ *ᵥ Sum.elim (star (τ *ᵥ v)) (star v) = Sum.elim (star u) 0 := by
    funext i
    have h1 := congrArg (starRingEnd ℂ) (congrFun hu i)
    have h2 : (Sum.elim (star u) 0 : Fin g ⊕ Fin g → ℂ) i =
        starRingEnd ℂ ((Sum.elim u 0 : Fin g ⊕ Fin g → ℂ) i) := by
      rcases i with i | i <;> simp
    rw [h2, ← h1]
    generalize τ *ᵥ v = w
    simp [mulVec, dotProduct, cmat, Fintype.sum_sum_type]
  have h0 : Sum.elim (star (τ *ᵥ v)) (star v) ⬝ᵥ (J (Fin g) ℂ *ᵥ Sum.elim (τ *ᵥ v) v) = 0 := by
    rw [← cmat_symp γ, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
      hu, hu', form_J]
    simp
  rw [form_J] at h0
  have h1 : (star v ⬝ᵥ (τ *ᵥ v)).im = 0 := by
    have : star (τ *ᵥ v) ⬝ᵥ v = star (star v ⬝ᵥ (τ *ᵥ v)) := by
      rw [← star_dotProduct]
    rw [this] at h0
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at this
    linarith
  rw [im_form hτ.isSymm] at h1
  have n₁ := hτ.posDef.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).re)
  have n₂ := hτ.posDef.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).im)
  simp only [star_trivial] at n₁ n₂
  have r : (fun i => (v i).re) = 0 := by
    by_contra h
    linarith [hτ.dotProduct_pos h]
  have s : (fun i => (v i).im) = 0 := by
    by_contra h
    linarith [hτ.dotProduct_pos h]
  funext i
  exact Complex.ext (congrFun r i) (congrFun s i)

theorem cmat_mul_fromRows_inv (γ : Sp g) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : IsSiegel τ) :
    cmat γ * fromRows τ (1 : Matrix (Fin g) (Fin g) ℂ) * (den γ τ)⁻¹ = fromRows (moeb γ τ) (1 : Matrix (Fin g) (Fin g) ℂ) := by
  rw [cmat_mul_fromRows, fromRows_mul, moeb,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (isUnit_den γ hτ))]

theorem fromRows_J (τ : Matrix (Fin g) (Fin g) ℂ) :
    (fromRows τ (1 : Matrix (Fin g) (Fin g) ℂ))ᵀ * J (Fin g) ℂ *
      fromRows τ (1 : Matrix (Fin g) (Fin g) ℂ) = τ - τᵀ := by
  rw [transpose_fromRows, J, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

theorem isSymm_moeb (γ : Sp g) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : IsSiegel τ) :
    (moeb γ τ).IsSymm := by
  have h := fromRows_J (moeb γ τ)
  rw [← cmat_mul_fromRows_inv γ hτ, transpose_mul, transpose_mul] at h
  have h2 : (den γ τ)⁻¹ᵀ * ((fromRows τ (1 : Matrix (Fin g) (Fin g) ℂ))ᵀ * (cmat γ)ᵀ) *
      J (Fin g) ℂ * (cmat γ * fromRows τ (1 : Matrix (Fin g) (Fin g) ℂ) * (den γ τ)⁻¹) =
      (den γ τ)⁻¹ᵀ * ((fromRows τ (1 : Matrix (Fin g) (Fin g) ℂ))ᵀ *
        ((cmat γ)ᵀ * J (Fin g) ℂ * cmat γ) * fromRows τ (1 : Matrix (Fin g) (Fin g) ℂ)) *
        (den γ τ)⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [h2, cmat_symp, fromRows_J, hτ.isSymm.eq] at h
  simp only [sub_self, Matrix.mul_zero, Matrix.zero_mul] at h
  exact (sub_eq_zero.1 h.symm).symm

theorem tauU_symPart {A : Matrix (Fin g) (Fin g) ℂ} (hA : A.IsSymm) : tauU (symPart A) = A := by
  ext i j
  simp [tauU, symPart, hA.apply]

theorem per_eq (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) :
    per τ x = (fun i => (x i : ℂ)) ᵥ* fromRows τ (1 : Matrix (Fin g) (Fin g) ℂ) := by
  rw [vecMul_fromRows, per]
  simp only [vecMul_one]
  rfl

theorem per_moeb (γ : Sp g) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : IsSiegel τ) (x : Fl g) :
    per (moeb γ τ) (x ᵥ* (γ⁻¹).mat) = per τ x ᵥ* (den γ τ)⁻¹ := by
  have : (fun i => ((x ᵥ* (γ⁻¹).mat) i : ℂ)) = (fun i => (x i : ℂ)) ᵥ* cmat γ⁻¹ := by
    funext i
    simp only [vecMul, dotProduct, cmat, map_apply]
    push_cast
    rfl
  rw [per_eq, per_eq, this, ← cmat_mul_fromRows_inv γ hτ, vecMul_vecMul, vecMul_vecMul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, cmat_inv_mul, Matrix.one_mul]

theorem moeb_inj (γ : Sp g) {τ σ : Matrix (Fin g) (Fin g) ℂ} (hτ : IsSiegel τ) (hσ : IsSiegel σ)
    (h : moeb γ τ = moeb γ σ) : τ = σ := by
  have h1 := cmat_mul_fromRows_inv γ hτ
  rw [h, ← cmat_mul_fromRows_inv γ hσ] at h1
  have h2 := congrArg (cmat γ⁻¹ * ·) h1
  simp only [← Matrix.mul_assoc, cmat_inv_mul, Matrix.one_mul, fromRows_mul] at h2
  obtain ⟨h3, h4⟩ := fromRows_inj h2
  have h5 := congrArg (· * den γ τ) h3
  simp only [← h4, Matrix.mul_assoc,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 (isUnit_den γ hτ)), Matrix.mul_one] at h5
  exact h5

theorem inv_rat (γ : Sp g) (hγ : ∀ i k, ∃ r : ℚ, γ.mat i k = r) (i k) :
    ∃ r : ℚ, (γ⁻¹).mat i k = r := by
  choose A hA using hγ
  have e : γ.mat = (Matrix.of A).map (Rat.castHom ℝ) := by ext i k; simp [hA]
  have hJ : (J (Fin g) ℚ).map (Rat.castHom ℝ) = J (Fin g) ℝ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [J, Matrix.one_apply, apply_ite]
  have h : (γ⁻¹).mat = -J (Fin g) ℝ * γ.matᵀ * J (Fin g) ℝ := SymplecticGroup.coe_inv γ
  refine ⟨(-J (Fin g) ℚ * (Matrix.of A)ᵀ * J (Fin g) ℚ) i k, ?_⟩
  rw [h, e, ← hJ, ← transpose_map, Matrix.neg_mul, Matrix.neg_mul, Matrix.neg_mul, Matrix.neg_mul,
    ← Matrix.map_mul, ← Matrix.map_mul]
  simp

theorem isLat_latAct (γ : Sp g) {M : Submodule ℤ (Fl g)} (hM : IsLat M) : IsLat (latAct M γ) := by
  obtain ⟨hd, hz⟩ := hM
  have h1 : (γ⁻¹).mat * γ.mat = 1 := congrArg Subtype.val (inv_mul_cancel γ)
  have h2 : γ.mat * (γ⁻¹).mat = 1 := congrArg Subtype.val (mul_inv_cancel γ)
  let e : Fl g ≃ₗ[ℝ] Fl g := LinearEquiv.ofLinear (vecMulLinear γ.mat) (vecMulLinear (γ⁻¹).mat)
    (LinearMap.ext fun x => by simp [h1]) (LinearMap.ext fun x => by simp [h2])
  have : latAct M γ = ZLattice.comap ℝ M e.toContinuousLinearEquiv.toLinearMap := by
    ext x
    simp only [latAct, ZLattice.comap, Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [e, h1] using hy
    · intro hx
      exact ⟨_, hx, by simp [e, h2]⟩
  rw [this]
  exact ⟨inferInstance, inferInstance⟩

theorem sameOrbit_actU_iff : ∀ g : ℕ, ∀ γ : Sp g, (∀ i k, ∃ r : ℚ, γ.mat i k = r) →
    ∀ M : Submodule ℤ (Fl g), IsRatLat M → IsRatLat (latAct M γ) ∧
      ∀ P ∈ cov (siegel g) g, ∀ Q ∈ cov (siegel g) g,
        SameOrbit tauU M P Q ↔ SameOrbit tauU (latAct M γ) (actU γ P) (actU γ Q) := by
  intro g γ hγ M hM
  refine ⟨⟨isLat_latAct γ hM.1, ?_⟩, fun P hP Q hQ => ?_⟩
  · rintro _ ⟨l, hl, rfl⟩ k
    choose a ha using hM.2 l hl
    choose B hB using inv_rat γ hγ
    refine ⟨∑ i, a i * B i k, ?_⟩
    change ∑ i, l i * (γ⁻¹).mat i k = _
    simp only [ha, hB]
    push_cast
    rfl
  have hP' : IsSiegel (tauU P.1) := hP.1
  have hQ' : IsSiegel (tauU Q.1) := hQ.1
  have key : ∀ l : Fl g, transl tauU (l ᵥ* (γ⁻¹).mat) (actU γ P) = actU γ (transl tauU l P) := by
    intro l
    simp only [transl, actU, tauU_symPart (isSymm_moeb γ hP'), per_moeb γ hP', add_vecMul]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l ᵥ* (γ⁻¹).mat, ⟨l, hl, rfl⟩, (key l).symm⟩
  · rintro ⟨_, ⟨l, hl, rfl⟩, h⟩
    refine ⟨l, hl, ?_⟩
    have h' : actU γ Q = actU γ (transl tauU l P) := h.trans (key l)
    have h1 : tauU Q.1 = tauU P.1 := by
      have := congrArg (fun R => tauU R.1) h'
      simp only [actU, transl, tauU_symPart (isSymm_moeb γ hP'),
        tauU_symPart (isSymm_moeb γ hQ')] at this
      exact moeb_inj γ hQ' hP' this
    refine Prod.ext (Subtype.ext h1) ?_
    have h2 := congrArg (fun R => R.2 ᵥ* den γ (tauU P.1)) h'
    simp only [actU, transl, h1, vecMul_vecMul,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 (isUnit_den γ hP')), vecMul_one] at h2
    exact h2

end GlobalTheory.SymplecticOrbit
