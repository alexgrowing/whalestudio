import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.FrobStep

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

section Blocks
variable {n : Type} [Fintype n] [DecidableEq n]

theorem bd4_mul_apply {R : Type*} [CommRing R] (P : Matrix n n R) (Q : Matrix (Fin 4 × n) (Fin 4 × n) R)
    (a : Fin 4) (i : n) (w : Fin 4 × n) : (bd4 P * Q) (a, i) w = ∑ j, P i j * Q (a, j) w := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [bd4]
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [bd4, Ne.symm hb]
  · simp

theorem bd4_mul {R : Type*} [CommRing R] (P Q : Matrix n n R) : bd4 P * bd4 Q = bd4 (P * Q) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [bd4_mul_apply]
  by_cases hab : a = b
  · subst hab
    simp [bd4, Matrix.mul_apply]
  · simp [bd4, hab]

theorem bd4_map {R S : Type*} [Zero R] [Zero S] (f : R → S) (hf : f 0 = 0) (P : Matrix n n R) :
    (bd4 P).map f = bd4 (P.map f) := by
  ext x y
  simp only [Matrix.map_apply, bd4]
  split_ifs
  · rfl
  · exact hf

theorem blockShift_map {R S : Type*} [Zero R] [One R] [Zero S] [One S] (f : R → S) (hf : f 0 = 0) (hf1 : f 1 = 1)
    (k : Fin 4) : (bmv0 (n := n) k : Matrix _ _ R).map f = bmv0 k := by
  ext x y
  simp only [Matrix.map_apply, bmv0]
  split_ifs
  · exact hf1
  · exact hf

end Blocks

theorem sq_sq (d : ℕ) : sq d ^ 2 = -(d : ℂ) := by
  show (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 = -(d : ℂ)
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  push_cast
  ring

theorem lmat_coe {l : ℕ} [Fact l.Prime] {m m' : Type} (d : ℕ) (ι : ℂ ≃+* ℂ_[l]) (δ : MaximalUnramifiedExtension l)
    (hδ : (δ : ℂ_[l]) = ι (sq d)) (A B : Matrix m m' ℚ) :
    (lmat δ A B).map (MaximalUnramifiedExtension l).subtype = (kmat d A B).map ι := by
  ext x y
  simp only [lmat, kmat, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    map_add, map_mul, map_ratCast, hδ]
  simp
  exact Or.inl hδ

theorem hermFrame_of (hF : FrobStep) (hR : RatStep) (hL : LocCore) : Formalism.L2.Th1.Top.FrP.HermFrame := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hcm l _ hl hldK hsq ι σ hσ n _ _ h Λ g₀ g₁ hlat hiso hidx
  obtain ⟨P₀, M₁, M₂, R₁, R₂, c, hc, hg, hRR, hU⟩ :=
    hR a₀ b₀ c₀ dK ha hdK lam hlam hcm l hl hldK hsq n h Λ g₀ g₁ hlat hiso hidx
  obtain ⟨hnorm, δ, hδ, hσδ⟩ := hF l dK hl hldK hcm.2.2.2 hcm.2.2.1 hsq ι σ hσ
  have hδ2 : δ ^ 2 = -(dK : MaximalUnramifiedExtension l) := by
    apply Subtype.ext
    have e1 : ((δ ^ 2 : MaximalUnramifiedExtension l) : ℂ_[l]) = (δ : ℂ_[l]) ^ 2 := rfl
    have e2 : ((-(dK : MaximalUnramifiedExtension l) : MaximalUnramifiedExtension l) : ℂ_[l]) = -(dK : ℂ_[l]) := by simp
    rw [e1, e2, hδ, ← map_pow, sq_sq, map_neg, map_natCast]
  have hmulι : ∀ {p q r : Type} [Fintype q] (A : Matrix p q ℂ) (B : Matrix q r ℂ),
      (A * B).map ι = A.map ι * B.map ι := by
    intro p q r _ A B
    have : (A * B).map (ι : ℂ →+* ℂ_[l]) = A.map (ι : ℂ →+* ℂ_[l]) * B.map (ι : ℂ →+* ℂ_[l]) :=
      Matrix.map_mul
    simpa using this
  have hinj : ∀ {p q : Type}, Function.Injective
      (fun A : Matrix p q (MaximalUnramifiedExtension l) => A.map (MaximalUnramifiedExtension l).subtype) :=
    fun {p q} => Matrix.map_injective Subtype.val_injective
  have hLeq : (lmat δ M₁ M₂).transpose * bd4 (lmat δ R₁ R₂) * lmat δ M₁ (-M₂) =
      (c : MaximalUnramifiedExtension l) • (1 : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) := by
    apply hinj
    have h1 := congrArg (fun A => A.map ι) hRR
    simp only [hmulι, Matrix.transpose_map, bd4_map ι (map_zero ι)] at h1
    simp only [Matrix.map_mul, Matrix.transpose_map, bd4_map (MaximalUnramifiedExtension l).subtype (map_zero _),
      lmat_coe dK ι δ hδ]
    rw [h1]
    ext x y
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp [map_ratCast]
  have hUk : ∀ k : Fin 4, ∃ U₁ U₂ : Matrix (Fin 4 × n) (Fin 4 × n) ℚ,
      (∀ x y, padicNorm l (U₁ x y) ≤ 1 ∧ padicNorm l (U₂ x y) ≤ 1) ∧
      bmv0 k * lmat δ M₁ M₂ = lmat δ M₁ M₂ * lmat δ U₁ U₂ := by
    intro k
    obtain ⟨U₁, U₂, hUn, hUe⟩ := hU k
    refine ⟨U₁, U₂, hUn, ?_⟩
    apply hinj
    have h1 := congrArg (fun A => A.map ι) hUe
    simp only [hmulι, blockShift_map ι (map_zero ι) (map_one ι)] at h1
    simp only [Matrix.map_mul, blockShift_map (MaximalUnramifiedExtension l).subtype (map_zero _) (map_one _),
      lmat_coe dK ι δ hδ]
    exact h1
  obtain ⟨T, Ti, hTTi, hUn⟩ := hL l dK σ δ hl hldK hsq hnorm hδ2 hσδ n M₁ M₂ R₁ R₂ c hc hLeq hUk
  refine ⟨bd4 Ti * lmat δ M₁ M₂, ι lam⁻¹ • (P₀.map ι * T.map (MaximalUnramifiedExtension l).subtype), hUn, ?_⟩
  intro i' i w
  have hγ : (bd4 Ti * lmat δ M₁ M₂).map (MaximalUnramifiedExtension l).subtype =
      bd4 (Ti.map (MaximalUnramifiedExtension l).subtype) * (kmat dK M₁ M₂).map ι := by
    rw [Matrix.map_mul, bd4_map (MaximalUnramifiedExtension l).subtype (map_zero _), lmat_coe dK ι δ hδ]
  have hTT : T.map (MaximalUnramifiedExtension l).subtype * Ti.map (MaximalUnramifiedExtension l).subtype = 1 := by
    rw [← Matrix.map_mul, hTTi, Matrix.map_one _ (map_zero _) (map_one _)]
  have hB : bd4 (ι lam⁻¹ • (P₀.map ι * T.map (MaximalUnramifiedExtension l).subtype)) * bd4 (Ti.map (MaximalUnramifiedExtension l).subtype) =
      bd4 (ι lam⁻¹ • P₀.map ι) := by
    rw [bd4_mul, Matrix.smul_mul, Matrix.mul_assoc, hTT, Matrix.mul_one]
  have hsm : ∀ (x : ℂ_[l]) (Q : Matrix n n ℂ_[l]), bd4 (x • Q) = x • bd4 Q := by
    intro x Q
    ext p q
    simp only [bd4, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hG : (gmat g₁).map ι = bd4 (ι lam⁻¹ • P₀.map ι) * (kmat dK M₁ M₂).map ι := by
    rw [hg, hsm, Matrix.smul_mul, ← bd4_map ι (map_zero ι), ← hmulι]
    ext p q
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  calc ∑ j, (ι lam⁻¹ • (P₀.map ι * T.map (MaximalUnramifiedExtension l).subtype)) i j *
        (((bd4 Ti * lmat δ M₁ M₂) (i', j) w : MaximalUnramifiedExtension l) : ℂ_[l])
      = (bd4 (ι lam⁻¹ • (P₀.map ι * T.map (MaximalUnramifiedExtension l).subtype)) *
          (bd4 Ti * lmat δ M₁ M₂).map (MaximalUnramifiedExtension l).subtype) (i', i) w := by
        rw [bd4_mul_apply]
        rfl
    _ = (gmat g₁).map ι (i', i) w := by
        rw [hγ, ← Matrix.mul_assoc, hB, hG]
    _ = ι (g₁.symm (Pi.single w 1) (i', i)) := rfl

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
