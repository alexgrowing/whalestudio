import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SubConjTransposeOfSymm

noncomputable section

open Complex Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.LagSplit

section Defs

variable {R M V : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V]

def IsLagSection (ω : LinearMap.BilinForm R M) (π : M →ₗ[R] V) (σ : V →ₗ[R] M) : Prop :=
  (∀ z, π (σ z) = z) ∧ ∀ z w, ω (σ z) (σ w) = 0

def KerIsotropic (ω : LinearMap.BilinForm R M) (π : M →ₗ[R] V) : Prop :=
  ∀ m m', π m = 0 → π m' = 0 → ω m m' = 0

def beta (ω : LinearMap.BilinForm R M) (σ σ' : V →ₗ[R] M) : LinearMap.BilinForm R V :=
  LinearMap.compl₁₂ ω σ σ'

@[simp] theorem beta_apply (ω : LinearMap.BilinForm R M) (σ σ' : V →ₗ[R] M) (z w : V) :
    beta ω σ σ' z w = ω (σ z) (σ' w) := rfl

end Defs

section Concrete

variable {g : ℕ}

def omegaCx (g : ℕ) : LinearMap.BilinForm ℂ (Fin g ⊕ Fin g → ℂ) :=
  LinearMap.mk₂ ℂ (fun a b => ∑ i, (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i)))
    (fun a a' b => by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by simp; ring)
    (fun c a b => by
      rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring)
    (fun a b b' => by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by simp; ring)
    (fun c a b => by
      rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring)

theorem omegaCx_apply (a b : Fin g ⊕ Fin g → ℂ) :
    omegaCx g a b = ∑ i, (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i)) := rfl

theorem omegaCx_eq_dot (a b : Fin g ⊕ Fin g → ℂ) :
    omegaCx g a b = (a ∘ Sum.inl) ⬝ᵥ (b ∘ Sum.inr) - (a ∘ Sum.inr) ⬝ᵥ (b ∘ Sum.inl) := by
  simp [omegaCx_apply, dotProduct, Finset.sum_sub_distrib]

theorem omegaCx_elim (m n m' n' : Fin g → ℂ) :
    omegaCx g (Sum.elim m n) (Sum.elim m' n') = m ⬝ᵥ n' - n ⬝ᵥ m' := by
  simp [omegaCx_eq_dot]

theorem omegaCx_intCast (a b : Fin g ⊕ Fin g → ℤ) :
    omegaCx g (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) = (omegaStd a b : ℂ) := by
  simp [omegaCx_apply, omegaStd]

theorem eq_omegaCx_of_intCast (B : LinearMap.BilinForm ℂ (Fin g ⊕ Fin g → ℂ))
    (hB : ∀ a b : Fin g ⊕ Fin g → ℤ,
      B (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) = (omegaStd a b : ℂ)) : B = omegaCx g := by
  classical
  refine LinearMap.BilinForm.ext_basis (Pi.basisFun ℂ _) fun i j => ?_
  have e : ∀ i : Fin g ⊕ Fin g, Pi.basisFun ℂ (Fin g ⊕ Fin g) i =
      fun k => (((Pi.single i 1 : Fin g ⊕ Fin g → ℤ) k : ℤ) : ℂ) := by
    intro i; ext k; simp [Pi.single_apply]
  rw [e, e, hB, omegaCx_intCast]

def perProj (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun u := u ∘ Sum.inl + τ *ᵥ (u ∘ Sum.inr)
  map_add' u v := by
    have h1 : (u + v) ∘ Sum.inl = u ∘ Sum.inl + v ∘ Sum.inl := rfl
    have h2 : (u + v) ∘ Sum.inr = u ∘ Sum.inr + v ∘ Sum.inr := rfl
    rw [h1, h2, Matrix.mulVec_add]; abel
  map_smul' c u := by
    have h1 : (c • u) ∘ Sum.inl = c • (u ∘ Sum.inl) := rfl
    have h2 : (c • u) ∘ Sum.inr = c • (u ∘ Sum.inr) := rfl
    rw [h1, h2, Matrix.mulVec_smul, smul_add]; rfl

theorem perProj_apply (τ : Matrix (Fin g) (Fin g) ℂ) (u : Fin g ⊕ Fin g → ℂ) :
    perProj τ u = u ∘ Sum.inl + τ *ᵥ (u ∘ Sum.inr) := rfl

theorem perProj_elim (τ : Matrix (Fin g) (Fin g) ℂ) (m n : Fin g → ℂ) :
    perProj τ (Sum.elim m n) = m + τ *ᵥ n := by
  simp [perProj_apply]

def secL (g : ℕ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g ⊕ Fin g → ℂ) where
  toFun z := Sum.elim z 0
  map_add' z w := by ext (i | i) <;> simp
  map_smul' c z := by ext (i | i) <;> simp

theorem secL_apply (z : Fin g → ℂ) : secL g z = Sum.elim z 0 := rfl

def secH (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g ⊕ Fin g → ℂ) where
  toFun z := Sum.elim (-(τ.map star *ᵥ (((2 * I) • imC τ)⁻¹ *ᵥ z))) (((2 * I) • imC τ)⁻¹ *ᵥ z)
  map_add' z w := by ext (i | i) <;> simp [Matrix.mulVec_add, add_comm]
  map_smul' c z := by ext (i | i) <;> simp [Matrix.mulVec_smul]

theorem secH_apply (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : secH τ z =
    Sum.elim (-(τ.map star *ᵥ (((2 * I) • imC τ)⁻¹ *ᵥ z))) (((2 * I) • imC τ)⁻¹ *ᵥ z) := rfl

theorem dot_mulVec_symm {A : Matrix (Fin g) (Fin g) ℂ} (hA : A.IsSymm) (x y : Fin g → ℂ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (A *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq]

theorem perProj_eq_zero_iff (τ : Matrix (Fin g) (Fin g) ℂ) (u : Fin g ⊕ Fin g → ℂ) :
    perProj τ u = 0 ↔ u ∘ Sum.inl = -(τ *ᵥ (u ∘ Sum.inr)) := by
  rw [perProj_apply, add_eq_zero_iff_eq_neg]

theorem secL_isLagSection (τ : Matrix (Fin g) (Fin g) ℂ) :
    IsLagSection (omegaCx g) (perProj τ) (secL g) :=
  ⟨fun z => by simp [secL_apply, perProj_elim], fun z w => by simp [secL_apply, omegaCx_elim]⟩

theorem sub_map_star (τ : Matrix (Fin g) (Fin g) ℂ) : τ - τ.map star = (2 * I) • imC τ := by
  ext i j
  simp only [Matrix.sub_apply, imC, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp; ring

theorem imC_mul_inv {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    imC τ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) = 1 := by
  have h := congrArg (fun A : Matrix (Fin g) (Fin g) ℝ => A.map Complex.ofRealHom)
    (Matrix.mul_nonsing_inv _ hY)
  simp only [Matrix.map_mul] at h
  rw [Matrix.map_one _ (by simp) (by simp)] at h
  exact h

theorem imC_inv {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    (imC τ)⁻¹ = ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) :=
  Matrix.inv_eq_right_inv (imC_mul_inv hY)

theorem two_I_imC_mul {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    ((2 * I) • imC τ) * ((2 * I)⁻¹ • (imC τ)⁻¹) = 1 := by
  have h2 : (2 * I : ℂ) ≠ 0 := by simp
  rw [imC_inv hY, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h2, one_smul,
    imC_mul_inv hY]

theorem two_I_imC_inv {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    ((2 * I) • imC τ)⁻¹ = (2 * I)⁻¹ • (imC τ)⁻¹ :=
  Matrix.inv_eq_right_inv (two_I_imC_mul hY)

theorem two_I_imC_mul_inv {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    ((2 * I) • imC τ) * ((2 * I) • imC τ)⁻¹ = 1 := by
  rw [two_I_imC_inv hY, two_I_imC_mul hY]

theorem two_I_imC_inv_mul {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    ((2 * I) • imC τ)⁻¹ * ((2 * I) • imC τ) = 1 :=
  mul_eq_one_comm.mp (two_I_imC_mul_inv hY)

theorem perProj_secH {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det)
    (z : Fin g → ℂ) : perProj τ (secH τ z) = z := by
  rw [secH_apply, perProj_elim, neg_add_eq_sub, ← Matrix.sub_mulVec, sub_map_star,
    Matrix.mulVec_mulVec, two_I_imC_mul_inv hY, Matrix.one_mulVec]

theorem star_mulVec_map (τ : Matrix (Fin g) (Fin g) ℂ) (n : Fin g → ℂ) :
    star (τ *ᵥ n) = τ.map star *ᵥ star n := by
  ext i; simp [Matrix.mulVec, dotProduct]

theorem mem_range_secH_iff {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det)
    (u : Fin g ⊕ Fin g → ℂ) : u ∈ LinearMap.range (secH τ) ↔ perProj τ (star u) = 0 := by
  have key : perProj τ (star u) = 0 ↔ u ∘ Sum.inl = -(τ.map star *ᵥ (u ∘ Sum.inr)) := by
    rw [perProj_eq_zero_iff, ← star_inj, star_neg, star_mulVec_map]
    have h1 : star ((star u) ∘ Sum.inl) = u ∘ (Sum.inl : Fin g → _) := by ext i; simp
    have h2 : star ((star u) ∘ Sum.inr) = u ∘ (Sum.inr : Fin g → _) := by ext i; simp
    rw [h1, h2]
  rw [key]
  constructor
  · rintro ⟨z, rfl⟩
    simp [secH_apply]
  · intro h
    refine ⟨((2 * I) • imC τ) *ᵥ (u ∘ Sum.inr), ?_⟩
    rw [secH_apply, Matrix.mulVec_mulVec (u ∘ Sum.inr), two_I_imC_inv_mul hY, Matrix.one_mulVec, ← h]
    ext (i | i) <;> rfl

theorem eq_secH_of_conj_mem_ker {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det)
    {u : Fin g ⊕ Fin g → ℂ} {z : Fin g → ℂ} (hu : perProj τ u = z) (hc : perProj τ (star u) = 0) :
    u = secH τ z := by
  obtain ⟨v, rfl⟩ := (mem_range_secH_iff hY u).mpr hc
  rw [perProj_secH hY] at hu
  rw [hu]

theorem secH_equivariant {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det)
    (A : (Fin g ⊕ Fin g → ℂ) → (Fin g ⊕ Fin g → ℂ)) (B : (Fin g → ℂ) → (Fin g → ℂ)) (hB : B 0 = 0)
    (hA : ∀ u, A (star u) = star (A u)) (hAB : ∀ u, perProj τ (A u) = B (perProj τ u))
    (z : Fin g → ℂ) : secH τ (B z) = A (secH τ z) := by
  refine (eq_secH_of_conj_mem_ker hY ?_ ?_).symm
  · rw [hAB, perProj_secH hY]
  · rw [← hA, hAB, (mem_range_secH_iff hY _).mp ⟨z, rfl⟩, hB]

theorem beta_secL (σ : (Fin g → ℂ) →ₗ[ℂ] (Fin g ⊕ Fin g → ℂ)) (z w : Fin g → ℂ) :
    beta (omegaCx g) σ (secL g) z w = -((σ z ∘ Sum.inr) ⬝ᵥ w) := by
  simp [omegaCx_eq_dot, secL_apply]

theorem beta_secH_secL' {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (hY : IsUnit (τ.map Complex.im).det) (z w : Fin g → ℂ) :
    beta (omegaCx g) (secH τ) (secL g) z w = -(2 * I)⁻¹ * (z ⬝ᵥ (imC τ)⁻¹ *ᵥ w) := by
  have hs : (imC τ).IsSymm := (hτ.map _).map _
  rw [beta_secL, secH_apply, Sum.elim_comp_inr, two_I_imC_inv hY, Matrix.smul_mulVec,
    smul_dotProduct, dot_mulVec_symm hs.inv, smul_eq_mul, neg_mul]

theorem beta_secH_secL {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (hY : IsUnit (τ.map Complex.im).det) (z w : Fin g → ℂ) :
    beta (omegaCx g) (secH τ) (secL g) z w =
      -(2 * I)⁻¹ * (z ⬝ᵥ ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ w) := by
  rw [beta_secH_secL' hτ hY, imC_inv hY]

end Concrete

section General

variable {R M V : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V]
  {ω : LinearMap.BilinForm R M} {π : M →ₗ[R] V} {σ σ' σ'' : V →ₗ[R] M}

variable {O : Type*} [CommRing O] [StarRing O] [Module O M] [Module O V]

end General

end GlobalTheory.LagSplit
