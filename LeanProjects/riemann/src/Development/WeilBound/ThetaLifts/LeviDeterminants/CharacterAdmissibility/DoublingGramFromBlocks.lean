import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SiegelTransportAlg

noncomputable section

namespace PositivityTheory.ThKF0.Chr

open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {β β₁ μ ν : Type} [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁] [Fintype μ] [DecidableEq μ]
  [Fintype ν] [DecidableEq ν]

variable (c) in

structure Fr (J : Matrix β β E) (J₁ : Matrix β₁ β₁ E) (H : Matrix μ μ E) (ι : Matrix β β₁ E) (Z : Matrix β μ E)
    (π : Matrix β₁ β E) (ρ : Matrix μ β E) : Prop where
  one : ι * π + Z * ρ = 1
  pi : π * ι = 1
  pz : π * Z = 0
  ri : ρ * ι = 0
  rz : ρ * Z = 1
  gii : ιᵀ * J * ι.map c = J₁
  giz : ιᵀ * J * Z.map c = 0
  gzi : Zᵀ * J * ι.map c = 0
  gzz : Zᵀ * J * Z.map c = H

abbrev dd2 {a b : Type} (A : Matrix a b E) : Matrix (a ⊕ a) (b ⊕ b) E := fromBlocks A 0 0 A

variable {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {H : Matrix μ μ E} {ι : Matrix β β₁ E} {Z : Matrix β μ E}
  {π : Matrix β₁ β E} {ρ : Matrix μ β E}

theorem doubling_gram_fromBlocks {a b : Type} (A : Matrix β a E) (B : Matrix β b E) :
    (dd2 A)ᵀ * dbl J * (dd2 B).map c = fromBlocks (Aᵀ * J * B.map c) 0 0 (-(Aᵀ * J * B.map c)) := by
  simp only [dbl, fromBlocks_transpose, fromBlocks_map, Matrix.map_zero _ (map_zero c), fromBlocks_multiply]
  simp

theorem Fr.dbl (h : Fr c J J₁ H ι Z π ρ) : Fr c (dbl J) (dbl J₁) (dbl H) (dd2 ι) (dd2 Z) (dd2 π) (dd2 ρ) where
  one := by simp [fromBlocks_multiply, fromBlocks_add, h.one]
  pi := by simp [fromBlocks_multiply, h.pi]
  pz := by simp [fromBlocks_multiply, h.pz]
  ri := by simp [fromBlocks_multiply, h.ri]
  rz := by simp [fromBlocks_multiply, h.rz]
  gii := by rw [doubling_gram_fromBlocks, h.gii]; rfl
  giz := by rw [doubling_gram_fromBlocks, h.giz]; simp
  gzi := by rw [doubling_gram_fromBlocks, h.gzi]; simp
  gzz := by rw [doubling_gram_fromBlocks, h.gzz]; rfl

theorem Fr.mul (h : Fr c J J₁ H ι Z π ρ) (g g' : Matrix β₁ β₁ E) (k k' : Matrix μ μ E) :
    (ι * g * π + Z * k * ρ) * (ι * g' * π + Z * k' * ρ) = ι * (g * g') * π + Z * (k * k') * ρ := by
  have e : ∀ {a b a' b' : Type} [Fintype a] [Fintype b] [Fintype a'] [Fintype b'] (A : Matrix β a E) (x : Matrix a b E)
      (B : Matrix b β E) (A' : Matrix β a' E) (x' : Matrix a' b' E) (B' : Matrix b' β E),
      A * x * B * (A' * x' * B') = A * x * (B * A') * x' * B' := fun A x B A' x' B' => by simp only [Matrix.mul_assoc]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e, e, e, e, h.pi, h.pz, h.ri, h.rz]
  simp [Matrix.mul_assoc]

theorem Fr.gram (h : Fr c J J₁ H ι Z π ρ) (g : Matrix β₁ β₁ E) (k : Matrix μ μ E) :
    (ι * g * π + Z * k * ρ)ᵀ * J * (ι * g * π + Z * k * ρ).map c =
      πᵀ * (gᵀ * J₁ * g.map c) * π.map c + ρᵀ * (kᵀ * H * k.map c) * ρ.map c := by
  have e : ∀ {a a' : Type} [Fintype a] [Fintype a'] (A : Matrix β a E) (x : Matrix a a E)
      (B : Matrix a β E) (A' : Matrix β a' E) (x' : Matrix a' a' E) (B' : Matrix a' β E),
      (A * x * B)ᵀ * J * (A' * x' * B').map c = Bᵀ * (xᵀ * (Aᵀ * J * A'.map c) * x'.map c) * B'.map c :=
    fun A x B A' x' B' => by simp only [transpose_mul, map_mul', Matrix.mul_assoc]
  rw [Matrix.map_add _ (map_add c), transpose_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e, e, e, e,
    h.gii, h.giz, h.gzi, h.gzz]
  simp

def Fr.emb (h : Fr c J J₁ H ι Z π ρ) : UG c J₁ × UG c H →* UG c J where
  toFun p := ⟨⟨ι * p.1.1.1 * π + Z * p.2.1.1 * ρ, ι * (p.1.1⁻¹).1 * π + Z * (p.2.1⁻¹).1 * ρ,
    by rw [h.mul, Units.mul_inv, Units.mul_inv, Matrix.mul_one, Matrix.mul_one, h.one],
    by rw [h.mul, Units.inv_mul, Units.inv_mul, Matrix.mul_one, Matrix.mul_one, h.one]⟩, by
      have e := h.gram 1 1
      rw [Matrix.mul_one, Matrix.mul_one, h.one, transpose_one, transpose_one, transpose_one, map_one', map_one', map_one',
        Matrix.mul_one, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, Matrix.one_mul] at e
      refine (h.gram _ _).trans (Eq.trans ?_ e.symm)
      rw [show p.1.1.1ᵀ * J₁ * p.1.1.1.map c = J₁ from p.1.2, show p.2.1.1ᵀ * H * p.2.1.1.map c = H from p.2.2]⟩
  map_one' := Subtype.ext (Units.ext (by
    show ι * 1 * π + Z * 1 * ρ = 1
    rw [Matrix.mul_one, Matrix.mul_one, h.one]))
  map_mul' p q := Subtype.ext (Units.ext (h.mul _ _ _ _).symm)

theorem Fr.emb_i (h : Fr c J J₁ H ι Z π ρ) (p : UG c J₁ × UG c H) : (h.emb p).1.1 * ι = ι * p.1.1.1 := by
  show (ι * p.1.1.1 * π + Z * p.2.1.1 * ρ) * ι = _
  rw [Matrix.add_mul, Matrix.mul_assoc, h.pi, Matrix.mul_assoc (Z * _), h.ri]
  simp

theorem Fr.embeddingAtLocalFactor (h : Fr c J J₁ H ι Z π ρ) (p : UG c J₁ × UG c H) : (h.emb p).1.1 * Z = Z * p.2.1.1 := by
  show (ι * p.1.1.1 * π + Z * p.2.1.1 * ρ) * Z = _
  rw [Matrix.add_mul, Matrix.mul_assoc, h.pz, Matrix.mul_assoc (Z * _), h.rz]
  simp

theorem Fr.continuous_emb [TopologicalSpace E] [IsTopologicalRing E] (h : Fr c J J₁ H ι Z π ρ) :
    Continuous fun g : UG c J₁ => h.emb (g, 1) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact ((continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
      continuous_const).add (continuous_const (y := Z * (1 : Matrix μ μ E) * ρ))
  · exact ((continuous_const.matrix_mul (Units.continuous_coe_inv.comp continuous_subtype_val)).matrix_mul
      continuous_const).add (continuous_const (y := Z * (1 : Matrix μ μ E) * ρ))

abbrev hyp (ν : Type) [DecidableEq ν] (η : ℤˣ) : Matrix (ν ⊕ ν) (ν ⊕ ν) E := fromBlocks 0 1 (((η : ℤ) : E) • 1) 0

theorem eta_sq (η : ℤˣ) : ((η : ℤ) : E) * ((η : ℤ) : E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

theorem exists_gamma0 (η : ℤˣ) : ∃ γ : UG c (dbl (hyp ν η : Matrix _ _ E)), γ.1.1 * (diagCols (ν ⊕ ν) : Matrix _ _ E) =
    dd2 (fromRows (1 : Matrix ν ν E) (0 : Matrix ν ν E)) * (fromBlocks 1 0 0 (((η : ℤ) : E) • 1) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) := by
  set a : E := ((η : ℤ) : E) with ha
  have h2 : a * a = 1 := eta_sq η
  have hca : (a • (1 : Matrix ν ν E)).map c = a • 1 := by
    ext i j; by_cases h : i = j <;> simp [h, ha, Matrix.one_apply]
  have hm1 : (-1 : Matrix ν ν E).map c = -1 := by rw [Matrix.map_neg _ (map_neg c), map_one']
  have hz : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
  let g : Matrix ((ν ⊕ ν) ⊕ (ν ⊕ ν)) ((ν ⊕ ν) ⊕ (ν ⊕ ν)) E :=
    fromBlocks (fromBlocks 1 0 0 1) (fromBlocks 0 0 0 (-1)) (fromBlocks 0 0 (-1) 0) (fromBlocks 0 (a • 1) 1 0)
  let g' : Matrix ((ν ⊕ ν) ⊕ (ν ⊕ ν)) ((ν ⊕ ν) ⊕ (ν ⊕ ν)) E :=
    fromBlocks (fromBlocks 1 0 0 1) (fromBlocks 0 0 (a • 1) 0) (fromBlocks 1 0 0 0) (fromBlocks 0 1 (a • 1) 0)
  refine ⟨⟨⟨g, g', ?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [g, g', fromBlocks_multiply, fromBlocks_add, ← fromBlocks_one, ← fromBlocks_zero]
    simp [smul_smul, h2]
  · simp only [g, g', fromBlocks_multiply, fromBlocks_add, ← fromBlocks_one, ← fromBlocks_zero]
    simp [smul_smul, h2]
  · show gᵀ * _ * g.map c = _
    simp only [g, hyp, ← ha, dbl, fromBlocks_transpose, fromBlocks_map, map_one', hm1, hz, hca, fromBlocks_neg, ← fromBlocks_zero,
      fromBlocks_multiply, fromBlocks_add]
    simp [smul_smul, h2]
  · show g * diagCols (E := E) (ν ⊕ ν) = _
    simp only [g, diagCols, fromBlocks_mul_fromRows, Matrix.mul_one, fromBlocks_add, fromBlocks_multiply]
    ext ((i | i) | (i | i)) (j | j) <;> simp

theorem Fr.exists_gamma {η : ℤˣ} {X Y : Matrix β ν E} {ρ : Matrix (ν ⊕ ν) β E}
    (h : Fr c J J₁ (hyp ν η) ι (fromCols X Y) π ρ) :
    ∃ (γ : UG c (GlobalTheory.WeilM.dbl J)) (s : Matrix (β₁ ⊕ (ν ⊕ ν)) β E) (s' : Matrix β (β₁ ⊕ (ν ⊕ ν)) E), s * s' = 1 ∧ s' * s = 1 ∧
      γ.1.1 * (diagCols β : Matrix _ _ E) = fromCols (dd2 ι * diagCols (E := E) β₁) (dd2 X) * s := by
  obtain ⟨γ₀, hγ⟩ := exists_gamma0 (c := c) (ν := ν) η
  set s₀ : Matrix (ν ⊕ ν) (ν ⊕ ν) E := fromBlocks 1 0 0 (((η : ℤ) : E) • 1)
  have hs : s₀ * s₀ = 1 := by simp [s₀, fromBlocks_multiply, smul_smul, eta_sq]
  set Z := fromCols X Y
  refine ⟨h.dbl.emb (1, γ₀), fromRows π (s₀ * ρ), fromCols ι (Z * s₀), ?_, ?_, ?_⟩
  · rw [fromRows_mul_fromCols, ← Matrix.mul_assoc π, Matrix.mul_assoc s₀, Matrix.mul_assoc s₀, ← Matrix.mul_assoc ρ,
      h.pi, h.pz, h.ri, h.rz, Matrix.one_mul, hs]
    simp
  · rw [fromCols_mul_fromRows, Matrix.mul_assoc, ← Matrix.mul_assoc s₀, hs, Matrix.one_mul, h.one]
  · have e : (diagCols β : Matrix _ _ E) = dd2 ι * (diagCols (E := E) β₁ * π) + dd2 Z * (diagCols (E := E) (ν ⊕ ν) * ρ) := by
      simp only [diagCols, fromRows_mul, fromBlocks_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
      rw [← h.one]
      ext (i | i) j <;> rfl
    have e2 : dd2 Z * dd2 (fromRows (1 : Matrix ν ν E) (0 : Matrix ν ν E)) = dd2 X := by
      rw [fromBlocks_multiply]
      simp [Z, fromCols_mul_fromRows]
    rw [e, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc _ (dd2 Z), Fr.emb_i, Fr.embeddingAtLocalFactor, fromCols_mul_fromRows,
      Matrix.mul_assoc (dd2 Z), ← Matrix.mul_assoc γ₀.1.1, hγ, ← e2]
    simp only [Matrix.mul_assoc]
    simp

end PositivityTheory.ThKF0.Chr
