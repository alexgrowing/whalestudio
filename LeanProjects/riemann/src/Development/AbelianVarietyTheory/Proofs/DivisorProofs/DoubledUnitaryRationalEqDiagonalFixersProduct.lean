import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFactorisationDoubledUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCornerUnitOfRightInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSkewDetUnitOfAvoidanceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelUnipotentAntidiagonalCornerStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.ThetaRatGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F))

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem exists_eval_ne (ψ : Polynomial E) (hψ : ψ ≠ 0) : ∃ t : F, ψ.eval (algebraMap F E t) ≠ 0 := by
  classical
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  have hinf : (Set.range (algebraMap F E)).Infinite := Set.infinite_range_of_injective (algebraMap F E).injective
  obtain ⟨y, ⟨t, rfl⟩, hy⟩ := hinf.exists_notMem_finset ψ.roots.toFinset
  refine ⟨t, fun h => hy ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hψ]
  exact h

theorem hyp1 : ∀ ψ : Polynomial E, (∀ (Ω : Type) [Field Ω] (φ : E →+* Ω), φ 1 = 1 → ψ.map φ ≠ 0) →
    ∃ t : F, IsUnit ((1 : E) * ψ.eval (algebraMap F E t) + (1 - 1)) := by
  intro ψ h
  have hψ : ψ ≠ 0 := by simpa using h E (RingHom.id E) (map_one _)
  obtain ⟨t, ht⟩ := exists_eval_ne (F := F) ψ hψ
  exact ⟨t, by simpa using ht⟩

theorem invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ ρ : E, ρ ≠ 0 ∧ σ ρ = -ρ := by
  have hne : σ ≠ AlgHom.id F E := by
    intro hσ
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := h.2.1
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := h.2.2.2 τ x
    rw [hσ] at this
    simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    exact hne (AlgHom.ext hc)
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, invol h]
  ring

variable (F) in
theorem incM_mul {m n k : Type} [Fintype n] (A : Matrix m n E) (B : Matrix n k E) :
    incM F (A * B) = incM F A * incM F B := Matrix.map_mul

variable (F) in
theorem incM_dbl {β : Type} (J : Matrix β β E) : incM F (dbl J) = dbl (incM F J) := by
  ext i j
  cases i <;> cases j <;> simp [incM, dbl]

theorem incM_map (σ : E →ₐ[F] E) {m n : Type} (A : Matrix m n E) : (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j
  simp [incM, cA_inclR]

variable (F) in
theorem incM_transpose {m n : Type} (A : Matrix m n E) : (incM F A)ᵀ = incM F Aᵀ := rfl

variable (F) in
theorem incM_diag {β : Type} [DecidableEq β] :
    incM F (Matrix.fromRows (1 : Matrix β β E) (1 : Matrix β β E)) = Matrix.fromRows (1 : Matrix β β (AE F E)) 1 := by
  simp [incM, Matrix.fromRows_map]

variable (F) in
theorem incM_nabla {β : Type} [DecidableEq β] :
    incM F (Matrix.fromRows (1 : Matrix β β E) (-1 : Matrix β β E)) = Matrix.fromRows (1 : Matrix β β (AE F E)) (-1) := by
  simp [incM, Matrix.fromRows_map, Matrix.map_neg _ (map_neg (inclR (F := F) (E := E) (AF F)))]

theorem incM_inj {m n : Type} {A B : Matrix m n E} (h : incM F A = incM F B) : A = B := by
  ext i j
  exact inclR_inj (congrFun (congrFun h i) j)

def up (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (p : UG σ (dbl JB)) : UG (cA σ) (dbl (incM F JB)) :=
  ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) p.1, by
    have hp : ((p.1 : Matrix _ _ E))ᵀ * dbl JB * (p.1 : Matrix _ _ E).map σ = dbl JB := p.2
    show (incM F (p.1 : Matrix _ _ E))ᵀ * dbl (incM F JB) * (incM F (p.1 : Matrix _ _ E)).map (cA σ) = dbl (incM F JB)
    rw [incM_map, ← incM_dbl, incM_transpose, ← incM_mul, ← incM_mul, hp]⟩

theorem up_mul (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (p q : UG σ (dbl JB)) :
    up σ JB (p * q) = up σ JB p * up σ JB q :=
  Subtype.ext (map_mul _ _ _)

theorem down (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (g : UG (cA σ) (dbl (incM F JB)))
    (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E)
    (hg : ((g : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) = incM F g₀) :
    ∃ g₁ : UG σ (dbl JB), ((g₁ : GL (Fin b ⊕ Fin b) E) : Matrix _ _ E) = g₀ ∧ g = up σ JB g₁ := by
  have hdet : IsUnit g₀.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hu : IsUnit (g.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)).det :=
      (Matrix.isUnit_iff_isUnit_det (g.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E))).mp (Units.isUnit _)
    have e : (incM F g₀).det = inclR (F := F) (AF F) g₀.det := (RingHom.map_det _ _).symm
    rw [hg, e, h0, map_zero, isUnit_zero_iff] at hu
    exact zero_ne_one (inclR_inj (F := F) (E := E) (by rw [map_zero, map_one]; exact hu))
  have hu : IsUnit g₀ := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hmem : hu.unit ∈ UG σ (dbl JB) := by
    show (hu.unit : Matrix _ _ E)ᵀ * dbl JB * (hu.unit : Matrix _ _ E).map σ = dbl JB
    rw [IsUnit.unit_spec]
    have h2 : ((g : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E))ᵀ * dbl (incM F JB) *
        ((g : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)).map (cA σ) = dbl (incM F JB) := g.2
    rw [hg, incM_map, ← incM_dbl, incM_transpose, ← incM_mul, ← incM_mul] at h2
    exact incM_inj h2
  refine ⟨⟨hu.unit, hmem⟩, IsUnit.unit_spec hu, Subtype.ext (Units.ext ?_)⟩
  rw [hg]
  exact (congrArg (incM F) (IsUnit.unit_spec hu)).symm

end GlobalTheory.ThetaRatGen

namespace GlobalTheory.ThetaRatGen

theorem gen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b : ℕ) (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ), (∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) → JB.det ≠ 0 → ∀ (g : UG (cA σ) (dbl (incM F JB))) (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((g : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F g₀ → ∃ (p q p' : UG (cA σ) (dbl (incM F JB))) (p₀ q₀ p₀' : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) (t s t' : GL (Fin b) (AE F E)), ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F p₀ ∧ ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F q₀ ∧ ((p' : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F p₀' ∧ ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (t : Matrix (Fin b) (Fin b) (AE F E)) ∧ ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) ∧ ((p' : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (t' : Matrix (Fin b) (Fin b) (AE F E)) ∧ g = p * q * p' := by
  intro F E _ _ _ _ _ σ hσ b JB ε hJ hdet g g₀ hg
  haveI : Invertible (2 : E) := invertibleOfNonzero two_ne_zero
  obtain ⟨g₁, -, rfl⟩ := down σ JB g g₀ hg
  set G : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E := (g₁.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) with hG
  set H : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E :=
    ((g₁.1⁻¹ : GL (Fin b ⊕ Fin b) E) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) with hH
  set Nt : Matrix (Fin b) (Fin b ⊕ Fin b) E := Matrix.fromCols 1 (-1) with hNt
  set N : Matrix (Fin b ⊕ Fin b) (Fin b) E := Matrix.fromRows 1 (-1) with hN
  set Dt : Matrix (Fin b) (Fin b ⊕ Fin b) E := Matrix.fromCols 1 1 with hDt
  set Δ : Matrix (Fin b ⊕ Fin b) (Fin b) E := Matrix.fromRows 1 1 with hΔ
  have hGH : G * H = 1 := by rw [hG, hH, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNN : Nt * N = (2 : E) • 1 := by
    rw [hNt, hN, Matrix.fromCols_mul_fromRows]
    simp [two_smul]
  have e2' : Δ * Dt + N * Nt = (2 : E) • 1 := GlobalTheory.BigCell.e2
  have hPQ : (Nt * G * N) * ((4 : E)⁻¹ • (Nt * H * N)) + (Nt * G * Δ) * ((4 : E)⁻¹ • (Dt * H * N)) = 1 := by
    calc _ = (4 : E)⁻¹ • (Nt * G * (Δ * Dt + N * Nt) * H * N) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, smul_add, Matrix.mul_assoc]
          abel
      _ = 1 := by
          rw [e2']
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
          rw [show Nt * G * H * N = Nt * N by rw [Matrix.mul_assoc Nt G H, hGH, Matrix.mul_one], hNN, smul_smul]
          norm_num
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.exists_corner_unit_of_right_inverse' (F := F) (1 : E) (mul_one 1) hyp1 _ _ _ _ hPQ
  obtain ⟨ρ, hρ0, hρ⟩ := exists_anti hσ
  have hJ' : (JB.map (σ : E →+* E))ᵀ = ((ε : ℤ) : E) • JB := by
    ext i j
    simp [hJ]
  obtain ⟨x, hxS, hx⟩ := GlobalTheory.T.exists_conj_skew_det_unit_of_avoidance' (F := F) (σ : E →+* E) (invol hσ) (fun t => σ.commutes t) 1 hyp1 ρ
    (isUnit_iff_ne_zero.mpr hρ0) hρ JB ε hJ' (isUnit_iff_ne_zero.mpr hdet) _ _ x₀ hx₀
  obtain ⟨p, hpΔ, hcorner⟩ := GlobalTheory.T.siegelUnipotent_antidiagonal_corner (R₀ := F) σ JB x hxS
  have hunit : IsUnit (Matrix.fromCols (1 : Matrix (Fin b) (Fin b) E) (-1 : Matrix (Fin b) (Fin b) E) *
      (((g₁ * p : UG σ (dbl JB)) : GL (Fin b ⊕ Fin b) E) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
      Matrix.fromRows (1 : Matrix (Fin b) (Fin b) E) (-1 : Matrix (Fin b) (Fin b) E)).det := by
    rw [Subgroup.coe_mul, Units.val_mul, hcorner]
    have hx' : IsUnit (Nt * G * N + Nt * G * Δ * x).det := by simpa using hx
    exact hx'
  obtain ⟨p₀, q₀, t, s, hp₀, hq₀, hpq⟩ := GlobalTheory.BigCell.bigCell_factor F E σ (Fin b) JB (g₁ * p) hunit
  have hg₁ : g₁ = p₀ * q₀ * p⁻¹ := eq_mul_inv_of_mul_eq hpq
  have hpinv : ((p⁻¹ : UG σ (dbl JB)).1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) = (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) := by
    have h1 : (p.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) =
        (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) := by
      exact hpΔ.trans (Matrix.mul_one _)
    calc _ = ((p⁻¹ : UG σ (dbl JB)).1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
          ((p.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
            (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E)) := by rw [h1]
      _ = diagCols (Fin b) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
            Matrix.one_mul]
  refine ⟨up σ JB p₀, up σ JB q₀, up σ JB p⁻¹, p₀.1, q₀.1, (p⁻¹).1,
    Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) t,
    Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) s, 1, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (incM F) hp₀
    rw [incM_mul, incM_mul, incM_diag] at h
    exact h
  · have h := congrArg (incM F) hq₀
    rw [incM_mul, incM_mul, incM_nabla] at h
    exact h
  · have h := congrArg (incM F) hpinv
    rw [incM_mul, diagCols, incM_diag] at h
    exact h.trans (Matrix.mul_one _).symm
  · rw [hg₁, up_mul, up_mul]

end GlobalTheory.ThetaRatGen
