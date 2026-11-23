import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblySympl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.NformRed

open scoped Matrix

variable {g : ℕ}

theorem hermForm_sum_left {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ) (a : κ → ℤ)
    (x : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i, a i • x i) w = ∑ i, (a i : ℂ) * hermForm Hm (x i) w := by
  simp only [hermForm, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_dotProduct, zsmul_eq_mul]

theorem hermForm_sum_right {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ) (b : κ → ℤ)
    (y : κ → Fin g → ℂ) (z : Fin g → ℂ) :
    hermForm Hm z (∑ j, b j • y j) = ∑ j, (b j : ℂ) * hermForm Hm z (y j) := by
  have hs : star (∑ j, b j • y j) = ∑ j, b j • star (y j) := by
    simp [star_sum, star_smul]
  simp only [hermForm]
  rw [hs, Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, zsmul_eq_mul]

theorem hermForm_sum_sum {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : κ → ℤ)
    (x : κ → Fin g → ℂ) :
    hermForm Hm (∑ i, a i • x i) (∑ j, b j • x j) =
      ∑ i, ∑ j, (a i : ℂ) * (b j : ℂ) * hermForm Hm (x i) (x j) := by
  rw [hermForm_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hermForm_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem re_int_mul (m n : ℤ) (c : ℂ) :
    ((m : ℂ) * (n : ℂ) * c).re = (m : ℝ) * (n : ℝ) * c.re := by
  simp [Complex.mul_re]

theorem im_int_mul (m n : ℤ) (c : ℂ) :
    ((m : ℂ) * (n : ℂ) * c).im = (m : ℝ) * (n : ℝ) * c.im := by
  simp [Complex.mul_im]

theorem congr_apply {κ : Type*} [Fintype κ] (P : Matrix κ κ ℤ) (M : Matrix κ κ ℝ) (α δ : κ) :
    (P.map (Int.cast : ℤ → ℝ) * M * (P.map (Int.cast : ℤ → ℝ))ᵀ) α δ =
      ∑ β, ∑ ε, (P α β : ℝ) * (P δ ε : ℝ) * M β ε := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun ε _ => ?_
  ring

theorem J_map_int : (Matrix.J (Fin g) ℤ).map (Int.cast : ℤ → ℝ) = Matrix.J (Fin g) ℝ :=
  Matrix.map_J (Fin g) (Int.castRingHom ℝ)

theorem cast_symplectic {P : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hP : P ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    P.map (Int.cast : ℤ → ℝ) * Matrix.J (Fin g) ℝ * (P.map (Int.cast : ℤ → ℝ))ᵀ =
      Matrix.J (Fin g) ℝ := by
  have h := SymplecticGroup.mem_iff.1 hP
  have h2 := congrArg (fun M => M.map (Int.castRingHom ℝ)) h
  simp only [Matrix.map_mul] at h2
  have e : (Int.castRingHom ℝ : ℤ → ℝ) = (Int.cast : ℤ → ℝ) := rfl
  rw [e, J_map_int, Matrix.transpose_map] at h2
  exact h2

theorem left_inv_transpose {P : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hP : P ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    (-(Matrix.J (Fin g) ℤ * P * Matrix.J (Fin g) ℤ)) * Pᵀ = 1 := by
  have h := SymplecticGroup.mem_iff.1 hP
  have : Matrix.J (Fin g) ℤ * P * Matrix.J (Fin g) ℤ * Pᵀ =
      Matrix.J (Fin g) ℤ * (P * Matrix.J (Fin g) ℤ * Pᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [Matrix.neg_mul, this, h, Matrix.J_squared, neg_neg]

noncomputable def twist {κ M : Type*} [Fintype κ] [DecidableEq κ] [AddCommGroup M]
    (b : Module.Basis κ ℤ M) (P Q : Matrix κ κ ℤ) (h : Q * Pᵀ = 1) : Module.Basis κ ℤ M :=
  b.map (b.equivFun.trans ((Matrix.toLinearEquiv' Pᵀ ⟨Q, h, mul_eq_one_comm.1 h⟩).trans
    b.equivFun.symm))

theorem twist_apply {κ M : Type*} [Fintype κ] [DecidableEq κ] [AddCommGroup M]
    (b : Module.Basis κ ℤ M) (P Q : Matrix κ κ ℤ) (h : Q * Pᵀ = 1) (α : κ) :
    twist b P Q h α = ∑ β, P α β • b β := by
  have h1 : b.equivFun (b α) = Pi.single α 1 := by
    ext j
    simp [Module.Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  simp only [twist, Module.Basis.map_apply, LinearEquiv.trans_apply, h1,
    Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun β _ => ?_
  change (Pᵀ *ᵥ Pi.single α 1) β • b β = _
  rw [Matrix.mulVec_single_one]
  rfl

theorem coe_sum_smul {n : ℕ} {κ : Type*} [Fintype κ] (Λ : Submodule ℤ (Fin n → ℂ)) (v : κ → ℤ)
    (x : κ → Λ) : ((∑ α, v α • x α : Λ) : Fin n → ℂ) = ∑ α, v α • (x α : Fin n → ℂ) := by
  simp [Submodule.coe_sum]

theorem symplectic_reduction_basis :
    ∀ (g : ℕ) [NeZero g] (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ α β, (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β) →
    (Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re) ∈ Matrix.symplecticGroup (Fin g) ℝ →
    (Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re).PosDef →
    ∃ (bs' : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (ρ : ℝ),
      0 < ρ ∧ ρ ^ 2 ≤ 2 * g ∧
      (∀ α β, (hermForm Hm (bs' α : Fin g → ℂ) (bs' β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β) ∧
      (hermForm Hm (bs' (Sum.inl 0) : Fin g → ℂ) (bs' (Sum.inl 0) : Fin g → ℂ)).re = ρ ^ 2 ∧
      (∀ l : Λ, l ≠ 0 → ρ ^ 2 ≤ (hermForm Hm (l : Fin g → ℂ) (l : Fin g → ℂ)).re) ∧
      (Matrix.of fun i j : Fin g => (hermForm Hm (bs' (Sum.inl i) : Fin g → ℂ) (bs' (Sum.inl j) : Fin g → ℂ)).re).det ≤
        ρ ^ 2 * (2 * g) ^ (g - 1) := by
  intro g _ Λ Hm bs hHm hpos him hsymp hposdef
  set G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
    Matrix.of fun α β => (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).re with hG
  obtain ⟨ρsq, hleast, hle, P, hP, hfirst, hdet⟩ := SymplecticReduction.full g G hsymp hposdef
  have hqf : ∀ v : Fin g ⊕ Fin g → ℤ, qf G (intVec v) =
      (hermForm Hm (∑ α, v α • (bs α : Fin g → ℂ)) (∑ α, v α • (bs α : Fin g → ℂ))).re := by
    intro v
    rw [hermForm_sum_sum, Complex.re_sum]
    simp only [Complex.re_sum, re_int_mul, qf, intVec, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hG, Matrix.of_apply]
    ring
  have hne : ∀ v : Fin g ⊕ Fin g → ℤ, v ≠ 0 → ∑ α, v α • (bs α : Fin g → ℂ) ≠ 0 := by
    intro v hv h0
    apply hv
    have h1 : (∑ α, v α • bs α : Λ) = 0 := by
      apply Subtype.ext
      rw [coe_sum_smul]
      exact h0
    funext α
    exact Fintype.linearIndependent_iff.1 bs.linearIndependent v h1 α
  have hρpos : 0 < ρsq := by
    obtain ⟨v, hv, hval⟩ := hleast.1
    rw [hval, hqf]
    exact hpos _ (hne v hv)
  have hb' : ∀ α, ((twist bs P _ (left_inv_transpose hP) α : Λ) : Fin g → ℂ) =
      ∑ β, P α β • (bs β : Fin g → ℂ) := by
    intro α
    rw [twist_apply, coe_sum_smul]
  have hre : ∀ α δ, (hermForm Hm ((twist bs P _ (left_inv_transpose hP) α : Λ) : Fin g → ℂ)
      ((twist bs P _ (left_inv_transpose hP) δ : Λ) : Fin g → ℂ)).re =
      (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ) α δ := by
    intro α δ
    rw [hb', hb', hermForm_sum_sum, congr_apply]
    simp only [Complex.re_sum, re_int_mul, hG, Matrix.of_apply]
  have him' : ∀ α δ, (hermForm Hm ((twist bs P _ (left_inv_transpose hP) α : Λ) : Fin g → ℂ)
      ((twist bs P _ (left_inv_transpose hP) δ : Λ) : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α δ := by
    intro α δ
    rw [hb', hb', hermForm_sum_sum, ← cast_symplectic hP, congr_apply]
    simp only [Complex.im_sum, im_int_mul, him]
  refine ⟨twist bs P _ (left_inv_transpose hP), Real.sqrt ρsq, Real.sqrt_pos.2 hρpos, ?_, him', ?_,
    ?_, ?_⟩
  · rw [Real.sq_sqrt hρpos.le]
    exact hle
  · rw [Real.sq_sqrt hρpos.le, hre]
    exact hfirst
  · intro l hl
    rw [Real.sq_sqrt hρpos.le]
    have hv : (fun α => bs.repr l α) ≠ 0 := by
      intro h0
      apply hl
      have : bs.repr l = 0 := by
        ext α
        exact congrFun h0 α
      simpa using this
    have hsum : (l : Fin g → ℂ) = ∑ α, bs.repr l α • (bs α : Fin g → ℂ) := by
      rw [← coe_sum_smul, bs.sum_repr]
    rw [hsum, ← hqf (fun α => bs.repr l α)]
    exact hleast.2 ⟨_, hv, rfl⟩
  · rw [Real.sq_sqrt hρpos.le]
    have : (Matrix.of fun i j : Fin g =>
        (hermForm Hm ((twist bs P _ (left_inv_transpose hP) (Sum.inl i) : Λ) : Fin g → ℂ)
          ((twist bs P _ (left_inv_transpose hP) (Sum.inl j) : Λ) : Fin g → ℂ)).re) =
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ).toBlocks₁₁ := by
      ext i j
      simp only [Matrix.of_apply, hre, Matrix.toBlocks₁₁]
    rw [this]
    exact hdet

end GlobalTheory.CompanionTheory.Ar.NformRed
