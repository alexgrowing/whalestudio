import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatMemSpanOfRealMemSpanFinStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordsEqPairingsRationalSymplecticBasisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianContainingIsotropicRatStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatAlternatingOrthogonalOrthogonalLeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinearIndependentRatBasisAdaptedSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDotProductMulVecEqOfLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemPairingEqSingleNonradicalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsotropicDualOfSkewMatrixStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymplecticNormalForm

theorem key_apply {a b r : ℕ} (A : Matrix (Fin a) (Fin r) ℚ) (Mq : Matrix (Fin r) (Fin r) ℚ)
    (B : Matrix (Fin b) (Fin r) ℚ) (i : Fin a) (j : Fin b) :
    (A * Mq * Bᵀ) i j = A i ⬝ᵥ Mq *ᵥ B j := by
  rw [Matrix.mul_apply, dotProduct_mulVec]
  simp only [Matrix.transpose_apply, dotProduct, vecMul, Matrix.mul_apply]

theorem skew_swap {r : ℕ} (Mq : Matrix (Fin r) (Fin r) ℚ) (h : Mqᵀ = -Mq) (x y : Fin r → ℚ) :
    x ⬝ᵥ Mq *ᵥ y = -(y ⬝ᵥ Mq *ᵥ x) := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, h, dotProduct_comm, Matrix.neg_mulVec, dotProduct_neg]

theorem exists_adapted_rational_symplectic_basis : ∀ (g r r₀ : ℕ) (M : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ), r = 2 * g → Mᵀ = -M → M.det ≠ 0 → LinearIndependent ℚ (fun i j => (c i j : ℚ)) → (∀ v : Fin r → ℝ, (∀ i, v ⬝ᵥ (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (c i j : ℝ)) = 0) → v ∈ Submodule.span ℝ (Set.range fun i j => (c i j : ℝ))) → ∃ (rk : ℕ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (β : Matrix (Fin g) (Fin r₀) ℚ) (gm dl : Matrix (Fin r₀) (Fin g) ℚ), rk ≤ g ∧ (α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 0 ∧ φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 ∧ φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 ∧ (∀ i : Fin g, i.val < rk → ∀ m, ((α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (c.map (Int.cast : ℤ → ℚ))ᵀ) i m = 0) ∧ (∀ j : Fin g, rk ≤ j.val → ∀ m, φ j m = (β * c.map (Int.cast : ℤ → ℚ)) j m) ∧ (∀ m (j : Fin g), j.val < rk → dl m j = 0) ∧ c.map (Int.cast : ℤ → ℚ) = gm * (α * c.map (Int.cast : ℤ → ℚ)) + dl * φ := by
  intro g r r₀ M c hr hskew hdet hind hreal
  set Mq : Matrix (Fin r) (Fin r) ℚ := M.map (Int.cast : ℤ → ℚ) with hMq
  set cq : Matrix (Fin r₀) (Fin r) ℚ := c.map (Int.cast : ℤ → ℚ) with hcq
  have hskq : Mqᵀ = -Mq := by
    ext i j
    have := congrArg (fun A => A i j) hskew
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    simp only [hMq, Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply]
    exact_mod_cast this
  have hdq : Mq.det ≠ 0 := by
    rw [hMq, ← Int.cast_det]
    exact_mod_cast hdet
  set V : Submodule ℚ (Fin r → ℚ) := Submodule.span ℚ (Set.range fun i j => (c i j : ℚ)) with hVdef
  have hcqV : ∀ m, cq m ∈ V := fun m => Submodule.subset_span ⟨m, rfl⟩
  have hV : ∀ v : Fin r → ℚ, (∀ w ∈ V, v ⬝ᵥ Mq *ᵥ w = 0) → v ∈ V := by
    intro v hv
    apply GlobalTheory.T.rat_mem_span_of_real_mem_span_fin r₀ r (fun i j => (c i j : ℚ)) v
    have hfun : (fun i j => (((c i j : ℚ)) : ℝ)) = fun i j => (c i j : ℝ) := by
      funext i j; simp
    rw [hfun]
    apply hreal
    intro i
    have h := congrArg (fun q : ℚ => (q : ℝ)) (hv _ (hcqV i))
    simp only [dotProduct, mulVec, hMq, hcq, Matrix.map_apply] at h ⊢
    push_cast at h ⊢
    exact h
  let I : Submodule ℚ (Fin r → ℚ) :=
    { carrier := {y | ∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0}
      add_mem' := by
        intro a b ha hb w hw
        simp only [Set.mem_setOf_eq] at ha hb
        rw [add_dotProduct, ha w hw, hb w hw, add_zero]
      zero_mem' := by intro w _; simp
      smul_mem' := by
        intro t a ha w hw
        simp only [Set.mem_setOf_eq] at ha
        rw [smul_dotProduct, ha w hw, smul_zero] }
  have hmemI : ∀ y, y ∈ I ↔ ∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0 := fun y => Iff.rfl
  have hIiso : ∀ x ∈ I, ∀ y ∈ I, x ⬝ᵥ Mq *ᵥ y = 0 :=
    fun x hx y hy => (hmemI x).mp hx y (hV y ((hmemI y).mp hy))
  obtain ⟨L, hIL, hLiso, hLdim⟩ := GlobalTheory.T.exists_lagrangian_containing_isotropic_rat' g r Mq I hr hskq hdq hIiso
  have hLV : ∀ x ∈ L, x ∈ V := fun x hx =>
    GlobalTheory.T.mem_of_orthogonal_orthogonal_of_skew_det_ne_zero r Mq V hskq hdq x (fun y hy => hLiso x hx y (hIL ((hmemI y).mpr hy)))
  obtain ⟨rk, hrk, ε, hεind, hεL, hεI, hIspan⟩ := GlobalTheory.T.exists_linearIndependent_rat_basis_adapted_subspace g r I L hIL hLdim
  have hεiso : ∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0 := fun i j => hLiso _ (hεL i) _ (hεL j)
  have hεV : ∀ i, ε i ∈ V := fun i => hLV _ (hεL i)
  have hεperp : ∀ i : Fin g, i.val < rk → ∀ w ∈ V, ε i ⬝ᵥ Mq *ᵥ w = 0 :=
    fun i hi => (hmemI _).mp (hεI i hi)
  have hψ : ∀ j : Fin g, ∃ x : Fin r → ℚ, (rk ≤ j.val → x ∈ V) ∧
      ∀ i, x ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0 := by
    intro j
    by_cases hj : rk ≤ j.val
    · obtain ⟨x, hxV, hx⟩ := GlobalTheory.T.exists_mem_pairing_eq_single_nonradical r g rk Mq V ε hskq hεind hεperp
        (fun y hy => hIspan y ((hmemI y).mpr hy)) j hj
      exact ⟨x, fun _ => hxV, hx⟩
    · obtain ⟨x, hx⟩ := GlobalTheory.T.exists_dotProduct_mulVec_eq_of_linearIndependent' r g Mq ε hdq hεind (fun i => if i = j then 1 else 0)
      exact ⟨x, fun h => absurd h hj, hx⟩
  choose ψ hψV hψε using hψ
  obtain ⟨φ, hφiso, hφε, hφψ⟩ := GlobalTheory.T.exists_isotropic_dual_of_skew_matrix' r g Mq ε ψ hskq hεiso (fun i j => hψε j i)
  have hspanV : Submodule.span ℚ (Set.range ε) ≤ V :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hεV i)
  have hφV : ∀ j : Fin g, rk ≤ j.val → φ j ∈ V := fun j hj => by
    have := V.add_mem (hspanV (hφψ j)) (hψV j hj)
    simpa using this
  have hα : ∀ i, ∃ a : Fin r₀ → ℚ, ∑ m, a m • (fun k => (c m k : ℚ)) = ε i :=
    fun i => (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hεV i)
  choose α hα using hα
  have hβ : ∀ j : Fin g, ∃ b : Fin r₀ → ℚ, rk ≤ j.val → ∑ m, b m • (fun k => (c m k : ℚ)) = φ j := by
    intro j
    by_cases hj : rk ≤ j.val
    · obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hφV j hj)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose β hβ using hβ
  let αm : Matrix (Fin g) (Fin r₀) ℚ := α
  let εm : Matrix (Fin g) (Fin r) ℚ := ε
  let φm : Matrix (Fin g) (Fin r) ℚ := φ
  let βm : Matrix (Fin g) (Fin r₀) ℚ := β
  have hαc : αm * cq = εm := by
    ext i k
    have h1 := congrFun (hα i) k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    show (αm * cq) i k = ε i k
    rw [← h1, Matrix.mul_apply]
    rfl
  refine ⟨rk, αm, φm, βm,
    Matrix.of fun m i => -(cq m ⬝ᵥ Mq *ᵥ φ i), Matrix.of fun m j => cq m ⬝ᵥ Mq *ᵥ ε j,
    hrk, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hαc]; ext i j; rw [key_apply]; exact hεiso i j
  · ext i j; rw [key_apply]; exact hφiso i j
  · rw [hαc]; ext i j; rw [key_apply, Matrix.one_apply]
    rw [hφε j i]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  · intro i hi m
    rw [hαc, key_apply]
    exact hεperp i hi _ (hcqV m)
  · intro j hj m
    have h1 := congrFun (hβ j hj) m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    show φ j m = (βm * cq) j m
    rw [← h1, Matrix.mul_apply]
    rfl
  · intro m j hj
    simp only [Matrix.of_apply]
    rw [skew_swap Mq hskq, hεperp j hj _ (hcqV m), neg_zero]
  · rw [hαc]
    ext m k
    have h := congrFun (GlobalTheory.T.coords_eq_pairings_rational_symplectic_basis g r Mq ε φ hr hskq hdq hεiso hφiso hφε (cq m)) k
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    exact h

end GlobalTheory.SymplecticNormalForm
