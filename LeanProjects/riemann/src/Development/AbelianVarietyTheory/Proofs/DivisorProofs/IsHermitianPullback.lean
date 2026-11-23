import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMapGivesHomomorphism
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnProdOfForall
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AHExists

theorem dotProduct_pullback {g n : ℕ} (J : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (H : Matrix (Fin n) (Fin n) ℂ)
    (z w : Fin g → ℂ) :
    z ⬝ᵥ ((LinearMap.toMatrix' J).transpose * H * (LinearMap.toMatrix' J).map star).mulVec (star w) =
      J z ⬝ᵥ H.mulVec (star (J w)) := by
  have e : ((LinearMap.toMatrix' J).map star).mulVec (star w) = star (J w) := by
    rw [← LinearMap.toMatrix'_mulVec J w]
    generalize LinearMap.toMatrix' J = N
    funext a
    simp [Matrix.mulVec, dotProduct, star_sum, _root_.mul_comm]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    LinearMap.toMatrix'_mulVec]

theorem isHermitian_pullback {g n : ℕ} (N : Matrix (Fin n) (Fin g) ℂ) {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) : (N.transpose * H * N.map star).IsHermitian := by
  have e : N.transpose = (N.map star).conjTranspose := by
    ext a b
    simp
  rw [e]
  exact Matrix.isHermitian_conjTranspose_mul_mul _ hH

theorem exists_isAH : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (L : LB A.left) (u : HolUnif A L g), ∃ (M : LB A.left) (u' : HolUnif A M g) (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ), M.IsLB ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsAH H χ := by
  intro A _ g hA L u
  obtain ⟨Q, v, i, r, J, R, m, -, hi, -, hm, hJ, -, -, -, hRJ⟩ :=
    GlobalTheory.HolUnifHom.exists_linear_factor A g hA (GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u) L u
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v', Hm, χ', -, hAH, -, hv1, hv2, -⟩ := thetaUnifAV_all Q rig hrig
  obtain ⟨J', hJ', hJΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A Q.A hA Q.isAb L Q.L g Q.g u v'
    hv1 hv2 i hi
  have hinj : ∀ z, J' z = 0 → z = 0 := by
    intro z hz
    have h0 : J z = 0 := LatticeHom.eq_zero_of_forall_smul_mem v.Λ v.discrete fun t => by
      rw [← map_smul, ← v.ker, hJ, ← hJ', map_smul, hz, smul_zero, v'.ker]
      exact v'.Λ.zero_mem
    have h1 := hRJ z
    rw [h0, map_zero, ← Nat.cast_smul_eq_nsmul ℂ] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left (by exact_mod_cast (show m ≠ 0 by omega))
  obtain ⟨u₁, hex, hΛ₁, hfr⟩ := GlobalTheory.exists_holUnif_linComb A Q.A L Q.L g Q.g u v' PUnit (fun _ => i)
    (fun _ => J') (fun _ => 1) (fun _ z => hJ' z)
  have hmem : ∀ l : u₁.Λ, J' (l : Fin g → ℂ) ∈ v'.Λ := fun l => hJΛ _ (hΛ₁ ▸ l.2)
  refine ⟨_, u₁, (LinearMap.toMatrix' J').transpose * Hm * (LinearMap.toMatrix' J').map star,
    fun l => χ' ⟨J' l.1, hmem l⟩, LB.isLB_linComb Q.isLB _ _, hex, hΛ₁, isHermitian_pullback _ hAH.1,
    fun z hz => ?_, fun l => hAH.2.2.1 _, ?_⟩
  · rw [dotProduct_pullback]
    exact hAH.2.1 _ fun h => hz (hinj z h)
  intro l j z hz
  rw [hex] at hz
  have hz' : ⊤ ≤ (v'.ex (J' z)).left ⁻¹ᵁ Q.L.U (j PUnit.unit) := by
    rw [hJ' z]
    exact (CubeValues.le_preimage_wchart (u.ex z).left Q.L (fun _ => i.left) j).1 hz PUnit.unit
  have e1 : u₁.fr j z = v'.fr (j PUnit.unit) (J' z) := by simpa using hfr j z
  have e2 : u₁.fr j (z + l) = v'.fr (j PUnit.unit) (J' z + J' l) := by simpa using hfr j (z + l)
  rw [e1, e2, dotProduct_pullback, dotProduct_pullback]
  exact hAH.2.2.2 ⟨J' l.1, hmem l⟩ (j PUnit.unit) (J' z) hz'

end GlobalTheory.AHExists
