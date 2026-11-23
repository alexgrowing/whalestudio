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
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.CanThLine

section Law

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CanTh
open scoped Real

variable {g : ℕ}

theorem gaussian_mul_factor {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (a c : Fin g → ℝ) (m n : Fin g → ℤ) {l : Fin g → ℂ}
    (hl : l = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) (ζ : Fin g → ℂ) :
    cexp (-(π / 2 * ((ζ + l) ⬝ᵥ imInv τ *ᵥ (ζ + l)))) *
        (canMult a c m n *
          cexp (π * hermForm (imInv τ) ζ l + π / 2 * hermForm (imInv τ) l l)) =
      eC (((1 : ℕ) : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec m - ofRealVec c ⬝ᵥ ofIntVec n)) *
        eC (-((1 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ ζ)) *
        cexp (-(π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ))) := by
  have hl' : l = (fun i => (((m i : ℝ)) : ℂ)) + τ *ᵥ fun i => (((n i : ℝ)) : ℂ) := by
    simpa using hl
  have h1 := dot_imInv_eq_hermForm_add hp (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) ζ
  have h2 := dot_imInv_eq_hermForm_add hp (fun i => (n i : ℝ)) (fun i => (m i : ℝ)) l
  rw [← hl'] at h1 h2
  have h3 := dot_mulVec_symm (isSymm_imInv hs) ζ l
  have e0 : (fun i => (((n i : ℝ)) : ℂ)) = ofIntVec n := by
    funext i; simp [ofIntVec]
  have h5 : (l ⬝ᵥ ofIntVec n) = ((m ⬝ᵥ n : ℤ) : ℂ) + ofIntVec n ⬝ᵥ τ *ᵥ ofIntVec n := by
    rw [hl, add_dotProduct, dotProduct_comm (τ *ᵥ _)]
    congr 1
    simp [dotProduct, ofIntVec]
  have e1 : ((a ⬝ᵥ (fun i => (m i : ℝ)) : ℝ) : ℂ) = ofRealVec a ⬝ᵥ ofIntVec m := by
    simp [dotProduct, ofRealVec, ofIntVec]
  have e2 : ((c ⬝ᵥ (fun i => (n i : ℝ)) : ℝ) : ℂ) = ofRealVec c ⬝ᵥ ofIntVec n := by
    simp [dotProduct, ofRealVec, ofIntVec]
  rw [e0] at h1 h2
  rw [canMult, e1, e2]
  simp only [eC, ← Complex.exp_add]
  congr 1
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, h3, h1, h2, h5,
    dotProduct_comm (ofIntVec n) ζ]
  push_cast
  ring

end Law

section Main

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CanTh
open scoped Real

variable {g : ℕ}

theorem gaussian_mul_mem_thetaLevelChar {τ h Hm : Matrix (Fin g) (Fin g) ℂ} {a c : Fin g → ℝ}
    {θ : (Fin g → ℂ) → ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (hh : IsUnit h.det)
    (hH : ∀ z w, hermForm Hm z w = hermForm (imInv τ) (h *ᵥ z) (h *ᵥ w))
    (hθ : Differentiable ℂ θ)
    (hlaw : ∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ),
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = canMult a c m n *
        cexp (π * hermForm Hm z lam + π / 2 * hermForm Hm lam lam) * θ z) :
    (fun ζ => cexp (-(π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ))) * θ (h⁻¹ *ᵥ ζ)) ∈
      GlobalTheory.thetaLevelChar a c 1 τ := by
  have hhi : h * h⁻¹ = 1 := mul_nonsing_inv _ hh
  have hback : ∀ v : Fin g → ℂ, h *ᵥ (h⁻¹ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, hhi, one_mulVec]
  have hd : Differentiable ℂ (fun ζ : Fin g → ℂ => h⁻¹ *ᵥ ζ) :=
    differentiable_pi.2 fun i => by
      simp only [mulVec, dotProduct]
      fun_prop
  refine GlobalTheory.mem_thetaLevelChar.2 ⟨?_, fun n n' z => ?_⟩
  · refine Differentiable.mul ?_ (hθ.comp hd)
    simp only [dotProduct, mulVec]
    fun_prop
  · set l : Fin g → ℂ := (fun i => (n' i : ℂ)) + τ *ᵥ fun i => (n i : ℂ) with hl
    have e : z + τ *ᵥ ofIntVec n + ofIntVec n' = z + l := by
      rw [hl, add_assoc, add_comm (τ *ᵥ _)]
      rfl
    have hL := hlaw n' n (h⁻¹ *ᵥ l) (hback l) (h⁻¹ *ᵥ z)
    rw [hH, hH, hback, hback] at hL
    have hG := gaussian_mul_factor hs hp a c n' n hl z
    simp only [e]
    rw [show h⁻¹ *ᵥ (z + l) = h⁻¹ *ᵥ z + h⁻¹ *ᵥ l from mulVec_add _ _ _, hL]
    linear_combination θ (h⁻¹ *ᵥ z) * hG

theorem eq_const_mul_canTh {τ h Hm : Matrix (Fin g) (Fin g) ℂ} {a c : Fin g → ℝ}
    {θ : (Fin g → ℂ) → ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (hh : IsUnit h.det)
    (hH : ∀ z w, hermForm Hm z w = hermForm (imInv τ) (h *ᵥ z) (h *ᵥ w))
    (hθ : Differentiable ℂ θ)
    (hlaw : ∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ),
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = canMult a c m n *
        cexp (π * hermForm Hm z lam + π / 2 * hermForm Hm lam lam) * θ z) :
    ∃ κ : ℂ, ∀ z, θ z = κ * canTh τ a c (h *ᵥ z) := by
  have hmem := gaussian_mul_mem_thetaLevelChar hs hp hh hH hθ hlaw
  rw [GlobalTheory.thetaLevelChar_one (a := a) (b := c) (τ := τ) ⟨hs, hp⟩, Submodule.mem_span_singleton] at hmem
  obtain ⟨κ, hκ⟩ := hmem
  refine ⟨κ, fun z => ?_⟩
  have hback : h⁻¹ *ᵥ (h *ᵥ z) = z := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hh, one_mulVec]
  have hz := congrFun hκ (h *ᵥ z)
  simp only [Pi.smul_apply, smul_eq_mul] at hz
  rw [hback] at hz
  rw [canTh, thetaChar_eq_theta, mul_left_comm, hz, ← _root_.mul_assoc, ← Complex.exp_add]
  simp

end Main

theorem level_one_line : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (θ : (Fin g → ℂ) → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    Differentiable ℂ θ →
    (∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ), h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = GlobalTheory.CanTh.canMult a c m n *
        Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) * θ z) →
    ∃ κ : ℂ, ∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z) := by
  intro g τ h Hm a c θ hs hp hh hH hθ hlaw
  exact eq_const_mul_canTh hs hp hh hH hθ hlaw

end GlobalTheory.CompanionTheory.CanThLine
