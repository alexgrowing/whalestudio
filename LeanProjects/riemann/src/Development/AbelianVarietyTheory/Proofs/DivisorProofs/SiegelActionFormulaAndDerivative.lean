import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryInvariantHermitianFormSymmEqSmulTrace
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SiegelAffine

theorem symPart_add' {g : ℕ} (Z W : Matrix (Fin g) (Fin g) ℂ) :
    symPart (Z + W) = symPart Z + symPart W := by
  apply Subtype.ext; funext i j
  simp only [symPart, Submodule.coe_add, Pi.add_apply, Matrix.add_apply]; ring

theorem symPart_smul' {g : ℕ} (c : ℂ) (Z : Matrix (Fin g) (Fin g) ℂ) :
    symPart (c • Z) = c • symPart Z := by
  apply Subtype.ext; funext i j
  simp only [symPart, Submodule.coe_smul, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]; ring

def congL {g : ℕ} (B : Matrix (Fin g) (Fin g) ℂ) : symMat g →L[ℂ] symMat g :=
  LinearMap.toContinuousLinearMap
    { toFun := fun s => symPart (B * tauU s * Bᵀ)
      map_add' := fun s t => by
        have e : tauU (s + t) = tauU s + tauU t := rfl
        rw [e, Matrix.mul_add, Matrix.add_mul, symPart_add']
      map_smul' := fun c s => by
        have e : tauU (c • s) = c • tauU s := rfl
        rw [e, Matrix.mul_smul, Matrix.smul_mul, symPart_smul']; rfl }

theorem block_mem {g : ℕ} (A X : Matrix (Fin g) (Fin g) ℝ) (hA : IsUnit A) (hX : X.IsSymm) :
    Matrix.fromBlocks A (X * (A⁻¹)ᵀ) 0 (A⁻¹)ᵀ ∈ Matrix.symplecticGroup (Fin g) ℝ := by
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hd
  have h2 : (A⁻¹)ᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have h3 : A * (A⁻¹ * X) = X := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hX' : Xᵀ = X := hX
  rw [SymplecticGroup.mem_iff, Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc, h1, h2, h3, hX']

theorem exists_affine : ∀ (g : ℕ) (A X : Matrix (Fin g) (Fin g) ℝ), IsUnit A → X.IsSymm → ∃ γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g, ∀ s v : symMat g, actB γ s = symPart (A.map (fun t : ℝ => (t : ℂ)) * tauU s * (A.map (fun t : ℝ => (t : ℂ)))ᵀ + X.map (fun t : ℝ => (t : ℂ))) ∧ fderiv ℂ (actB γ) s v = symPart (A.map (fun t : ℝ => (t : ℂ)) * tauU v * (A.map (fun t : ℝ => (t : ℂ)))ᵀ) := by
  intro g A X hA hX
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hd
  have h2 : (A⁻¹)ᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have hm : ∀ P Q : Matrix (Fin g) (Fin g) ℝ, (P * Q).map (fun t : ℝ => (t : ℂ)) =
      P.map (fun t : ℝ => (t : ℂ)) * Q.map (fun t : ℝ => (t : ℂ)) := fun P Q =>
    Matrix.map_mul (f := Complex.ofRealHom)
  have h3 : ((A⁻¹)ᵀ).map (fun t : ℝ => (t : ℂ)) * (A.map (fun t : ℝ => (t : ℂ)))ᵀ = 1 := by
    rw [← Matrix.transpose_map, ← hm, h2]
    exact Matrix.map_one _ (by simp) (by simp)
  let γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g := ⟨_, block_mem A X hA hX⟩
  have hγ : γ.mat = Matrix.fromBlocks A (X * (A⁻¹)ᵀ) 0 (A⁻¹)ᵀ := rfl
  have hmo : ∀ τ : Matrix (Fin g) (Fin g) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.moeb γ τ =
      A.map (fun t : ℝ => (t : ℂ)) * τ * (A.map (fun t : ℝ => (t : ℂ)))ᵀ +
        X.map (fun t : ℝ => (t : ℂ)) := by
    intro τ
    have hden : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.den γ τ = ((A⁻¹)ᵀ).map (fun t : ℝ => (t : ℂ)) := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.den, hγ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂,
        Matrix.map_zero _ (by simp), Matrix.zero_mul, zero_add]
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.moeb, hden, Matrix.inv_eq_right_inv h3, hγ, Matrix.toBlocks_fromBlocks₁₁,
      Matrix.toBlocks_fromBlocks₁₂, Matrix.add_mul, hm, Matrix.mul_assoc (X.map _), h3,
      Matrix.mul_one]
  refine ⟨γ, fun s v => ⟨by rw [actB, hmo], ?_⟩⟩
  have he : actB γ = fun s => congL (A.map (fun t : ℝ => (t : ℂ))) s +
      symPart (X.map (fun t : ℝ => (t : ℂ))) := by
    funext s
    rw [actB, hmo, symPart_add']; rfl
  rw [he, ((congL (A.map (fun t : ℝ => (t : ℂ)))).hasFDerivAt.add_const _).fderiv]
  rfl

end GlobalTheory.SiegelAffine
