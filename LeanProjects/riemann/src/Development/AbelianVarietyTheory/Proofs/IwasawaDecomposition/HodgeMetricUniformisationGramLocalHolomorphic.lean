import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentEqOfSameModulusPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFlagDomainSectionFlatCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLieEigenspaceFrameAtUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameChangeAlongAnalyticLiftStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix

namespace GlobalTheory.HodgeUnifFrame

theorem transpose_hermitian_gram_submatrix_bijection {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : n → m)
    (he : Function.Bijective e) (K G : Matrix m m ℂ) (W P : Matrix n n ℂ) (c : ℂ)
    (hG : G.submatrix e e = c • (Wᴴ * P * W)) :
    ((Kᴴ * G * K)ᵀ).submatrix e e = c • ((W * K.submatrix e e)ᵀ * Pᵀ * ((W * K.submatrix e e)ᵀ)ᴴ) := by
  have h1 : (Kᴴ * G * K).submatrix e e = (K.submatrix e e)ᴴ * G.submatrix e e * K.submatrix e e := by
    rw [Matrix.submatrix_mul _ _ _ e _ he, Matrix.submatrix_mul _ _ _ e _ he, Matrix.conjTranspose_submatrix]
  have h2 : ((Kᴴ * G * K)ᵀ).submatrix e e = ((Kᴴ * G * K).submatrix e e)ᵀ := by ext; rfl
  rw [h2, h1, hG]
  have h3 : ((W * K.submatrix e e)ᵀ)ᴴ = ((W * K.submatrix e e)ᴴ)ᵀ := by ext; rfl
  rw [h3]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

theorem lieGram_unif_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), ∀ (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U), ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ τ : GlobalTheory.AllWt.Psi H, ∃ c : ℝ, 0 < c ∧ ∃ g : ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin Dw.p) (Fin Dw.p) ℂ, (∀ i j, AnalyticAt ℂ (fun w => g w i j) v) ∧ IsUnit (g v).det ∧ ∀ᶠ w in nhds v, (lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) τ.1).submatrix (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) = (c : ℂ) • (g w * ((hP (unflat (GlobalTheory.UnifDens.flatL h w) (GlobalTheory.HodgeGenUnf.letter hσ hU k τ)))⁻¹)ᵀ * (g w)ᴴ) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA τ
  obtain ⟨hoi, -, hT⟩ := hL
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  obtain ⟨s, hsa, hWa, hsev⟩ := GlobalTheory.T.exists_analytic_flagDomain_section_flatCoordinates E Dw.p Dw.q X.dim (U.X k) hp h v hv
  obtain ⟨K, hKa, hKu, hKev⟩ := GlobalTheory.T.exists_holomorphic_frameChange_along_analyticLift E H Dw l Xo c O β Y T F e σ U hσ hU k X j f₀ Eb A₀ hj hoi hT ψ hψ h v hv A hA s hsa hsev
  have hex := GlobalTheory.T.eventually_lieEigenspaceFrameAt_uniformisation E H Dw l Xo c O β Y T F e σ U hσ hU k X j f₀ Eb A₀ hj hoi hT ψ hψ h v hv A hA
  set τ' := GlobalTheory.HodgeGenUnf.letter hσ hU k τ with hτ'
  set ec : Fin Dw.p → Fin (Dw.mult τ.1) := Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm with hec
  have he : Function.Bijective ec := (finCongr (GlobalTheory.HodgeGenUnf.mult_psi τ).symm).bijective
  refine ⟨2 * Real.pi, Real.two_pi_pos,
    fun w => (coW (U.X k) (Nat.le_add_right Dw.p Dw.q) (s w) τ' * (K w τ.1).submatrix ec ec)ᵀ, ?_, ?_, ?_⟩
  · intro a b
    simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.submatrix_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ => (hWa τ' b i).mul (hKa τ.1 (ec i) (ec a))
  · obtain ⟨hs0, -⟩ := hsev.self_of_nhds
    rw [Matrix.det_transpose, Matrix.det_mul]
    refine (isUnit_coW (U.X k) _ hp hs0 τ').mul ?_
    have : (K v τ.1).submatrix ec ec = (K v τ.1).submatrix (finCongr (GlobalTheory.HodgeGenUnf.mult_psi τ).symm)
      (finCongr (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) := rfl
    rw [this, Matrix.det_submatrix_equiv_self]
    exact hKu τ.1
  · filter_upwards [hsev, hKev, hex] with w ⟨hs, hflat⟩ hKw ⟨g0, hg0⟩
    have hexw : ∃ g, FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g := ⟨g0, hg0⟩
    rw [lieGram, dif_pos hexw]
    show (((hodgeMet T.Z U).gram _ hexw.choose τ.1)ᵀ).submatrix ec ec = _
    rw [hKw hs _ hexw.choose_spec (hodgeMet T.Z U) τ.1]
    have hG := GlobalTheory.HodgeGenUnf.hodgeMet_gram_frame T.Z hσ hU k ⟨s w, hs⟩ τ τ' rfl (Nat.le_add_right Dw.p Dw.q)
    have hz : domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (s w) τ' = unflat (GlobalTheory.UnifDens.flatL h w) τ' := by
      rw [← hflat]; rfl
    have hG' : ((hodgeMet T.Z U).gram (cxPt T.Z (U.un k ⟨s w, hs⟩)) (cxFrame T.Z (U.un k ⟨s w, hs⟩)) τ.1).submatrix ec ec =
        ((2 * Real.pi : ℝ) : ℂ) • ((coW (U.X k) (Nat.le_add_right Dw.p Dw.q) (s w) τ')ᴴ *
          (hP (unflat (GlobalTheory.UnifDens.flatL h w) τ'))⁻¹ * coW (U.X k) (Nat.le_add_right Dw.p Dw.q) (s w) τ') := by
      rw [← hz]; exact hG
    rw [transpose_hermitian_gram_submatrix_bijection ec he _ _ _ _ _ hG']

end GlobalTheory.HodgeUnifFrame
