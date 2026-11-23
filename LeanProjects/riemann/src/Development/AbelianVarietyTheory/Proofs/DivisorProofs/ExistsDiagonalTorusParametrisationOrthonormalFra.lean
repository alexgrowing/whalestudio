import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsOrth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementConjugatedByFrameMemSpecialUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtDiagonalTorusZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentMemSpecialUnitaryLieDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperTriangularSignFormDiagonalUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusAnglesOfUnimodularProdOneStatement

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

noncomputable section

namespace GlobalTheory.TorusFrame

theorem gram_mul_of_preserves {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (M x : Matrix (Fin r) (Fin r) ℂ)
    (hM : ∀ u w, hermC τ G (M *ᵥ u) (M *ᵥ w) = hermC τ G u w) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G (M * x) = ReciprocityTheory.ChartRestriction.G.FD.gram τ G x := by
  have hc (a : Fin r) : ReciprocityTheory.ChartRestriction.G.FD.col (M * x) a = M *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col x a := by
    ext k; simp [ReciprocityTheory.ChartRestriction.G.FD.col, mul_apply, mulVec, dotProduct]
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, of_apply, hc, hM]

theorem torus_param : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (Dt : (X.Ψ → Fin (r - 1) → ℝ) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) ∧ (∀ θ θ', t (θ + θ') = t θ * t θ') ∧ Continuous t ∧ HasStrictFDerivAt (fun θ => (fun τ a b => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) Dt 0 ∧ (∀ θ, Dt θ ∈ realLie X.Ψ X.Gm ∧ ∀ τ a b, inFrame x (Dt θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0) ∧ (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) := by
  intro E _ _ _ r X x hx
  refine ⟨fun θ => ⟨torusGL hx θ, GlobalTheory.T.torusElementConjugatedByFrame_mem_specialUnitary E r X x hx θ⟩, torusDer x, ?_, ?_, ?_, ?_, fun θ => GlobalTheory.T.torusTangent_mem_specialUnitaryLie_diagonal E r X x hx θ, ?_⟩
  · intro θ; funext τ
    show ((mat x τ * diagonal (fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))) * (mat x τ)⁻¹ * mat x τ :
      Matrix (Fin r) (Fin r) ℂ) : Fin r → Fin r → ℂ) = (mat x τ * mat (phaseFrame θ) τ : Matrix (Fin r) (Fin r) ℂ)
    rw [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_of_isOrth hx τ), Matrix.mul_one]; rfl
  · intro θ θ'
    refine Subtype.ext (funext fun τ => ?_)
    have hp : phaseU ((θ + θ') τ) = phaseU (θ τ) * phaseU (θ' τ) := by
      refine Units.ext ?_
      simp only [phaseU, Units.val_mul, diagonal_mul_diagonal, Pi.add_apply, angles_add, Complex.ofReal_add,
        mul_add, Complex.exp_add]
    simp only [Subgroup.coe_mul, Pi.mul_apply, torusGL, hp]
    group
  · refine Continuous.subtype_mk (continuous_pi fun τ => ?_) _
    have hph : Continuous fun φ : Fin (r - 1) → ℝ => phaseU φ := by
      refine Units.continuous_iff.2 ⟨Continuous.matrix_diagonal (continuous_pi fun a => ?_),
        Continuous.matrix_diagonal (continuous_pi fun a => ?_)⟩
      · exact Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_angles a)))
      · exact Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_angles a))).neg
    exact (continuous_const.mul (hph.comp (continuous_apply τ))).mul continuous_const
  · exact GlobalTheory.T.hasStrictFDerivAt_diagonalTorus_zero E r X.Ψ x
  · rintro g ⟨b, hb, hgb⟩
    have hgx (τ : X.Ψ) : ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat b τ :=
      congrFun hgb τ
    have hdiag (τ : X.Ψ) := GlobalTheory.T.upperTriangular_signForm_diagonal_unimodular r (mat b τ) (fun a => sgn X.p0 a)
      (fun a => by unfold sgn; split_ifs <;> simp) (isUnit_iff_ne_zero.2 (hb τ).1) (fun a c h => (hb τ).2 a c h) (by
        have h1 := gram_mul_of_preserves τ.1 X.Gm _ (mat x τ) ((g.2 τ).2)
        have hJ := hx τ
        rw [gram_eq] at hJ
        rw [hgx τ, gram_eq, gram_eq, transpose_mul, Matrix.map_mul] at h1
        rw [← hJ]; refine Eq.trans ?_ h1; simp only [Matrix.mul_assoc])
    have hbd (τ : X.Ψ) : mat b τ = diagonal fun a => mat b τ a a := by
      ext a c; by_cases h : a = c
      · subst h; simp
      · simp [diagonal_apply_ne _ h, (hdiag τ).1 a c h]
    have hdet (τ : X.Ψ) : ∏ a, mat b τ a a = 1 := by
      have h := congrArg Matrix.det (hgx τ)
      rw [det_mul, det_mul, (g.2 τ).1, one_mul, hbd τ, det_diagonal] at h
      exact (mul_left_cancel₀ (isUnit_det_of_isOrth hx τ).ne_zero (h.symm.trans (mul_one _).symm))
    choose φ hφ using fun τ : X.Ψ => GlobalTheory.T.exists_torusAngles_of_unimodular_prod_one r (fun a => mat b τ a a) (hdiag τ).2 (hdet τ)
    refine ⟨φ, Subtype.ext (funext fun τ => Units.ext ?_)⟩
    show ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) =
      mat x τ * diagonal (fun a => Complex.exp (Complex.I * (angles (φ τ) a : ℂ))) * (mat x τ)⁻¹
    have hD : (diagonal fun a => Complex.exp (Complex.I * (angles (φ τ) a : ℂ))) = mat b τ := by
      rw [hbd τ]; congr 1; funext a; exact hφ τ a
    rw [hD, ← hgx τ, Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_det_of_isOrth hx τ), Matrix.mul_one]

end GlobalTheory.TorusFrame
