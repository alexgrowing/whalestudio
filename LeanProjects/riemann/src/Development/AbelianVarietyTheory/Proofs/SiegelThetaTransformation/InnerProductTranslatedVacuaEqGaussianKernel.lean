import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatchStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaInnerProductEqRealTorusMeanStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeanRealTorusNormalisedThetaMulConjStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.GaussKer

theorem EFR_sub_right {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (X : Data E r)
    (v a b : WR X n) : EFR X v (a - b) = EFR X v a - EFR X v b := by
  simp only [EFR, hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib, Complex.sub_re]

theorem isRealPt_add {D : D7} {S T : HSp D} {w w' : WO S T} (h : IsRealPt w) (h' : IsRealPt w') :
    IsRealPt (w + w') := by
  unfold IsRealPt at h h' ⊢
  rw [Matrix.map_add (finPart D) (map_add _), h, h', add_zero]

theorem ipO_rho_Th : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ x₁ ∈ C.X.dom, ∀ x₂ ∈ C.X.dom, ∀ φ₁ φ₂ : TF S.rank C.g, SW.IsSB φ₁ → SW.IsSB φ₂ → ∀ w₁ w₂, IsRealPt w₁ → IsRealPt w₂ → ipO μ 𝓕 (C.rho w₁ (C.Th x₁ φ₁)) (C.rho w₂ (C.Th x₂ φ₂)) = dbl C.X C.bas C.idx φ₁ φ₂ 0 * (gaussR C.X C.bas C.idx x₁ (C.zOf x₁ w₁) * conj (gaussR C.X C.bas C.idx x₂ (C.zOf x₂ w₂)) * kZero C.X C.idx x₁ x₂ (C.zOf x₁ w₁) (fun k i => conj (C.zOf x₂ w₂ k i))) := by
  intro D S T C μ 𝓕 hF x₁ hx₁ x₂ hx₂ φ₁ φ₂ hφ₁ hφ₂ w₁ w₂ hw₁ hw₂
  obtain ⟨R, -, -, hadd, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  have hψ := (GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.1
  have hZ₁ := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C x₁ hx₁ φ₁ hφ₁).1
  have hZ₂ := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C x₂ hx₂ φ₂ hφ₂).1
  have hth := GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C
  have hT₁ : C.IsTh (C.rho w₁ (C.Th x₁ φ₁)) := (hth.2.2 _ hZ₁.1).2.1 w₁
  have hT₂ : C.IsTh (C.rho w₂ (C.Th x₂ φ₂)) := (hth.2.2 _ hZ₂.1).2.1 w₂

  have hval : ∀ (w w₀ : WO S T) (x : Frame C.X.Ψ T.rank) (φ : TF S.rank C.g), C.IsZak x φ (C.Th x φ) →
      IsRealPt w → IsRealPt w₀ → C.rho w₀ (C.Th x φ) w =
        cexp (π * I * (EFR C.X (C.realPt w) (C.realPt w₀) : ℝ)) *
          thR C.X C.bas C.idx φ x (C.realPt w + C.realPt w₀) := by
    intro w w₀ x φ hZ hw hw₀
    simp only [Ctx.rho]
    unfold heisO
    rw [hψ w w₀ hw hw₀, hZ.2 _ (isRealPt_add hw hw₀), hadd]
  obtain ⟨N₀, hN₀, hip⟩ := GlobalTheory.T.thetaInnerProduct_eq_realTorusMean D S T C μ 𝓕 hF _ _ hT₁ hT₂
  obtain ⟨N₁, hN₁, hsw⟩ := GlobalTheory.T.mean_realTorus_normalisedTheta_mul_conj D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even
    x₁ hx₁ x₂ hx₂ φ₁ φ₂ hφ₁ hφ₂
  obtain ⟨⟨Fd, hFd⟩, hint⟩ := hip (N₀ * N₁) (Nat.mul_pos hN₀ hN₁) (dvd_mul_right _ _)
  rw [hint Fd hFd (fun v => cexp (π * I * (EFR C.X v (C.realPt w₁ - C.realPt w₂) : ℝ)) *
    (thR C.X C.bas C.idx φ₁ x₁ (v + C.realPt w₁) * conj (thR C.X C.bas C.idx φ₂ x₂ (v + C.realPt w₂)))) ?_]
  · exact hsw (N₀ * N₁) (Nat.mul_pos hN₀ hN₁) (dvd_mul_left _ _) Fd hFd (C.realPt w₁) (C.realPt w₂)
  · intro w hw
    rw [hval w w₁ x₁ φ₁ hZ₁ hw hw₁, hval w w₂ x₂ φ₂ hZ₂ hw hw₂, EFR_sub_right, map_mul, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    have e : (π : ℂ) * I * ((EFR C.X (C.realPt w) (C.realPt w₁) - EFR C.X (C.realPt w) (C.realPt w₂) : ℝ) : ℂ) =
        π * I * (EFR C.X (C.realPt w) (C.realPt w₁) : ℂ) + π * -I * (EFR C.X (C.realPt w) (C.realPt w₂) : ℂ) := by
      push_cast; ring
    rw [e, Complex.exp_add]
    ring

end GlobalTheory.Ker.GaussKer
