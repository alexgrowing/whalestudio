import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NormMulDetGram

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.CM.TopLieVector

theorem sq_eq_det_gram : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (h : HermFam K (Fin x.P.g → K)), (GenFib.mk x.P φ hf x.v x.basis : GenFib A).IsHerm h → ∀ (T abelian₂ : MLine K) (s : K →+* ℂ), KeyArchAt x T abelian₂ s → abelian₂.n s ^ 2 = (h.gram s (fun i : Fin x.P.g => Pi.single i 1)).det.re := by
  intro hU _ K _ _ P x φ₀ hf₀ h hH T abelian₂ σ hx
  obtain ⟨x', u, Hm, W, χ, θ, Fd, hx, hA, -, -, hW, hF, -, hn⟩ := hx
  obtain ⟨φ, -, w, e, D, hp, hw, -, -, h₁, h₂, hv⟩ := hx
  obtain rfl := TopDifferential.eq_dualMapR h₁ h₂
  obtain ⟨Q, ψ, v, u', Hm', χ', W', a, b, c, d⟩ := hH σ
  have hf : IsPolFibre σ x.P x'.P φ := ⟨e, hp, LBIso.symm ⟨w, hw⟩⟩
  have key := LieMetric.hermForm_eq hU a hf b hA x.basis.1 c (w' := fun i => x'.v (i.cast e.symm))
    (W' := fun i => W (i.cast e.symm)) fun i => ⟨hv (i.cast e.symm), hW _⟩
  have e₁ : h.gram σ (fun i : Fin x.P.g => Pi.single i 1) =
      (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).submatrix (finCongr e.symm) (finCongr e.symm) := by
    ext i j
    exact (d i j).trans (congrArg (fun z => (Real.pi : ℂ) * z) (key j i))
  obtain ⟨Ef, t₁, t₂, -, -, t₃, -⟩ := AHWeil.tangent_and_weil_of_isAH hU x'.P _ u Hm χ hA
  have := u.discrete
  have hvol := volume_mul_det_eq_one_of_unimodular _ u.Λ u.full Hm Ef Fd hA.1 hA.2.1 t₁ t₂ hF
  rw [e₁, Matrix.det_submatrix_equiv_self, TopDifferential.det_gram, hn, div_eq_mul_inv,
    eq_inv_of_mul_eq_one_right hvol]

end GlobalTheory.CM.TopLieVector
end
