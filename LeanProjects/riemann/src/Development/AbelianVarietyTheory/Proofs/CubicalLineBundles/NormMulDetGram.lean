import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.VolumeFundamentalDomainStdRealBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.TopDifferential

theorem eq_dualMapR {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {F : DualNumber R →+* DualNumber R'}
    (h₁ : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h₂ : F DualNumber.eps = DualNumber.eps) :
    F = Chart.dualMapR f := by
  refine RingHom.ext fun x => ?_
  have e : x = algebraMap R _ x.fst + algebraMap R _ x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, map_add, map_mul, h₁, h₁, h₂, ← e]
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem det_gram {g : ℕ} (Hm W : Matrix (Fin g) (Fin g) ℂ) :
    (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).det.re = Real.pi ^ g * ‖W.det‖ ^ 2 * Hm.det.re := by
  have e : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)) =
      (Real.pi : ℂ) • (W * (Hm * W.conjTranspose)).transpose := rfl
  rw [e, Matrix.det_smul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    Fintype.card_fin, mul_left_comm W.det, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    mul_comm Hm.det, ← _root_.mul_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

theorem norm_mul_det_gram : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (σ : K →+* ℂ) (x' : KeyIn ℂ) (nth nη : ℝ), KeyPB x' (F.key hg rig hr th hth) σ → KeyPow.IsArchNorm x' nth nη → nη * (h.gram σ (Pi.basisFun K (Fin F.P₀.g))).det.re = 1 := by
  intro hU _ K _ _ P F hg rig hr th hth h hH σ x' nth nη hx hn
  obtain ⟨φ, -, w, e, D, hp, hw, -, -, h₁, h₂, hv⟩ := hx
  obtain rfl := eq_dualMapR h₁ h₂
  obtain ⟨u, Hm, W, χ, θ, Fd, hA, -, -, hW, hF, -, rfl⟩ := hn
  obtain ⟨Q, ψ, v, u', Hm', χ', W', a, b, c, d⟩ := hH σ
  change x'.P.g = F.P₀.g at e
  have hf : IsPolFibre σ F.P₀ x'.P φ := ⟨e, hp, LBIso.symm ⟨w, hw⟩⟩
  have key := LieMetric.hermForm_eq hU a hf b hA F.basis.1 c (w' := fun i => x'.v (i.cast e.symm))
    (W' := fun i => W (i.cast e.symm)) fun i => ⟨hv (i.cast e.symm), hW _⟩
  have e₁ : h.gram σ (Pi.basisFun K (Fin F.P₀.g)) =
      (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).submatrix (finCongr e.symm) (finCongr e.symm) := by
    ext i j
    simp only [HermFam.gram, Matrix.of_apply, Pi.basisFun_apply, d, key]
    rfl
  obtain ⟨Ef, t₁, t₂, -, -, t₃, -⟩ := AHWeil.tangent_and_weil_of_isAH hU x'.P _ u Hm χ hA
  have := u.discrete
  have hvol := volume_mul_det_eq_one_of_unimodular _ u.Λ u.full Hm Ef Fd hA.1 hA.2.1 t₁ t₂ hF
  have hdet : W.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det W).1 (Matrix.linearIndependent_rows_iff_isUnit.1
    (LieMetric.linearIndependent_of_isLieBasis u t₃ x'.basis hW))).ne_zero
  have hne : Real.pi ^ x'.P.g * ‖W.det‖ ^ 2 ≠ 0 := by positivity
  rw [e₁, Matrix.det_submatrix_equiv_self, det_gram, ← _root_.mul_assoc, div_mul_cancel₀ _ hne, hvol]

end GlobalTheory.CM.TopDifferential
end
