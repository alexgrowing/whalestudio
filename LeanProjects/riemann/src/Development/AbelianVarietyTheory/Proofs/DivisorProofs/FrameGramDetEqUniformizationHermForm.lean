import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ImDiagEqTrace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSqNormEqDot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreUniformisationAppellHumbertUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreIsoUniversalGroupFramedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLiftPreservingAppellHumbertFormStatement

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.LieGram

theorem form_eq_hermForm {K : Type} [Field K] {n g m : ℕ} (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (σ : K →+* ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Wc : Fin n → Fin g → ℂ)
    (hform : ∀ i j, h.form σ (Pi.single i 1) (Pi.single j 1) = Real.pi * hermForm Hm (Wc j) (Wc i))
    (v : Fin m → Fin n → K) (i j : Fin m) :
    h.form σ (v i) (v j) = Real.pi * hermForm Hm (∑ k, σ (v j k) • Wc k) (∑ k, σ (v i k) • Wc k) := by
  have hsum : ∀ a : Fin n → K, a = ∑ k, a k • Pi.single k (1 : K) := fun a => by
    ext t; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hsum (v i), hsum (v j)]
  rw [GlobalTheory.HermFamFrame.form_sum_left]
  simp_rw [GlobalTheory.HermFamFrame.form_sum_right, hform]
  simp only [hermForm, Matrix.mulVec_sum, Matrix.mulVec_smul, star_sum, star_smul, dotProduct_sum,
    sum_dotProduct, smul_dotProduct, dotProduct_smul, Finset.mul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def]
  ring

theorem gram_det_re_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v → ∀ (σ : K →+* ℂ), GoodEmb c (σ.comp (algebraMap c.F K)) → ∀ (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (k : (U (σ.comp (algebraMap c.F K))).Comp) (w : ((U (σ.comp (algebraMap c.F K))).X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt (U (σ.comp (algebraMap c.F K))) k w) (Wu : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnitAt W), z.x = ((U (σ.comp (algebraMap c.F K))).un k w).x → ∀ (C : Fin (Dw.mult ρ) → Fin (Dw.mult ρ) → CAt (σ.comp (algebraMap c.F K))), (∀ i, IsCombAt ((U (σ.comp (algebraMap c.F K))).un k w).x (((U (σ.comp (algebraMap c.F K))).un k w).u ρ) (C i) (z.u ρ i)) → (h.gram σ v).det.re = (Matrix.of fun i j : Fin (Dw.mult ρ) => (Real.pi : ℂ) * hermForm Wu.Hm (∑ l, toC (C j l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ)) (∑ l, toC (C i l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ))).det.re := by
  intro E _ _ _ H Dw l Xo c r U x hL K _ _ _ y B t₀ m1 m2 F h hH ρ v hv σ hσ φ hφ z hz k w W Wu hzx C hC
  obtain ⟨Q, ψ, v', u, Hm, χ, Wc, hfib, hAH, hvec, hform⟩ := hH σ
  obtain ⟨T, m, u', χ', hA', hw'⟩ := GlobalTheory.T.exists_fibre_uniformisation_appellHumbert_unit E H Dw l Xo c r _ _ hL.pos k w W Wu ρ z hzx C hC
  obtain ⟨f, hf, hLB, hq⟩ := GlobalTheory.T.complex_fibre_iso_universal_group_framed_point E H Dw l Xo c K y B t₀ m1 m2 F ρ v hv σ φ hφ z hz Q ψ v' hfib (fun i => (hvec i).1) T m
  choose w' hw'1 hw'2 using hw'
  have htan : ∀ i, IsTangent (v' i) := fun i => GlobalTheory.IsVecOver.isTangent hfib.2.1 (hvec i).1 (F.basis.1 i)
  obtain ⟨Lm, hL1, hL2⟩ := GlobalTheory.T.exists_linear_lift_preserving_appellHumbert_form Q T.pol W.g u Hm χ u' Wu.Hm χ' hAH hA' f hf hLB F.P₀.g v' Wc
    (fun i => ⟨htan i, (hvec i).2⟩) (Dw.mult ρ) (fun i k => σ (v i k)) w' _ hw'2
    (fun i q hq' => hq i q hq' (w' i) (hw'1 i))
  congr 2
  ext i j
  simp only [ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram, Matrix.of_apply]
  rw [form_eq_hermForm h σ Hm Wc hform v i j, ← hL1, hL2, hL2]

end GlobalTheory.LieGram
