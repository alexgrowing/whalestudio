import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TaylorPSEqTay
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticBiextensionChartComplexPointStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivProdColumnFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionReadingExistsUniqueIsThetaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem sum_support_natCast_smul {σ K : Type} [Field K] [Algebra K ℂ] (N : ℕ) (P : MvPolynomial σ K)
    (hs : ((N : K) • P).support = P.support) (v : (σ →₀ ℕ) → ℂ) :
    ∑ m ∈ ((N : K) • P).support, algebraMap K ℂ (((N : K) • P).coeff m) * v m =
      (N : ℂ) * ∑ m ∈ P.support, algebraMap K ℂ (P.coeff m) * v m := by
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, map_natCast, _root_.mul_assoc]

theorem harm_nab_eq_polyDeriv : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (k n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : Fin n → (Fin g → ℂ) → ℂ), (∀ b, Φ.toAnFr.Rd k (F b) (θ b)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∑ m ∈ P.support, algebraMap c.F ℂ (P.coeff m) * ∏ b, nab y k (F b) (colOf m b) = I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (letDir el) (fun z => ∏ b, θ b (z b)) 0 := by
  intro hC E _ _ _ H Dw l Xo c _ _ y g ty el Φ nab hnab k n F θ hθ a P hP
  classical
  obtain ⟨N, hN, hNP, hs⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  obtain ⟨C₁, hex₁, hpin₁⟩ := hnab.2 ℂ y
  choose f₁ hf₁ using fun b => hex₁ k (F b)
  obtain ⟨C, hd, hh, hF, hu, hgerm⟩ := GlobalTheory.T.exists_analytic_biextension_chart_complex_point E H Dw l Xo c y g ty el Φ hnab.1
  subst hd
  have hdiff : ∀ b, Differentiable ℂ (θ b) := fun b =>
    ((GlobalTheory.T.section_reading_existsUnique_isTheta _ _ _ _ _ Φ.toAnFr k (F b)).2.1 (θ b) (hθ b)).1
  have hg : ∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (tay (θ b) 0) := fun b => by
    have h := hgerm k (F b) (θ b) (hθ b)
    have e : (fun p : Fin 1 × Fin C.d => (p.1, Fin.cast (rfl : C.d = C.d).symm p.2)) = id := rfl
    simp only [e, MvPowerSeries.rename_id, AlgHom.id_apply] at h
    exact h
  have h := hC E H Dw l Xo c hnab.1 ℂ y C₁ C k n F f₁ (fun b => tay (θ b) 0) hf₁ hg a _ hNP
  unfold chartVal at h
  rw [sum_support_natCast_smul N P hs, sum_support_natCast_smul N P hs] at h
  have h' := mul_left_cancel₀ (Nat.cast_ne_zero.2 hN.ne' : (N : ℂ) ≠ 0) h
  have e₁ : ∀ m, ∏ b, nab y k (F b) (colOf m b) =
      ∏ b, C₁.B.nabVal ℂ C₁.h H.w0 k (f₁ b) C₁.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin₁ k (F b) (f₁ b) (hf₁ b) (colOf m b)
  simp only [e₁]
  rw [h']
  have huu : C.uvec = fun ℓ : Lt1 Dw => (Pi.single (el.symm ℓ) 1 : Fin C.d → ℂ) := by
    funext ℓ i
    rw [hu ℓ i, Pi.single_apply]
    rfl
  have hpd := GlobalTheory.T.polyDeriv_prod_column_functions (Fin C.d → ℂ) (E →+* ℂ) Dw.mult n
    (fun ℓ : Lt1 Dw => (Pi.single (el.symm ℓ) 1 : Fin C.d → ℂ)) θ hdiff
    (MvPolynomial.map (algebraMap c.F ℂ) P)
  refine Eq.trans ?_ hpd.symm
  rw [MvPolynomial.support_map_of_injective P (algebraMap c.F ℂ).injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [hh, huu]
  exact nabVal_additive C.B hF H.w0 k ((GlobalTheory.SCV.contDiff_of_differentiable (hdiff b) _).contDiffAt) _ _

end GlobalTheory.AnVal
