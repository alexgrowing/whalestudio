import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaValueStandardLatticeEqClassicalTheta
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetTranslateProjectedVacuumLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleExistsAndEval
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HermFormDiagonalEq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralHarmonicNeZeroAndIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticDataUnitFrameFramedPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThetaPt

theorem isUnitFr_of_isOrtho {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
    {x : Frame X.Ψ r} (ho : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i

  simp only [dmin, lminor]
  rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp_apply, sgn]
  split_ifs <;> simp

theorem sum_norm_coeff_rename_map {K α β : Type} [Field K] (σ : K →+* ℂ) (e : α ≃ β) (P : MvPolynomial α K) :
    ∑ m ∈ (MvPolynomial.rename e (MvPolynomial.map σ P)).support,
      ‖(MvPolynomial.rename e (MvPolynomial.map σ P)).coeff m‖ = ∑ m ∈ P.support, ‖σ (P.coeff m)‖ := by
  classical
  rw [MvPolynomial.support_rename_of_injective e.injective,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective e.injective h]
  simp only [MvPolynomial.coeff_rename_mapDomain _ e.injective, MvPolynomial.coeff_map]
  rw [MvPolynomial.support_map_of_injective _ σ.injective]

theorem theta_bound_ortho : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab → ∀ (xx : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab xx P f → ∀ k (x : (U.X k).dom), (U.X k).IsOrtho x.1 → ∀ lam : ℝ, 0 < lam → lam ^ 2 ≤ (U.X k).firstMinimumSq x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤ (∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n) := by
  intro hCI E _ _ _ H Dw l Xo c σ r U hG hU hr1 t ht hc a n hDom _ nab hnab xx P hP f hf k x ho lam hlam hla

  have hunit : IsUnitFr (U.X k) x.1 := isUnitFr_of_isOrtho ho
  obtain ⟨W, Dc, A, θ, v, κ, hDe, hWg, hw0, hSD, hmark, hAm, hRead, hth1, hmean, hvac, hprod⟩ :=
    GlobalTheory.Dict.VSetup.exists_setup E H Dw l Xo c σ r U hG hU hr1 a n hDom k x hunit
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have hn : Even n := hDom.2

  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨Yr, hYr⟩ : ∃ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E,
      IsRoots l (U.X k).Λ (W.mark k) l.M Y := by
    exact (DualMark.dual_marking E H Dw l r (U.X k) (U.X k).Λ (W.mark k) _ hSD hmark
      (Complex.isPrimitiveRoot_exp l.M hM.ne')).2.2.2.2 n l.M hM
  set Y := Yr fun b => (Submodule.Quotient.mk (xx b) : LevQ Dw l)
  have hY : ∀ b, (∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), a - xx b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧
        Y b - ((l.M : E)⁻¹) • W.mark k a ∈ (U.X k).Λ) ∧
        ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ (U.X k).Λ, s • Y b = (2 * l.M) • u := by
    intro b
    obtain ⟨⟨a', ha', hq, hmem⟩, hj⟩ := hYr (fun b => (Submodule.Quotient.mk (xx b) : LevQ Dw l)) b
    exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1 hq, hmem⟩, hj⟩

  have hval := (GlobalTheory.thetaRule_exists_and_eval hCI E H Dw l Xo c nab hnab a n xx P hP).2 f hf ℂ (unC U k x)
  have hdir : ∀ ℓ, letterDir (U.X k) Dc.hr Dc.idx (Dc.eL ℓ) =
      Pi.single ℓ.2.2 (Pi.single (W.e.symm ⟨ℓ.1, ℓ.2.1⟩) 1) := hDe ▸ Dc.dir_eq
  have heq := GlobalTheory.Dict.thVal_eq_thP hCI E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ
    (unC U k x) A Dc.sympl x.2 hSD Dw.p n Dc.hr Dc.eL hU.1 hn hdir nab hnab θ v κ hRead hvac hprod
    (W.mark k) hmark hAm xx Y hY a P hP _ hval

  have hstd : stdL E n ∈ Vset E n 1 := Base.stdL_mem_Vset n 1
  have hint : IsIntegral ℤ ((H.w0 : 𝓞 E) : E) := (H.w0).isIntegral_coe
  have hproj : projA (U.X k) Dc.bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v = v := by
    rw [(GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn (H.w0 : E) hint hw0 (U.X k).Λ hSD 1
      (stdL E n) hstd).2.2.1 v hvac.1 v hvac, hvac.2.1, one_smul]

  have hlamL : ∀ u ∈ (U.X k).Λ, u ≠ 0 →
      lam ^ 2 ≤ (hx (U.X k) Dc.bas Dc.idx x.1 (pv (U.X k) Dc.idx x.1 u) (pv (U.X k) Dc.idx x.1 u)).re :=
    fun u hu hne => hla.trans ((GlobalTheory.Dict.hx_ortho E r (U.X k) W.g Dc.bas Dc.idx Dc.sympl x.1 x.2 ho).2.2.1 u hu hne)

  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).IsHomogeneous (DF Dw a) :=
    (((GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).2 P
      (by unfold harmA at hP; unfold HaO at hP; exact hP.1)).map _).rename_isHomogeneous
  have hb := GlobalTheory.Dict.VacJet.jet_projA_le E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn H.w0 hw0
    (U.X k).Λ hSD (stdL E n) hstd v hvac x.1 x.2 ho t ht (hc k) θ κ hth1 hmean hprod lam hlam hlamL Y
    (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)) (DF Dw a) hhom

  rw [hproj, AddSubgroup.relIndex_self, Nat.cast_one, one_pow, Real.sqrt_one, _root_.mul_one] at hb
  have hsum : ∑ m ∈ (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).support,
      ‖(MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).coeff m‖ =
        ∑ m ∈ P.support, ‖σ (P.coeff m)‖ := sum_norm_coeff_rename_map σ Dc.eL P
  have hgR : ((W.g : ℕ) : ℝ) = ((fdeg E * r : ℕ) : ℝ) := by rw [hWg]
  have hgn : W.g * n = fdeg E * r * n := by rw [hWg]
  rw [hsum, hgR, hgn] at hb
  have hv0 : Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) = evR Xo c f (unC U k x) := rfl
  rw [hv0, heq]
  exact hb

end GlobalTheory.Dict.ThetaPt
