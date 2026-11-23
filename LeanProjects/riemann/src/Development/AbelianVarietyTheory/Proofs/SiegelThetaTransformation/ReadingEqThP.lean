import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMap
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleMemSec
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConstOfNormFactorUnitFr
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaValueStandardLatticeEqClassicalTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThRead

theorem cmHost_idempotent_trace_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  have hs : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have hc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hs]; simp
    have hre : (τ (H.rt : E)).re = 0 := by
      have a1 := congrArg Complex.re h1
      have a2 := congrArg Complex.im h1
      simp [pow_two] at a1 a2
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      by_contra hne
      have : (τ (H.rt : E)).im = 0 := by
        have : (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at a1
      nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
    rw [cc, IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [hre]
  have h3 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    simpa [cc, map_ofNat] using this
  have : 2 * ((H.w0 : E) + cc (H.w0 : E)) = 2 * 1 := by linear_combination h2 + h3 + hc
  exact mul_left_cancel₀ two_ne_zero this

theorem theta_smul₂ {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} (X : Data E r)
    (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (C : ℂ) (φ : TF n g)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x : Frame X.Ψ r)
    (h : AnalyticOnNhd ℂ (thA X bas idx φ x) Set.univ) :
    thP X hr bas idx (C • φ) P x = C * thP X hr bas idx φ P x := by
  have e : thA X bas idx (C • φ) x = C • thA X bas idx φ x := by
    funext z
    simp only [thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, tsum_mul_left]
    ring
  rw [thP, thP, e, I2.polyDeriv, I2.polyDeriv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_const_smul_apply ((h 0 trivial).contDiffAt)]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem isSB_smul {n g : ℕ} (C : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (C • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp [h0]
  · simp [h2 x y hy]

theorem thValAt_evR (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (nab : NabV Xo c) (hn : IsNab Xo c nab) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} (xs : Fin n → Dw.La)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) {f : Rul Xo c} (hf : IsThRule Xo c nab xs P f)
    (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    ThValAt Xo c nab y xs P (evR Xo c f y) := by
  have hL : Laws := GlobalTheory.allSixLaws.1
  have ht := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S y
  obtain ⟨w, hw, -⟩ := GlobalTheory.thValTot_of_chartIndep hL hC E H Dw l Xo c nab hn S y a n xs P hP
  have e : evR Xo c f y = w := by
    unfold evR evalAt
    rw [dif_pos ht]
    exact GlobalTheory.thetaValue_natural hL hC E H Dw l Xo c nab hn _ S _ _ y ht.choose_spec.choose_spec.choose_spec
      a n xs P hP _ w (hf _ _) hw
  rw [e]
  exact hw

theorem reading_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ n : ℕ, ∀ (W : UW U) (k : U.Comp) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ Dc : Dic Dw c σ (U.X k) W.g Dw.p n a, Dc.e = W.e → ∀ (xs : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab xs P f → f ∈ sec Xo c a n ∧ ∃ φ : TF n W.g, IsSB φ ∧ ∀ x ∈ (U.X k).dom, rdU U f k x = thP (U.X k) Dc.hr Dc.bas Dc.idx φ (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)) x := by
  intro hC E _ _ _ H Dw l Xo c σ r U hσ hU hr1 _ nab hn n W k a hD Dc he xs P hP f hf
  have hL : Laws := GlobalTheory.allSixLaws.1
  have hsec : f ∈ sec Xo c a n := GlobalTheory.thetaRule_mem_sec hL hC E H Dw l Xo c nab hn a n f ⟨xs, P, hP, hf⟩
  refine ⟨hsec, ?_⟩
  have hev : Even n := hD.2
  obtain ⟨-, hsd, hmk, -⟩ := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw1 := cmHost_idempotent_trace_eq_one H
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev _ hw hw1 _ hsd 1 _
    (GlobalTheory.SW.Base.stdL_mem_Vset n 1)).1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨Y, hY⟩ := (GlobalTheory.Dict.DualMark.dual_marking E H Dw l r (U.X k) _ (W.mark k) _ hsd hmk
    (Complex.isPrimitiveRoot_exp l.M hM.ne')).2.2.2.2 n l.M hM
  obtain ⟨ρ, hρ, hnorm⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev _ hw hw1 _ hsd v hv
  set Y₀ := Y (fun b => Submodule.Quotient.mk (xs b)) with hY₀
  have hsb : IsSB (heisG (U.X k) Dc.bas Y₀ v) :=
    ((GlobalTheory.SW.heisG_laws E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev).2.2.2 Y₀ v hv.1).1
  have hhol := GlobalTheory.SW.theta_holomorphic_weight E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hev Dc.k Dc.k'
    _ hsb _ (Dc.mem P hP.1)
  have hS := hU.2.2.2.2.1 a n hD f hsec k
  have hwt : wtOf (U.X k) Dc.hr Dc.k Dc.k' n = laU U a n k := Dc.wt_eq
  rw [hwt] at hhol
  obtain ⟨C, -, hCeq⟩ := GlobalTheory.Dict.const_of_norm_factor_unitFr E r (U.X k) (laU U a n k) Unit
    (fun _ => rdU U f k)
    (fun _ => thP (U.X k) Dc.hr Dc.bas Dc.idx (heisG (U.X k) Dc.bas Y₀ v)
      (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P))) ρ hρ
    (fun _ => ⟨hS.1, hhol.1, fun x hx b hb => ⟨hS.2.1 x hx b hb, hhol.2.1 x hx b hb⟩⟩) (by
      intro x hx hux
      letI : Algebra c.F ℂ := σ.toAlgebra
      obtain ⟨A, hA, θ, hθ, hmean⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k Dc.bas Dc.idx Dc.sympl
        (he ▸ Dc.per_eq) (he ▸ Dc.ty_eq) ⟨x, hx⟩ hux
      have h1 := GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hsd θ hθ
      obtain ⟨κ, hκ⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hev _ hw hw1 _ hsd v hv x hx θ h1
      refine ⟨κ, hnorm x hx hux θ κ h1 hmean hκ, fun _ => ?_⟩
      have hval := thValAt_evR hC Xo c nab hn xs hP hf ℂ (unC U k ⟨x, hx⟩)
      have := GlobalTheory.Dict.thVal_eq_thP hC E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hsd Dw.p n Dc.hr
        Dc.eL hU.1 hev (he ▸ Dc.dir_eq) nab hn θ v κ hθ hv hκ (W.mark k) hmk hA xs Y₀ (fun b => by
          obtain ⟨⟨a', ha', hq, hy⟩, hj⟩ := hY (fun b => Submodule.Quotient.mk (xs b)) b
          exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1 hq, hy⟩, hj⟩) a P hP _ hval
      refine Eq.trans ?_ this
      show (if h : x ∈ (U.X k).dom then Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) = _
      rw [dif_pos hx]
      rfl)
  refine ⟨C • heisG (U.X k) Dc.bas Y₀ v, isSB_smul C hsb, fun x hx => ?_⟩
  rw [theta_smul₂ _ _ _ _ _ _ _ _ (hhol.2.2.2 x hx)]
  exact hCeq () x hx

end GlobalTheory.Dict.ThRead
