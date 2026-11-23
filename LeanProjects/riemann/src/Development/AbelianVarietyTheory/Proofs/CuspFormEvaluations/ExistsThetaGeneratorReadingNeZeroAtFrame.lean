import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatchStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaValueStandardLatticeEqClassicalThetaStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleExistsAndEval
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevelTranslateJetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralHarmonicNeZeroAndIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticDataUnitFrameFramedPointStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.ThetaNoZero

theorem mem_mul_smul_top {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {I J : Ideal R}
    (h : I ⊔ J = ⊤) {x : M} (hI : x ∈ I • (⊤ : Submodule R M)) (hJ : x ∈ J • (⊤ : Submodule R M)) :
    x ∈ (I * J) • (⊤ : Submodule R M) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top : (1 : R) ∈ I ⊔ J)
  have e : x = i • x + j • x := by rw [← add_smul, hij, one_smul]
  rw [e]
  refine Submodule.add_mem _ ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hi hJ
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hj hI

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem dmin_of_isOrtho {X : Data E r} {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
  unfold dmin lminor psgn
  rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, Complex.ofReal_prod,
    ← Fin.prod_univ_eq_prod_range fun a => ((FD.sgn X.p0 a : ℝ) : ℂ)]
  rfl

theorem psgn_mul_self (p i : ℕ) : psgn p i * psgn p i = 1 := by
  unfold psgn
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold FD.sgn
  split_ifs <;> simp

theorem isUnitFr_of_isOrtho {X : Data E r} {x : Frame X.Ψ r} (ho : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i
  rw [dmin_of_isOrtho ho, Complex.norm_real, Real.norm_eq_abs]
  have h := psgn_mul_self X.p0 i
  rcases mul_self_eq_one_iff.1 h with h | h <;> simp [h]

theorem rmul_mem_dom_of_isOrtho {X : Data E r} {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r)
    (ho : X.IsOrtho (rmul x b)) : rmul x b ∈ X.dom := by
  refine fun τ => ⟨?_, fun i => ?_⟩
  · change (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · rw [dmin_of_isOrtho ho, Complex.ofReal_re, psgn_mul_self]
    exact one_pos

theorem mark_sub_mem {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {L : Lt E r}
    {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : IsMark l L mk) {a a' : Dw.La}
    (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) (ha' : a' ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La))
    (h : a' - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ((l.M : E)⁻¹) • mk a' - ((l.M : E)⁻¹) • mk a ∈ L := by
  have h1 := mem_mul_smul_top l.coprime h (Submodule.sub_mem _ ha' ha)
  rw [l.prod, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨z, -, hz⟩ := h1
  have hM : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  rw [← smul_sub, ← map_sub, ← hz, map_smul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul,
    inv_mul_cancel₀ hM, one_smul]
  exact hm.mem z

theorem exists_thGen_rdU_ne_zero : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → r ≤ n → 3 * Formalism.L2.Pj.DF Dw a + 2 ≤ l.M → ∀ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab → ∀ k, ∀ x ∈ (U.X k).dom, ∃ f ∈ thGen Xo c nab a n, Formalism.L2.PjFree.rdU U f k x ≠ 0 := by
  intro hCI E _ _ _ H Dw l Xo c σ r U hσ hU hr t ht hc a n hdom hrn hM _ nab hnab k x hx
  have hrpq : r = Dw.p + Dw.q := hU.1
  obtain ⟨x₀, b, hb, ho, rfl⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r (U.X k).p0 (U.X k).Ψ
    (U.X k).Gm (U.X k).Gm_herm).1 x hx
  have ho : (U.X k).IsOrtho (rmul x b) := ho
  have hx₀ := rmul_mem_dom_of_isOrtho hx hb ho
  obtain ⟨⟨P, hP, hP0⟩, hhom⟩ : (∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0) ∧ _ :=
    ⟨(GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).1 hdom (hrpq ▸ hrn),
      (GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).2⟩
  have hdeg : P.totalDegree ≤ Formalism.L2.Pj.DF Dw a := (hhom P hP.1).totalDegree_le
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨W, Dc, A, θ, v, κ, he, -, hw, hsd, hmk, hmarked, hreads, hth, hmean, hvac, hprod⟩ :=
    GlobalTheory.T.exists_analyticData_unitFrame_framedPoint E H Dw l Xo c σ r U hσ hU hr a n hdom k ⟨rmul x b, hx₀⟩ (isUnitFr_of_isOrtho ho)
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hME : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 hM0
  obtain ⟨-, -, hconj, hmul, hroots⟩ := GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw l r (U.X k) (U.X k).Λ (W.mark k) _ hsd hmk
    (Complex.isPrimitiveRoot_exp l.M hM0)
  obtain ⟨Y, hY⟩ := hroots n l.M (Nat.pos_of_ne_zero hM0)
  have hQ0 : MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P) ≠ 0 := by
    intro h0
    refine hP0 (MvPolynomial.map_injective (algebraMap c.F ℂ) (algebraMap c.F ℂ).injective
      (MvPolynomial.rename_injective _ Dc.eL.injective ?_))
    rw [h0, map_zero, map_zero]
  have hQd : (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).totalDegree ≤
      Formalism.L2.Pj.DF Dw a :=
    (((hhom P hP.1).map (algebraMap c.F ℂ)).rename_isHomogeneous (f := Dc.eL)).totalDegree_le
  obtain ⟨y, hy, hne⟩ := GlobalTheory.T.exists_level_translate_jet_ne_zero_alt E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hdom.2 H.w0 hw
    (U.X k).Λ hsd (rmul x b) hx₀ ho t ht (hc k) (Mfr l) l.M l.odd (by rw [hconj, hmul]) v hvac θ κ hth hmean hprod
    _ hQ0 (by omega)
  choose xs hxs u hu hyx using fun j => hmk.surj _ (hy j)
  obtain ⟨⟨f, hf, hfs⟩, hev⟩ := GlobalTheory.thetaRule_exists_and_eval hCI E H Dw l Xo c nab hnab a n xs P hP
  have hval := GlobalTheory.T.thetaValue_standardLattice_eq_classicalTheta hCI E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e (rmul x b) (U.X k).Λ
    (unC U k ⟨rmul x b, hx₀⟩) A Dc.sympl hx₀ hsd Dw.p n Dc.hr Dc.eL hrpq hdom.2 (he ▸ Dc.dir_eq) nab hnab θ v κ
    hreads hvac hprod (W.mark k) hmk hmarked xs (Y fun j => Submodule.Quotient.mk (xs j))
    (fun j => by
      obtain ⟨⟨a', ha', hq, hYa⟩, hj⟩ := hY (fun j => Submodule.Quotient.mk (xs j)) j
      exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1 hq, hYa⟩, hj⟩)
    a P hP _ (hev f hf ℂ (unC U k ⟨rmul x b, hx₀⟩))
  have hne' := hne (Y fun j => Submodule.Quotient.mk (xs j)) fun j => by
    obtain ⟨⟨a', ha', hq, hYa⟩, -⟩ := hY (fun j => Submodule.Quotient.mk (xs j)) j
    have h1 := mark_sub_mem hmk (hxs j) ha' ((Submodule.Quotient.eq _).1 hq)
    have h2 : y j = ((l.M : E)⁻¹) • W.mark k (xs j) + u j := by
      have := congrArg (fun z => ((l.M : E)⁻¹) • z) (hyx j)
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hME, one_smul, ← Nat.cast_smul_eq_nsmul E l.M (u j)] at this
      exact this
    have h3 := Submodule.sub_mem _ (Submodule.add_mem _ hYa h1) (hu j)
    convert h3 using 1
    rw [h2]
    abel
  rw [← hval] at hne'
  refine ⟨f, ⟨xs, P, hP, hf⟩, fun h0 => hne' ?_⟩
  have hB := (hU.2.2.2.2.1 a n hdom f hfs k).2.1 x hx b hb
  rw [h0, mul_zero] at hB
  have e : Formalism.L2.PjFree.rdU U f k (rmul x b) = Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨rmul x b, hx₀⟩)) := dif_pos hx₀
  exact e.symm.trans hB

end GlobalTheory.ThetaNoZero
