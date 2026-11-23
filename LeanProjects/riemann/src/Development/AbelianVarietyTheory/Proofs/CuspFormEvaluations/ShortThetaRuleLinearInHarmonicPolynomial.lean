import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PointsDetectFrobeniusSections
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueLinearInPolynomialStatement

noncomputable section

namespace GlobalTheory.ShortRuleLinear

section General

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem map_mem_HHa {F F₂ : IntermediateField ℚ ℂ} (h : F = F₂) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) F}
    (hP : P ∈ HHa Dw.mult n F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) :
    MvPolynomial.map (IntermediateField.equivOfEq h : F →+* F₂) P ∈
      HHa Dw.mult n F₂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  subst h
  have e : (IntermediateField.equivOfEq (rfl : F = F) : F →+* F) = RingHom.id F := RingHom.ext fun _ => rfl
  rw [e, MvPolynomial.map_id]
  exact hP

theorem eq_sum_of_isShortRule (hC : ChartIndepSt2) (Xo : Moduli Dw l) (c : Coeff l) {n : ℕ} (d : DeltaDat Xo c n)
    (hd : d.IsLev) [StarRing (𝓞 E)] (hn : IsNab d.Xo₂ d.c₂ d.nab₂) (a : (E →+* ℂ) × ℕ → ℕ) (Λ : GenLat E n) (N : ℕ)
    (x0 : Fin n → Dw.La) (hU : Λ.Unimod) (hT : Λ.TrivAt d.l₂.M) (hL : Λ.LevOK N d.l₂.M) (m : ℕ) (cf : Fin m → c.F)
    (Q : Fin m → MvPolynomial (LtN Dw n) c.F) (g : Rul Xo c) (gs : Fin m → Rul Xo c)
    (hQ : ∀ i, Q i ∈ harmL c Λ a) (hg : g ∈ sec Xo c a n) (hgs : ∀ i, gs i ∈ sec Xo c a n)
    (hr : IsShortRule Xo c d Λ N x0 (∑ i, cf i • Q i) g) (hrs : ∀ i, IsShortRule Xo c d Λ N x0 (Q i) (gs i)) :
    g = ∑ i, cf i • gs i := by
  rw [← sub_eq_zero]
  refine GlobalTheory.Frames.ptsDetect_framed E H Dw l Xo c a n _
    (Submodule.sub_mem _ hg (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hgs i))) ?_
  intro k _ _ _ y
  let _ : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have hk : ∀ x : c.F, algebraMap d.c₂.F k (d.eF x) = algebraMap c.F k x := fun x => by
    show algebraMap c.F k (d.eF.symm (d.eF x)) = _
    rw [AlgEquiv.symm_apply_apply]
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  obtain ⟨v, hv, e⟩ := hr k hk y y₂ hy
  choose u hu eu using fun i => hrs i k hk y y₂ hy
  have hm : MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (∑ i, cf i • Q i) =
      ∑ i, d.eF (cf i) • MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (Q i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    rfl
  rw [hm] at hv
  have hlin := GlobalTheory.T.short_theta_value_linear_in_polynomial hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hn n Λ N hU hT hL a (d.w x0) _ m (fun i => d.eF (cf i))
    (fun i => MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (Q i)) (fun i => map_mem_HHa d.hF.symm (hQ i).1) k y₂ v u hv hu
  let L := evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
  have hL : ∀ f, L f = evR Xo c f y := fun _ => rfl
  change L (g - ∑ i, cf i • gs i) = 0
  rw [map_sub, map_sum, hL, e, hlin, Finset.mul_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hL, eu, hk, Algebra.smul_def]
  ring

end General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem shortRule_linear : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), LawsSh T → ∀ (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La), Λ.Unimod → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → ∀ (m : ℕ) (cf : Fin m → T.Q.c.F) (Q : Fin m → MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j) (gs : Fin m → T.R j), (∀ i, Q i ∈ harmL T.Q.c Λ (wtA w)) → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → (∀ i, gs i ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 (∑ i, cf i • Q i) g → (∀ i, IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 (Q i) (gs i)) → g = ∑ i, cf i • gs i := by
  intro hC D T _ hS j hj w Λ N x0 hU hT hL m cf Q g gs hQ hg hgs hr hrs
  obtain ⟨_, hn⟩ := hS.dNab j hj w.n
  exact eq_sum_of_isShortRule hC (T.Q.Xo j) T.Q.c (T.dδ j w.n) (hS.dLev j hj w.n) hn (wtA w) Λ N x0 hU hT hL m cf Q g gs
    hQ hg hgs hr hrs

end GlobalTheory.ShortRuleLinear
