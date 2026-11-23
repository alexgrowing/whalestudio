import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReducedStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSectionOfGenericValuesRegularOnChartsStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValuesStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegrallyClosedQuotientOfMemMinimalPrimes

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.IntSec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem wchar_ex_smul {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n d : ℕ) (t : Ix Dw → Sˣ) :
    wchar (ex Dw (d • a) (d * n)) t = wchar (ex Dw a n) t ^ d := by
  unfold wchar
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_mul]
  cases i <;> simp [ex, mul_comm]

theorem one_mem (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : (1 : Rul Xo c) ∈ sec Xo c (0 • a) (0 * n) := by
  refine ⟨fun p q φ y z _ => by simp, fun p t y y' _ => ?_⟩
  rw [wchar_ex_smul]; simp

theorem mul_mem {a : (E →+* ℂ) × ℕ → ℕ} {n d e : ℕ} {f g : Rul Xo c} (hf : f ∈ sec Xo c (d • a) (d * n))
    (hg : g ∈ sec Xo c (e • a) (e * n)) : f * g ∈ sec Xo c ((d + e) • a) ((d + e) * n) := by
  rw [add_smul, add_mul]; exact sec_mul Xo c _ _ _ _ hf hg

theorem pow_mem {a : (E →+* ℂ) × ℕ → ℕ} {n d : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c (d • a) (d * n)) (j : ℕ) :
    f ^ j ∈ sec Xo c ((j * d) • a) ((j * d) * n) := by
  induction j with
  | zero => rw [pow_zero, zero_mul]; exact one_mem a n
  | succ j ih => rw [pow_succ, Nat.succ_mul]; exact mul_mem ih hf

theorem prod_mem {a : (E →+* ℂ) × ℕ → ℕ} {n N : ℕ} {w : Fin N → Rul Xo c} (hw : ∀ i, w i ∈ sec Xo c a n)
    (e : Fin N → ℕ) (s : Finset (Fin N)) :
    ∏ i ∈ s, w i ^ e i ∈ sec Xo c ((∑ i ∈ s, e i) • a) ((∑ i ∈ s, e i) * n) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact one_mem a n
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    refine mul_mem ?_ ih
    have := pow_mem (d := 1) (a := a) (n := n) (f := w i) (by simpa using hw i) (e i)
    rwa [Nat.mul_one] at this

theorem aeval_mem {a : (E →+* ℂ) × ℕ → ℕ} {n N d : ℕ} {w : Fin N → Rul Xo c} (hw : ∀ i, w i ∈ sec Xo c a n)
    {P : MvPolynomial (Fin N) c.F} (hP : P.IsHomogeneous d) :
    MvPolynomial.aeval w P ∈ sec Xo c (d • a) (d * n) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have h1 : ∑ i, s i = d := by
    have := hP (MvPolynomial.mem_support_iff.1 hs)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  rw [← h1]
  exact prod_mem hw s Finset.univ

def evA (hL : EvLaws Xo c) {S : Type} [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    Rul Xo c →ₐ[c.F] S where
  toFun f := evR Xo c f y
  map_one' := evalAt_one _ _ y (hL.test S y)
  map_mul' f g := evalAt_mul _ _ f g y
  map_zero' := evalAt_zero _ _ y
  map_add' f g := evalAt_add _ _ f g y
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    have h1 := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) r 1 y
    rw [evalAt_one _ _ y (hL.test S y), _root_.mul_one] at h1
    exact h1

theorem evC_aeval (hL : EvLaws Xo c) (h : GenFrEx Xo c) (Z : Comp Xo c) {N : ℕ} (w : Fin N → Rul Xo c)
    (P : MvPolynomial (Fin N) c.F) :
    evC h Z (MvPolynomial.aeval w P) = MvPolynomial.aeval (fun s => evC h Z (w s)) P := by
  have := MvPolynomial.comp_aeval_apply (evA hL (genFr h Z)) P (f := w)
  exact this

theorem chart_mem (hL : EvLaws Xo c) {h : GenFrEx Xo c} (C : FChart h) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul Xo c} (hf : f ∈ sec Xo c a n) : wchar (ex Dw a n) C.t * evC h C.Z f ∈ C.R := by
  have h1 := hL.wt a n f hf (Om C.Z) C.t (genFr h C.Z) C.yg (hL.test _ _) (hL.test _ _) C.bor
  have h2 := GlobalTheory.T.naturalRule_value_baseChange_of_isReduced E H Dw l Xo c hL a n f hf C.R (Om C.Z) C.R.val C.y C.yg C.gen
  unfold evC
  rw [← h1, h2]
  exact (evR Xo c f C.y).2

theorem mem_of_integral {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (R : Subalgebra K Ω)
    (sm : Algebra.Smooth K R) (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) (m : ℕ) (r : ℕ → Ω)
    (hr : ∀ i < m, r i ∈ R) (x : Ω) (hx : x ^ m + ∑ i ∈ Finset.range m, r i * x ^ i = 0) : x ∈ R := by
  classical
  have hq : IsIntegrallyClosed (R ⧸ (⊥ : Ideal R)) :=
    GlobalTheory.isIntegrallyClosed_quotient_minimalPrime_of_smooth K R ⊥ (by simp [IsDomain.minimalPrimes_eq_singleton_bot])
  have hR : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv (RingEquiv.quotientBot R)
  have hF : IsFractionRing R Ω := by
    refine IsFractionRing.of_field R Ω fun z => ?_
    obtain ⟨a, ha, b, hb, hb0, e⟩ := frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by rw [eq_div_iff]; exacts [e, hb0]⟩
  let r' : Fin m → R := fun i => ⟨r i, hr i i.2⟩
  have hi : IsIntegral R x := by
    refine ⟨Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (r' i) * Polynomial.X ^ (i : ℕ),
      Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt r'), ?_⟩
    rw [← hx, Finset.sum_range (fun i => r i * x ^ i)]
    simp [Polynomial.eval₂_finset_sum, r']
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
  exact y.2

end GlobalTheory.Reg.IntSec

open GlobalTheory.Reg.IntSec in

theorem GlobalTheory.Reg.exists_sec_of_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (w : Fin N → Rul Xo c), (∀ i, w i ∈ sec Xo c a n) → ∀ (Z : Comp Xo c) (k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) c.F) (b : Om Z), (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → b ^ m + ∑ i ∈ Finset.range m, MvPolynomial.aeval (fun s => evC h Z (w s)) (cf i) * b ^ i = 0 → ∃ g ∈ sec Xo c (k • a) (k * n), evC h Z g = b ∧ (∀ Z', Z' ≠ Z → evC h Z' g = 0) ∧ g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.aeval w (cf i)) * g ^ i = 0 := by
  intro E _ _ _ H Dw l Xo c hL h hA a n N w hw Z k m cf b hcf hb
  classical
  obtain ⟨g, hg, hgv⟩ := GlobalTheory.T.exists_section_of_generic_values_regular_on_charts E H Dw l Xo c hL h hA (k • a) (k * n)
    (Function.update (fun Z' => (0 : Om Z')) Z b) (by
      intro C
      by_cases hZ : C.Z = Z
      · subst hZ
        rw [Function.update_self, wchar_ex_smul]
        refine mem_of_integral C.R C.sm C.frac m
          (fun i => wchar (ex Dw a n) C.t ^ ((m - i) * k) * evC h C.Z (MvPolynomial.aeval w (cf i))) ?_ _ ?_
        · intro i hi
          rw [← wchar_ex_smul]
          exact chart_mem hL C (aeval_mem hw (hcf i hi))
        · have h0 := congrArg (fun x => wchar (ex Dw a n) C.t ^ (k * m) * x) hb
          simp only [mul_zero, mul_add, Finset.mul_sum] at h0
          rw [← h0, mul_pow, ← pow_mul]
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' : k * m = (m - i) * k + k * i := by
            rw [mul_comm (m - i), ← mul_add, Nat.sub_add_cancel (Finset.mem_range.1 hi).le]
          rw [evC_aeval hL, hi', pow_add, mul_pow, ← pow_mul]
          ring
      · rw [Function.update_of_ne hZ, mul_zero]
        exact C.R.zero_mem)
  have hZ : evC h Z g = b := by rw [hgv, Function.update_self]
  have hZ' : ∀ Z', Z' ≠ Z → evC h Z' g = 0 := fun Z' hne => by rw [hgv, Function.update_of_ne hne]
  refine ⟨g, hg, hZ, hZ', ?_⟩
  refine GlobalTheory.T.section_eq_zero_of_genericFramedPoint_values E H Dw l Xo c hL h hA ((k + m * k) • a) ((k + m * k) * n) _ ?_ ?_
  · refine Submodule.add_mem _ (IntSec.mul_mem hg (IntSec.pow_mem hg m)) (Submodule.sum_mem _ fun i hi => ?_)
    have hi' := Finset.mem_range.1 hi
    have e : k + m * k = k + (m - i) * k + i * k := by
      rw [add_assoc, ← add_mul, Nat.sub_add_cancel hi'.le]
    rw [e]
    exact IntSec.mul_mem (IntSec.mul_mem hg (aeval_mem hw (hcf i hi'))) (IntSec.pow_mem hg i)
  · intro Z'
    have e : g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.aeval w (cf i)) * g ^ i =
        g * (g ^ m + ∑ i ∈ Finset.range m, MvPolynomial.aeval w (cf i) * g ^ i) := by
      simp only [mul_add, Finset.mul_sum, _root_.mul_assoc]
    have ev : ∀ f, evC h Z' f = evA hL (genFr h Z') f := fun f => rfl
    rw [e, ev, map_mul]
    by_cases hne : Z' = Z
    · subst hne
      refine mul_eq_zero_of_right _ ?_
      rw [← hb, map_add, map_pow, map_sum, ← ev, hZ]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, ← ev, ← ev, hZ, evC_aeval hL]
    · rw [← ev, hZ' Z' hne, zero_mul]
