import Formalism.LocalToGlobal.ProjectiveLattices.CompTie
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

theorem extVal_unit_zero (T : CDVR) (u : T.Vˣ) : vV T.V (algebraMap T.V T.Fr (u : T.V)) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr (u : T.V)) = 1 := by
    apply le_antisymm ((IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one _)
    have h2 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (R := T.V) (K := T.Fr) ((u⁻¹ : T.Vˣ) : T.V)
    have h3 : valV T.V (algebraMap T.V T.Fr (u : T.V)) * valV T.V (algebraMap T.V T.Fr ((u⁻¹ : T.Vˣ) : T.V)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    by_contra hlt
    rw [not_le] at hlt
    have : valV T.V (algebraMap T.V T.Fr (u : T.V)) * valV T.V (algebraMap T.V T.Fr ((u⁻¹ : T.Vˣ) : T.V)) < 1 :=
      mul_lt_one_of_lt_of_le hlt h2
    rw [h3] at this
    exact lt_irrefl _ this
  simp [vV, h1]

def OrdTieQZ (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), IsNormDiscrete v → IsTrivOn c.F v →
    ∃ q : QPt Xo c,
      (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
        (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q f) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f = 0 → ordQ Xo c q f = ⊤

theorem height_F1_of_data (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU)
    (hreg : regular₂ Xo c U) (htie : OrdTieQZ h δ)
    (hdL : Dom uL.1 uL.2) (hdE : Dom uet.1 uet.2)
    (hws : ∀ k, wR k ∈ cusp Xo c U uL.1 uL.2) (het : etR ∈ cusp Xo c U uet.1 uet.2)
    (hnz : NoCommonZero Xo c wR) (hnzet : NZAt h etR)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2) (hcc : 0 ≤ cc)
    (nuA : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (halg : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v etR ∧
      (v etR ≠ ⊤ → (⨅ k, v (wR k)) ≤ (nuA la : EReal) + ((cc / (2 * i) : ℝ) : EReal) * v etR)) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).TrivialPlaceHyp := by
  classical
  have hc' : (0 : ℝ) ≤ cc / (2 * i) := div_nonneg hcc (by positivity)

  have hR2 := (hreg.1.2 ⟨uL, hdL⟩ ⟨uet, hdE⟩ (N + 1) (fun k => ⟨wR k, hws k⟩) ⟨etR, het⟩ nuA (cc / (2 * i)) hc'
    hnz (fun la y => halg la y.1 y.2)).2
  unfold Data.TrivialPlaceHyp
  intro Z v hAdm hTv
  obtain ⟨q, hq1, hq0⟩ := htie Z v hAdm.1 hTv

  have hqT : (fun f => ordQ Xo c q f) ∈ trivSet Xo c := by
    refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
    obtain ⟨u, hu⟩ := q.triv a ha
    rw [← hu]
    exact extVal_unit_zero q.T u
  obtain ⟨hE0, hEb⟩ := hR2 ⟨_, hqT⟩
  dsimp only [dataOf, Data.n1] at *
  rw [← huet]
  have hEq : (((ordC (δ Z v) v (wtZ uet.1 uet.2) (valC h uet.1 uet.2 etR Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q etR :=
    hq1 uet.1 uet.2 etR (cusp_le_sec Xo c U _ _ het) (hnzet Z)
  have hEne : ordQ Xo c q etR ≠ ⊤ := by rw [← hEq]; exact EReal.coe_ne_top _
  have hb := hEb hEne
  obtain ⟨k0, hk0⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin (N + 1) => ordQ Xo c q (wR k))
  have hk0le : ordQ Xo c q (wR k0) ≤ ((cc / (2 * i) : ℝ) : EReal) * ordQ Xo c q etR := by
    rw [hk0]; exact hb
  have hev : evC h Z (wR k0) ≠ 0 := by
    intro h0
    rw [hq0 uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hws k0)) h0, ← hEq, ← EReal.coe_mul] at hk0le
    exact EReal.coe_ne_top _ (top_le_iff.1 hk0le)
  have hval : valC h uL.1 uL.2 (wR k0) Z ≠ 0 := valC_ne_zero hev
  have hk0' := hq1 uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hws k0)) hev
  rw [← hk0', ← hEq, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hk0le
  have hle : (⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0}, ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z)) ≤
      ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) :=
    ciInf_le (Set.finite_range _).bddBelow (⟨k0, hval⟩ : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0})
  have hle' : ((⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0}, ordC (δ Z v) v (wtZ uL.1 uL.2)
      (valC h uL.1 uL.2 (wR j) Z) : ℤ) : ℝ) ≤ (ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) : ℝ) := by
    exact_mod_cast hle
  exact hle'.trans hk0le

end Formalism.L2.Pj
