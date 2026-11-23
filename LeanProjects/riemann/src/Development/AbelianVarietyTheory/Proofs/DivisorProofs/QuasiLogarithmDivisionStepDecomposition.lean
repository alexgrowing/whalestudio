import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentOfQuasiLogarithmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDecompositionOfTangentDivisibleByPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfLinearZeroCoboundaryZeroFractionsStatement

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogStep

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}

theorem constantCoeff_up_eq_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) : constantCoeff (up E μ i) = 0 := by
  rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ,
    map_zero]

theorem ql_add {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {N : Ideal O} {f g : MvPowerSeries (Fin d) E} (hf : QL μ N f) (hg : QL μ N g) :
    QL μ N (f + g) := by
  obtain ⟨f0, f1, f2⟩ := hf
  obtain ⟨g0, g1, g2⟩ := hg
  refine ⟨by rw [map_add, f0, g0, add_zero], fun i => ?_, fun α => ?_⟩
  · obtain ⟨a, ha, ha'⟩ := f1 i
    obtain ⟨b, hb, hb'⟩ := g1 i
    refine ⟨a + b, N.add_mem ha hb, ?_⟩
    simp only [lin, map_add] at ha' hb' ⊢
    rw [ha', hb']
  · obtain ⟨a, ha, ha'⟩ := f2 α
    obtain ⟨b, hb, hb'⟩ := g2 α
    refine ⟨a + b, N.add_mem ha hb, ?_⟩
    rw [formalCoboundary_add (constantCoeff_up_eq_zero hμ), map_add, ha', hb', map_add]

theorem ql_smul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {N : Ideal O} (a : O) {f : MvPowerSeries (Fin d) E} (hf : QL μ N f) :
    QL μ N (algebraMap O E a • f) := by
  obtain ⟨f0, f1, f2⟩ := hf
  refine ⟨?_, fun i => ?_, fun α => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, f0,
      mul_zero]
  · obtain ⟨b, hb, hb'⟩ := f1 i
    refine ⟨a * b, N.mul_mem_left a hb, ?_⟩
    simp only [lin, coeff_smul] at hb' ⊢
    rw [hb', map_mul]
  · obtain ⟨b, hb, hb'⟩ := f2 α
    refine ⟨a * b, N.mul_mem_left a hb, ?_⟩
    rw [formalCoboundary_smul (constantCoeff_up_eq_zero hμ), coeff_smul, hb', map_mul]

theorem ql_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    (N : Ideal O) : QL μ N (0 : MvPowerSeries (Fin d) E) := by
  refine ⟨map_zero _, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, fun α => ⟨0, N.zero_mem, ?_⟩⟩
  have := formalCoboundary_smul (constantCoeff_up_eq_zero (E := E) hμ) 0 0
  rw [zero_smul, zero_smul] at this
  rw [this, map_zero, map_zero]

theorem comb_add {ι : Type} [Fintype ι] (b b' : ι → O) (e : ι → MvPowerSeries (Fin d) E) :
    comb (b + b') e = comb b e + comb b' e := by
  simp only [comb, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem ql_comb {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {ι : Type} [Fintype ι] (b : ι → O) (e : ι → MvPowerSeries (Fin d) E)
    (he : ∀ i, QL μ ⊤ (e i)) : QL μ ⊤ (comb b e) := by
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.cons_induction with
  | empty => rw [Finset.sum_empty]; exact ql_zero hμ _
  | cons i s hi ih => rw [Finset.sum_cons]; exact ql_add hμ (ql_smul hμ _ (he i)) ih

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), (∀ i, QL c.μ ⊤ (e i)) → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → (∀ i, lin (e (Sum.inl i)) = Pi.single i 1) → (∀ j, c.IsLie (e (Sum.inr j)) (lb j)) → ∀ f, QL c.μ ⊤ f → ∃ (b : Fin d ⊕ Fin k → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL c.μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁ := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF k e lb hQe hcob hlin hLie f hf
  have hμ := c.isLaw.const
  have hinj : Function.Injective (algebraMap O E) := hF.inj
  have hc0 := constantCoeff_up_eq_zero (E := E) hμ

  let t : Fin d ⊕ Fin k → G.dual.Lie := Sum.elim (fun _ => 0) fun j => lb j
  have ht : ∀ i, c.IsLie (e i) (t i) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hF _ (hQe (Sum.inl i))
      have := ((GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF _ _ l l 0 hl hl).2.2 (hcob i))
      subst this
      exact hl
    · exact hLie j

  have hcombS : ∀ (b : Fin d ⊕ Fin k → O) (S : Finset (Fin d ⊕ Fin k)),
      c.IsLie (∑ i ∈ S, algebraMap O E (b i) • e i) (∑ i ∈ S, b i • t i) ∧
        QL c.μ ⊤ (∑ i ∈ S, algebraMap O E (b i) • e i) := by
    intro b S
    induction S using Finset.cons_induction with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact ⟨c.isLie_zero hinj, ql_zero hμ _⟩
    | cons i s hi ih =>
      rw [Finset.sum_cons, Finset.sum_cons, add_comm, add_comm (b i • t i)]
      exact ⟨(GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF _ _ _ _ (b i) ih.1 (ht i)).1 ih.2 (hQe i),
        ql_add hμ ih.2 (ql_smul hμ _ (hQe i))⟩
  have hcombLie : ∀ b : Fin d ⊕ Fin k → O, c.IsLie (comb b e) (∑ i, b i • t i) :=
    fun b => (hcombS b Finset.univ).1

  obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hF f hf
  let b0 : Fin d ⊕ Fin k → O := Sum.elim (0 : Fin d → O) fun j => lb.repr l j
  have hb0 : ∑ i, b0 i • t i = l := by
    rw [Fintype.sum_sum_type]
    simp only [b0, t, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
      zero_add]
    exact lb.sum_repr l
  set f' := f + algebraMap O E (-1) • comb b0 e with hf'
  have hQf' : QL c.μ ⊤ f' := ql_add hμ hf (ql_smul hμ _ (ql_comb hμ b0 e hQe))
  have hLf' : c.IsLie f' ((p : O) • 0) := by
    have := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF f (comb b0 e) l _ (-1) hl (hcombLie b0)).1 hf
      (ql_comb hμ b0 e hQe)
    rwa [hb0, neg_one_smul, add_neg_cancel, ← smul_zero (p : O)] at this
  obtain ⟨s, g, hg, hh⟩ := GlobalTheory.T.quasiLogarithm_decomposition_of_tangent_divisible_by_p p C v O hv G d c E hF f' 0 hQf' hLf'
  set h := f' - map (algebraMap O E) s - g with hhdef

  have hw : ∀ i, ∃ w : O, lin g i = algebraMap O E w := by
    intro i
    obtain ⟨b1, -, hb1⟩ := hQf'.2.1 i
    obtain ⟨b3, -, hb3⟩ := hh.2.1 i
    refine ⟨b1 - coeff (Finsupp.single i 1) s - b3, ?_⟩
    have : g = f' - map (algebraMap O E) s - h := by rw [hhdef]; ring
    simp only [lin] at hb1 hb3 ⊢
    rw [this, map_sub, map_sub, hb1, hb3, coeff_map, map_sub, map_sub]
  choose w hw using hw
  let bw : Fin d ⊕ Fin k → O := Sum.elim w 0
  have hcw : comb bw e = ∑ i, algebraMap O E (w i) • e (Sum.inl i) := by
    simp [comb, bw, Fintype.sum_sum_type]

  have hgw : g = comb bw e := by
    have key := GlobalTheory.T.eq_zero_of_lin_zero_cob1_zero p O E hF d c.μ c.isLaw (g - comb bw e) ?_ ?_
    · exact sub_eq_zero.1 key
    · funext i
      simp only [lin, hcw, map_sub, map_sum, coeff_smul, Pi.zero_apply] at hw ⊢
      have hl' : ∀ j, coeff (Finsupp.single i 1) (e (Sum.inl j)) =
          (Pi.single j (1 : E) : Fin d → E) i := fun j => congrFun (hlin j) i
      simp only [hl', hw]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, Ne.symm hj]) (by simp)]
      simp
    · let L : MvPowerSeries (Fin d) E →+ MvPowerSeries (Fin d ⊕ Fin d) E :=
        AddMonoidHom.mk' (cob1 (up E c.μ)) (formalCoboundary_add hc0)
      have hL : ∀ x, L x = cob1 (up E c.μ) x := fun _ => rfl
      rw [← hL, map_sub, hcw, map_sum]
      simp only [hL, formalCoboundary_smul hc0, hcob, smul_zero, Finset.sum_const_zero, sub_zero]
      exact hg

  obtain ⟨u, hu⟩ := hF.unit_p
  refine ⟨bw + b0, s, (↑u⁻¹ : E) • h, ?_, ?_⟩
  · obtain ⟨h0, h1, h2⟩ := hh
    refine ⟨?_, fun i => ?_, fun α => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0,
        mul_zero]
    · obtain ⟨b, hb, hb'⟩ := h1 i
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton.1 hb
      refine ⟨b', trivial, ?_⟩
      simp only [lin, coeff_smul] at hb' ⊢
      rw [hb', map_mul, map_natCast, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    · obtain ⟨b, hb, hb'⟩ := h2 α
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton.1 hb
      refine ⟨b', trivial, ?_⟩
      rw [formalCoboundary_smul hc0, coeff_smul, hb', map_mul, map_natCast, ← hu, ← mul_assoc, Units.inv_mul,
        one_mul]
  · rw [smul_smul, ← hu, Units.mul_inv, one_smul, comb_add, ← hgw]
    rw [map_neg, map_one, neg_one_smul] at hf'
    rw [hhdef, hf']
    ring

end GlobalTheory.QLogStep
