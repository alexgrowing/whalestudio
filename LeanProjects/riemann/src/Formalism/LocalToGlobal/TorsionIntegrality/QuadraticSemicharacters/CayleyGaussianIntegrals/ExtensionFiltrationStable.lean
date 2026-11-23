import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.KerPNonzero
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.RelIndexEqAbsDetReal

noncomputable section
open scoped BigOperators ComplexConjugate Pointwise
open MeasureTheory Module

namespace Formalism.L2.Th1.H

private theorem exists_real_basis_span_int_eq_of_isLat {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (Λ : AddSubgroup V) (hΛ : IsLat Λ) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ V),
      (Submodule.span ℤ (Set.range b)).toAddSubgroup = Λ := by
  obtain ⟨hdisc, hspan⟩ := hΛ
  let L : Submodule ℤ V := AddSubgroup.toIntSubmodule Λ
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  refine ⟨_, inferInstance, (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L, ?_⟩
  rw [Module.Basis.ofZLatticeBasis_span]
  rfl

theorem fundamentalDomainExists : FundDomain := by
  intro V _ _ _ _ _ μ _ Λ hΛ
  obtain ⟨ι, _, b, hb⟩ := exists_real_basis_span_int_eq_of_isLat Λ hΛ
  subst hb
  set L := (Submodule.span ℤ (Set.range b)).toAddSubgroup with hL
  set D := ZSpan.fundamentalDomain b with hDdef
  have hFD : IsAddFundamentalDomain L D μ := ZSpan.isAddFundamentalDomain b μ
  have hbdd : Bornology.IsBounded D := ZSpan.fundamentalDomain_isBounded b
  have hmeas : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet b
  have hne : μ D ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero b
  have htop : μ D ≠ ⊤ := hbdd.measure_lt_top.ne
  refine ⟨D, hFD, hbdd, ENNReal.toReal_pos hne htop, ?_⟩
  intro Λ' hle hidx
  have hmem : ∀ v : V, v ∈ L → ∀ x : V, (v + x ∈ D ↔ v = -(ZSpan.floor b x : V)) := by
    intro v hv x
    have := ZSpan.vadd_mem_fundamentalDomain b ⟨v, hv⟩ x
    rw [Subtype.ext_iff, Submodule.coe_neg] at this
    exact this
  have hfl : ∀ x : V, (ZSpan.floor b x : V) ∈ L := fun x => (ZSpan.floor b x).2
  set H := Λ'.addSubgroupOf L with hH
  have hcardQ : Nat.card (L ⧸ H) = relIdx Λ' L := rfl
  haveI : Finite (L ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact hidx)
  letI : Fintype (L ⧸ H) := Fintype.ofFinite _
  let rep : L ⧸ H → V := fun q => ((Quotient.out q : L) : V)
  have hrepL : ∀ q, rep q ∈ L := fun q => (Quotient.out q).2
  have hrep : ∀ q : L ⧸ H, ((Quotient.out q : L) : L ⧸ H) = q := fun q => QuotientAddGroup.out_eq' q
  have hdisj : Pairwise (Function.onFun Disjoint fun q : L ⧸ H => rep q +ᵥ D) := by
    intro p q hpq
    rw [Function.onFun, Set.disjoint_left]
    intro y hyp hyq
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hyp hyq
    have e1 := (hmem _ (L.neg_mem (hrepL p)) y).mp hyp
    have e2 := (hmem _ (L.neg_mem (hrepL q)) y).mp hyq
    apply hpq
    have hpq' : rep p = rep q := by
      rw [← neg_neg (rep p), e1, ← e2, neg_neg]
    rw [← hrep p, ← hrep q]
    congr 1
    exact Subtype.ext hpq'
  refine ⟨⋃ q : L ⧸ H, rep q +ᵥ D, ?_, ?_, ?_⟩
  · refine IsAddFundamentalDomain.mk' (MeasurableSet.iUnion fun q => hmeas.const_vadd _).nullMeasurableSet ?_
    intro x
    set l0 : V := -(ZSpan.floor b x : V) with hl0def
    have hl0 : l0 ∈ L := L.neg_mem (hfl x)
    set q0 : L ⧸ H := ((⟨-l0, L.neg_mem hl0⟩ : L) : L ⧸ H) with hq0def
    have hq0 : rep q0 + l0 ∈ Λ' := by
      have h1 := hrep q0
      rw [hq0def, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
      have h2 : -(-(rep q0) + -l0) ∈ Λ' := Λ'.neg_mem (by simpa [rep] using h1)
      rwa [neg_add_rev, neg_neg, neg_neg, add_comm] at h2
    refine ⟨⟨rep q0 + l0, hq0⟩, ?_, ?_⟩
    · show rep q0 + l0 + x ∈ ⋃ q : L ⧸ H, rep q +ᵥ D
      refine Set.mem_iUnion.mpr ⟨q0, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        show -rep q0 + (rep q0 + l0 + x) = l0 + x by abel]
      exact (hmem l0 hl0 x).mpr rfl
    · intro g hg
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hg
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hq
      have hgx : -rep q + (g : V) + x ∈ D := by
        rw [add_assoc]
        exact hq
      have hv : -rep q + (g : V) ∈ L := L.add_mem (L.neg_mem (hrepL q)) (hle g.2)
      have e1 : -rep q + (g : V) = l0 := (hmem _ hv x).mp hgx
      have hqq : q = q0 := by
        rw [← hrep q, hq0def, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        have h3 : -rep q + -l0 = -(g : V) := by
          rw [← e1]
          abel
        have h4 : -(g : V) ∈ Λ' := Λ'.neg_mem g.2
        simpa [rep, h3] using h4
      apply Subtype.ext
      show (g : V) = rep q0 + l0
      rw [← hqq, ← e1]
      abel
  · exact Bornology.isBounded_iUnion.mpr fun q => hbdd.vadd (rep q)
  · have hμ : μ (⋃ q : L ⧸ H, rep q +ᵥ D) = (Fintype.card (L ⧸ H) : ENNReal) * μ D := by
      rw [measure_iUnion hdisj (fun q => hmeas.const_vadd _), tsum_fintype]
      simp [measure_vadd]
    rw [hμ, ENNReal.toReal_mul, ENNReal.toReal_natCast, ← hcardQ, Nat.card_eq_fintype_card]

theorem characterIntegral : CharIntegral := by
  intro V _ _ _ _ _ μ _ H _ hH Λ' D' hD v hv hv0
  set f : V → ℂ := fun z => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H v z : ℂ)) with hf
  have hadd : ∀ x y : V, altE H v (x + y) = altE H v x + altE H v y := by
    intro x y
    simp [altE, map_add]
  have hmul : ∀ x y : V, f (x + y) = f x * f y := by
    intro x y
    simp only [hf, hadd]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hper : ∀ (g : Λ') (z : V), f (g +ᵥ z) = f z := by
    intro g z
    obtain ⟨m, hm⟩ := hv g g.2
    show f ((g : V) + z) = f z
    rw [hmul]
    have : f (g : V) = 1 := by
      simp only [hf, hm]
      have := Complex.exp_int_mul_two_pi_mul_I m
      rw [← this]
      congr 1
      push_cast
      ring
    rw [this, one_mul]
  by_cases hμ : μ D' = 0
  · exact setIntegral_measure_zero _ hμ
  haveI : Countable Λ' := by
    have hc := Measure.countable_meas_pos_of_disjoint_iUnion₀ (μ := μ) (As := fun g : Λ' => g +ᵥ D')
      (fun g => hD.nullMeasurableSet_vadd g) hD.aedisjoint
    have huniv : {g : Λ' | 0 < μ (g +ᵥ D')} = Set.univ := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [measure_vadd]
      exact pos_iff_ne_zero.mpr hμ
    rw [huniv] at hc
    exact Set.countable_univ_iff.mp hc
  have htr : ∀ w : V, ∫ z in D', f z ∂μ = f w * ∫ z in D', f z ∂μ := by
    intro w
    have hD2 : IsAddFundamentalDomain Λ' (w +ᵥ D') μ := hD.vadd_of_comm w
    have e1 : ∫ z in w +ᵥ D', f z ∂μ = ∫ z in D', f z ∂μ := hD2.setIntegral_eq hD hper
    have e2 : ∫ z in w +ᵥ D', f z ∂μ = ∫ z in D', f (w + z) ∂μ := by
      rw [← Set.image_vadd]
      exact (measurePreserving_add_left μ w).setIntegral_image_emb (measurableEmbedding_addLeft w) f D'
    calc ∫ z in D', f z ∂μ = ∫ z in w +ᵥ D', f z ∂μ := e1.symm
      _ = ∫ z in D', f (w + z) ∂μ := e2
      _ = f w * ∫ z in D', f z ∂μ := by
        simp only [hmul]
        rw [integral_const_mul]
  have ha : 0 < (H v v).re := hH v hv0
  set c : ℂ := ((1 / (2 * (H v v).re) : ℝ) : ℂ) * Complex.I with hc
  have hw : altE H v (c • v) = -(1 / 2) := by
    simp only [altE, LinearMap.map_smulₛₗ, hc, smul_eq_mul, Complex.mul_im, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im]
    field_simp
    ring
  have hfw : f (c • v) = -1 := by
    simp only [hf, hw]
    push_cast
    have : 2 * (Real.pi : ℂ) * Complex.I * -(1 / 2) = -(Real.pi * Complex.I) := by ring
    rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have := htr (c • v)
  rw [hfw] at this
  linear_combination this / 2

end Formalism.L2.Th1.H
