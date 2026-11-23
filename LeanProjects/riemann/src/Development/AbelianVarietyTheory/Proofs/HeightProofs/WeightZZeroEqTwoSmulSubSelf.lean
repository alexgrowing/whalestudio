import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.HtXfer
import Formalism.LocalToGlobal.ProjectiveLattices.CompTie
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import Formalism.LocalToGlobal.ProjectiveLattices.ProdInLatPf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LawBddDataOf

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

namespace GlobalTheory.HeightDefinite

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem ex_zero : ex Dw (0 : (E →+* ℂ) × ℕ → ℕ) 0 = fun _ => 0 := by
  funext i; cases i <;> rfl

theorem one_mem_sec : (1 : Rul Xo c) ∈ sec Xo c 0 0 := by
  refine ⟨fun p q φ y z _ => ?_, fun p t y y' _ => ?_⟩
  · show (1 : q.R) = φ 1
    rw [map_one]
  · show (1 : p.R) = wchar (ex Dw 0 0) t * 1
    simp [wchar, ex_zero]

theorem wtZ_zero : wtZ (E := E) 0 0 = 0 := by
  ext <;> simp [wtZ]

theorem evC_one {h : GenFrEx Xo c} (hgt : GenFromTest Xo c h) (Z : Comp Xo c) : evC h Z 1 = 1 :=
  evalAt_one _ _ _ (hgt Z)

theorem exists_nat_comb {ι : Type} [Finite ι] {Ω : ι → Type} [∀ Z, Field (Ω Z)] [∀ Z, CharZero (Ω Z)] {n : ℕ}
    (a : ∀ Z, Fin n → Ω Z) (ha : ∀ Z, ∃ k, a Z k ≠ 0) :
    ∃ m : Fin n → ℕ, ∀ Z, ∑ k, (m k : Ω Z) * a Z k ≠ 0 := by
  classical
  let p : ∀ Z, Polynomial (Ω Z) := fun Z => ∑ k : Fin n, Polynomial.monomial (k : ℕ) (a Z k)
  have hp : ∀ Z, p Z ≠ 0 := by
    intro Z h0
    obtain ⟨k, hk⟩ := ha Z
    have h1 := congrArg (fun q => Polynomial.coeff q (k : ℕ)) h0
    simp only [p, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single k (fun b _ hb => if_neg fun e => hb (Fin.ext e)) (by simp), if_pos rfl] at h1
    exact hk h1
  have hfin : ∀ Z, {t : ℕ | (p Z).IsRoot (t : Ω Z)}.Finite := fun Z =>
    Set.Finite.preimage (f := fun t : ℕ => (t : Ω Z)) Nat.cast_injective.injOn (Polynomial.finite_setOf_isRoot (hp Z))
  obtain ⟨t, ht⟩ := (Set.finite_iUnion hfin).exists_notMem
  refine ⟨fun k => t ^ (k : ℕ), fun Z h0 => ht (Set.mem_iUnion.2 ⟨Z, ?_⟩)⟩
  show (p Z).eval (t : Ω Z) = 0
  rw [← h0]
  simp only [p, Polynomial.eval_finset_sum, Polynomial.eval_monomial, Nat.cast_pow, mul_comm]

variable [Fintype (Comp Xo c)]

theorem supBdd_one (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) : SupBdd Xo c fn 0 0 1 := by
  intro σ
  refine ⟨1, ?_⟩
  rintro _ ⟨y, rfl⟩
  unfold ptNorm
  rw [ex_zero]
  simp only [pow_zero, Finset.prod_const_one, mul_one]
  unfold evalAt
  split_ifs
  · rw [Pi.one_apply, Pi.one_apply, map_one]
    exact le_of_eq (norm_one (α := ℂ))
  · exact le_of_eq_of_le (norm_zero (E := ℂ)) zero_le_one

theorem log_sup_le {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
    {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}
    (hfn : FnNe Xo c fn) (hfg : FnFG Xo c) (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul Xo c} (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (hN : NZSome h f ∨ f = 0) (σ : c.F →+* ℂ) :
    Real.log (⨆ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ), nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) ≤
      Real.log (supR Xo c fn σ a n f) := by
  rcases hN with hN | rfl
  · exact log_supN_le hfn (ptNe_of_fnFG hfg) hcx hS hB hN σ
  · unfold supR supAt
    simp only [valC_zero, nrmC_zero, ptNorm_zero, Real.iSup_const_zero, le_refl]

variable (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N : ℕ) (uL uF uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (etR ta2R : Rul Xo c)
    (nu : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (wsize : WTZ E → ℝ) (DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO : ℝ)

abbrev dat : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z) :=
  dataOf h δ fn yP Dd N 0 1 1 0 uL uF uL uL uL (0, 0) uta2 wR jc np thpR 0 Fin.elim0 uF 0 Fin.elim0 ∅ etR 1 ta2R nu
    (fun _ _ _ => 0) wsize DF PN 1 1 PP0' 1 Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO 0 0

omit [NumberField E] [IsCMField E] in
theorem wt_et : wtZ uL.1 uL.2 = (1 * 1 : ℕ) • wtZ uL.1 uL.2 := by simp

omit [NumberField E] [IsCMField E] in
theorem weightZ_zero_eq_two_smul_sub_self : wtZ ((0, 0) : WtR E).1 ((0, 0) : WtR E).2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ uL.1 uL.2) := by
  rw [sub_self, smul_zero]
  ext <;> simp [wtZ]

theorem height_definite_law_data [Nonempty (HeightOneSpectrum (𝓞 c.F))]
    (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop)
    (hgt : GenFromTest Xo c h)
    (hT : OrdTie h δ cls PY lies) (hTQ : OrdTieQ h δ) (hR1 : RegularityR1ValuedPoints Xo c C cls PY lies) (hR1Q : RegularityR1Quotient Xo c C)
    (hwS : ∀ k, wR k ∈ sec Xo c uL.1 uL.2) (hwC : ∀ k, wR k ∈ C uL.1 uL.2) (hwI : ∀ k, IntAlg (wR k))
    (hpS : ∀ k, thpR k ∈ sec Xo c uF.1 uF.2) (hpC : ∀ k, thpR k ∈ C uF.1 uF.2) (hpI : ∀ k, IntAlg (thpR k))
    (heS : etR ∈ sec Xo c uL.1 uL.2) (heC : etR ∈ C uL.1 uL.2) (heI : IntAlg etR) (heN : NZAt h etR)
    (h2S : ta2R ∈ sec Xo c uta2.1 uta2.2) (h2C : ta2R ∈ C uta2.1 uta2.2) (h2I : IntAlg ta2R) (h2N : NZAt h ta2R)
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2) :
    A2RegularityOrders (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO) := by
  have cases' : ∀ {Z : Comp Xo c} {v : AddValuation (Om Z) (WithTop ℤ)},
      (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).admitted Z v →
      IsNormDiscrete v ∧ ((∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) := by
    intro Z v hA
    obtain ⟨hd, hc⟩ := hA
    exact ⟨hd, hc.imp (fun h' => let ⟨la, ho, _⟩ := h'; ⟨la, ho⟩) (fun h' => h'.1)⟩
  refine ⟨fun Z v hA x hx hx0 => ?_, fun Z v hA x hx hx0 => ?_, fun Z v hA => ?_, fun Z v hA => ?_,
    fun Z v hA => ?_⟩
  · obtain ⟨hd, hc⟩ := cases' hA
    obtain ⟨F, hF, rfl⟩ := exists_of_mem_span_valG h hx
    have h0 := ord_nonneg_of h δ C cls PY lies hT hTQ hR1 hR1Q
      (mem_of_mem_span_int _ (Set.range_subset_iff.2 hwS) hF) (mem_of_mem_span_int _ (Set.range_subset_iff.2 hwC) hF)
      (intAlg_span (Set.forall_mem_range.2 hwI) hF) hd hc (evC_ne_zero_of_valC hx0)
    exact h0
  · obtain ⟨hd, hc⟩ := cases' hA
    obtain ⟨F, hF, rfl⟩ := exists_of_mem_span_valG h hx
    have h0 := ord_nonneg_of h δ C cls PY lies hT hTQ hR1 hR1Q
      (mem_of_mem_span_int _ (Set.range_subset_iff.2 hpS) hF) (mem_of_mem_span_int _ (Set.range_subset_iff.2 hpC) hF)
      (intAlg_span (Set.forall_mem_range.2 hpI) hF) hd hc (evC_ne_zero_of_valC hx0)
    exact h0
  · obtain ⟨hd, hc⟩ := cases' hA
    have h0 := ord_nonneg_of h δ C cls PY lies hT hTQ hR1 hR1Q heS heC heI hd hc (heN Z)
    show 0 ≤ ordC (δ Z v) v ((1 * 1 : ℕ) • wtZ uL.1 uL.2) (valC h uL.1 uL.2 etR Z)
    rw [← wt_et]
    exact h0
  · show 0 ≤ ordC (δ Z v) v ((2 : ℕ) • (wtZ uL.1 uL.2 - wtZ uL.1 uL.2)) (valC h 0 0 1 Z)
    have hz : frW (δ Z v) (0 : WTZ E) = 0 := by
      simp only [frW]
      exact Finset.sum_eq_zero fun i _ => by cases i <;> simp [exZ]
    rw [sub_self, smul_zero]
    simp only [valC, wtZ_zero, evC_one hgt, ordC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, hz,
      AddValuation.map_one, add_zero]
    exact le_rfl
  · obtain ⟨hd, hc⟩ := cases' hA
    have h0 := ord_nonneg_of h δ C cls PY lies hT hTQ hR1 hR1Q h2S h2C h2I hd hc (h2N Z)
    rw [huta2] at h0
    exact h0

theorem htSup_dat (hgt : GenFromTest Xo c h) (hfn : FnNe Xo c fn) (hfg : FnFG Xo c) (hcx : ValAtCx h yP)
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hwS : ∀ k, wR k ∈ sec Xo c uL.1 uL.2) (hwB : ∀ k, SupBdd Xo c fn uL.1 uL.2 (wR k))
    (hwN : ∀ k, NZSome h (wR k) ∨ wR k = 0)
    (hpS : ∀ k, thpR k ∈ sec Xo c uF.1 uF.2) (hpB : ∀ k, SupBdd Xo c fn uF.1 uF.2 (thpR k))
    (hpN : ∀ k, NZSome h (thpR k) ∨ thpR k = 0)
    (h2S : ta2R ∈ sec Xo c uta2.1 uta2.2) (h2B : SupBdd Xo c fn uta2.1 uta2.2 ta2R)
    (h2N : NZSome h ta2R ∨ ta2R = 0)
    (mx : (c.F →+* ℂ) → ℝ) (hmx : ∀ σ k, Real.log (supR Xo c fn σ uL.1 uL.2 (wR k)) ≤ mx σ)
    (hmxm : meanK mx ≤ Gc * wsize (wtZ uL.1 uL.2))
    (hth : ∀ k, meanK (fun σ => Real.log (supR Xo c fn σ uF.1 uF.2 (thpR k))) ≤ Gc * wsize (wtZ uF.1 uF.2))
    (hta1 : 0 ≤ 2 * PI4 * Dd * wsize (wtZ uL.1 uL.2))
    (hta2 : ∀ σ, Real.log (supR Xo c fn σ uta2.1 uta2.2 ta2R) ≤ PI4 * Dd * wsize (wtZ uL.1 uL.2)) :
    (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HtSup := by
  have hmean : ∀ (F : (c.F →+* ℂ) → ℝ) (b : ℝ), (∀ σ, F σ ≤ b) → meanK F ≤ b := by
    intro F b hF
    have hn : (0 : ℝ) < Fintype.card (c.F →+* ℂ) := by
      rw [NumberField.Embeddings.card]; exact_mod_cast Module.finrank_pos
    unfold meanK
    rw [div_le_iff₀ hn]
    refine (Finset.sum_le_sum fun σ _ => hF σ).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (meanK_mono' fun σ => ?_).trans hmxm
    have : Nonempty (Fin (N + 1)) := ⟨0⟩
    exact ciSup_le fun j => (log_sup_le hfn hfg hcx (hwS j) (hwB j) (hwN j) σ).trans (hmx σ j)
  · intro k
    exact (meanK_mono' fun σ => log_sup_le hfn hfg hcx (hpS k) (hpB k) (hpN k) σ).trans (hth k)
  · refine hmean _ _ fun σ => le_trans ?_ hta1
    refine Real.log_nonpos (supN_dataOf_nonneg ..) (Real.iSup_le (fun p => ?_) zero_le_one)
    show nrmC fn (yP p.1) ((2 : ℕ) • (wtZ uL.1 uL.2 - wtZ uL.1 uL.2)) (valC h 0 0 1 p.1) p.2 ≤ 1
    rw [sub_self, smul_zero]
    simp only [valC, wtZ_zero, evC_one hgt, nrmC_single, map_one, norm_one, one_mul]
    refine le_of_eq (Finset.prod_eq_one fun i _ => ?_)
    cases i <;> simp [exZ]
  · refine hmean _ _ fun σ => le_trans ?_ (hta2 σ)
    have h2 := log_sup_le (h := h) (yP := yP) hfn hfg hcx h2S h2B h2N σ
    rw [huta2] at h2
    exact h2

theorem htI2be_dat {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (xR : ℝ)
    (htie : NrmTieU h fn yP U xR wR uL etR uL)
    (hI2 : ∀ σ, GoodEmb c σ → ∀ (k : (U σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ rU),
      x ∈ ((U σ).X k).dom → -Real.log (Real.sqrt (∑ j, recNrm (U σ) xR uL.1 uL.2 (wR j) k x ^ 2)) ≤ tableLineDegreeFive * DF) :
    (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HeightIntegralBoundEstimate := by
  intro Z P
  obtain ⟨σ, hσ, k, x, hx, hw, -⟩ := htie Z P
  have h1 := hI2 σ hσ k x hx
  show -Real.log (Real.sqrt (∑ j, nrmC fn (yP Z) (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) P ^ 2)) ≤
    tableLineDegreeFive * DF + (0 : ℝ) / _ * _ + (0 : ℝ) * tableLineDegreeTwo
  simp only [hw, zero_div, zero_mul, add_zero]
  exact h1

theorem lawBdd_dat (hcx : ValAtCx h yP)
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hwS : ∀ k, wR k ∈ sec Xo c uL.1 uL.2) (hwB : ∀ k, SupBdd Xo c fn uL.1 uL.2 (wR k))
    (hpS : ∀ k, thpR k ∈ sec Xo c uF.1 uF.2) (hpB : ∀ k, SupBdd Xo c fn uF.1 uF.2 (thpR k))
    (heS : etR ∈ sec Xo c uL.1 uL.2) (heB : SupBdd Xo c fn uL.1 uL.2 etR)
    (h2S : ta2R ∈ sec Xo c uta2.1 uta2.2) (h2B : SupBdd Xo c fn uta2.1 uta2.2 ta2R) :
    LawBdd (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO) :=
  GlobalTheory.Reg.LawBddPf.lawBdd_dataOf E H Dw l Xo c h δ fn yP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcx (fun k => ⟨hwS k, hwB k⟩) (fun k => ⟨hpS k, hpB k⟩) ⟨heS, heB⟩
    ⟨one_mem_sec, supBdd_one fn⟩ ⟨h2S, h2B⟩ (wt_et uL) (weightZ_zero_eq_two_smul_sub_self uL) huta2

theorem exists_htConcl (hgt : GenFromTest Xo c h)
    (hne : CompNe Xo c) (hfg : FnFG Xo c) (htr : FnTrdeg Xo c Dd) (hac : FnAlgClosed Xo c)
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (het : NZAt h etR) (hta2 : NZAt h ta2R)
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hfn : FnNe Xo c fn) (hconj : FnConj Xo c fn yP)
    (hbdd : LawBdd (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO))
    (ha1 : A1Bigness (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO))
    (ha2 : A2RegularityOrders (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO))
    (ha3' : LawA3' (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO))
    (sel : Fin (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).del → Fin np)
    (ha4 : A4Selection (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO) sel)
    (hnum : NumOK (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO))
    (ha13 : A13Measurable (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO))
    (hH1 : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).FinitePlaceHyp)
    (hF1d : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).TrivialPlaceHyp)
    (hLAM : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HtLAM)
    (hSup : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HtSup)
    (hI2et : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HeightIntegralEstimateTrivialPlace)
    (hI2be : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).HeightIntegralBoundEstimate) :
    ∃ (hd : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).AxH (fun Z => AG Z))
      (hs : (dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).S1),
      hd.sel = sel ∧ Formalism.MainNotions.Gaps.HeightData.HtConcl ((dat h δ fn yP Dd N uL uF uta2 wR jc np thpR etR ta2R nu wsize DF PN PP0' Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO).htOf hd hs) := by
  have h1 : NZAt h 1 := fun Z => by rw [evC_one hgt]; exact one_ne_zero
  refine ⟨_, _, ?_, htConcl_dataOf h δ fn yP Dd N 0 1 1 0 uL uF uL uL uL (0, 0) uta2 wR jc np thpR 0 Fin.elim0 uF 0
    Fin.elim0 ∅ etR 1 ta2R nu (fun _ _ _ => 0) wsize DF PN 1 1 PP0' 1 Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO 0 0 hne hfg htr hac hwb
    het h1 hta2 (wt_et uL) (weightZ_zero_eq_two_smul_sub_self uL) huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13 hH1 hF1d hLAM hSup hI2et
    hI2be⟩
  obtain ⟨hD, hi, hg, hc0, hc1, hcg, hL, hDF, hrw, hnK, hrd, hP⟩ := hnum
  rfl

section Transfer

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.HeightData

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
  {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra B.KO (A c)]
  [∀ c, Algebra (𝓞 B.KO) (A c)] {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

theorem heights_of_first (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1)
    (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) (hj : ¬ j < D.R.m)
    (hD : d.D = WeightFamilies.dimY D j) (hδ : d.del = G.del) (hL : d.wsize d.wL = wL.size) (hG : d.Gc = Gc)
    (hPH : d.PHc = PH) (hPrw : d.Prw = Prw)
    (hS : ∑ k, (d.htOf hd hs).S k ≤ ∑ k, WeightFamilies.meanLogSup B (G.th' k))
    (hI : IlaTie d hd hs G Qf Gc PH Prw Pet) (h : HtConcl (d.htOf hd hs)) : Heights Qf Gc PH Prw Pet := by
  refine heights_of_htConcl G Qf Gc PH Prw Pet ?_
  obtain ⟨hfin, hsum, hineq, -⟩ := h
  have hle : ∀ la : HeightOneSpectrum (𝓞 B.KO),
      (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
        (((d.htOf hd hs).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la := fun la =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast ENat.toNat_le_toNat (hI la) (hfin la)) (lN_nonneg' _ la)
  have hsum' : Summable fun la : HeightOneSpectrum (𝓞 B.KO) =>
      (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la :=
    Summable.of_nonneg_of_le (fun la => mul_nonneg (Nat.cast_nonneg _) (lN_nonneg' _ la)) hle hsum
  have hDr : ((d.htOf hd hs).D : ℝ) = (WeightFamilies.dimY D j : ℝ) := by exact_mod_cast hD
  have hδr : ((d.htOf hd hs).δ : ℝ) = (G.del : ℝ) := by exact_mod_cast hδ
  have hL' : (d.htOf hd hs).L = wL.size := hL
  have hG' : (d.htOf hd hs).G = Gc := hG
  have hPH' : (d.htOf hd hs).PH = PH := hPH
  have hPrw' : (d.htOf hd hs).Prw = Prw := hPrw
  refine ⟨fun la => ne_top_of_le_ne_top (hfin la) (hI la), hsum', ?_, fun he => absurd he hj⟩
  have ht := Summable.tsum_le_tsum hle hsum' hsum
  have hineq' : 2 * ∑' la : HeightOneSpectrum (𝓞 B.KO),
        (((d.htOf hd hs).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
      (G.del : ℝ) * Real.log G.del + 2 * ∑ k, (d.htOf hd hs).S k +
      8 / 3 * (WeightFamilies.dimY D j : ℝ) * ((WeightFamilies.dimY D j : ℝ) + 4) * G.del * Prw * wL.size +
      2 * ((WeightFamilies.dimY D j : ℝ) + 4) * ((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size := by
    rw [hDr, hδr, hL', hG', hPH', hPrw'] at hineq
    exact hineq
  show 2 * ∑' la : HeightOneSpectrum (𝓞 B.KO),
        (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
      (G.del : ℝ) * Real.log G.del + 2 * ∑ k, WeightFamilies.meanLogSup B (G.th' k) +
      8 / 3 * (WeightFamilies.dimY D j : ℝ) * ((WeightFamilies.dimY D j : ℝ) + 4) * G.del * Prw * wL.size +
      2 * ((WeightFamilies.dimY D j : ℝ) + 4) * ((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size
  linarith

end Transfer

end GlobalTheory.HeightDefinite
