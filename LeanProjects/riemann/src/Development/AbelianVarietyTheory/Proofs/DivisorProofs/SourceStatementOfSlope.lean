import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSetupCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BudgetOfSizeAndWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBoundOfHeightPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalHeightBoundOfLatticeBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulCardPsi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagNonempty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyRingHomComplexOfLeContinuum
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HostFieldGaloisDegreeDiscrConjMovesPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentsBijectModuliComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspSectionExtendsComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRankLeSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomNormSqEqInfiniteSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspSectionValuationBoundPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightValuationLeRecursiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVolumeLeCountStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MbarSectionsCuspidalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteNormSqExponentialBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNormBoundedMbarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MbarSemipositiveNefSmallRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSemipositiveFibrewiseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MbarDegreeTendstoIntersectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefSectionGrowthLeIntersectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLogSumAndPrimeBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovHt.Link

theorem nrmInf_twist {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} (M : Adl C Y) (t : ℝ)
    (cf : HeightOneSpectrum (𝓞 F) → ℝ) (σ : F →+* ℂ) (τ : ℕ) (f : Y.Fn) (y : Pts Y σ) :
    (M.twist (fun _ => t) cf).nrmInf σ τ f y = Real.exp (-((τ : ℝ) * t)) * M.nrmInf σ τ f y := by
  simp only [Adl.nrmInf, Adl.twist, Pi.add_apply]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem nrmFin_twist {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} (M : Adl C Y)
    (ci : InfinitePlace F → ℝ) (cf : HeightOneSpectrum (𝓞 F) → ℝ) (v : HeightOneSpectrum (𝓞 F)) (τ : ℕ) (f : Y.Fn)
    (e : Ext v) (y : AlgPt Y) :
    (M.twist ci cf).nrmFin v τ f e y = Real.exp (-((τ : ℝ) * cf v)) * M.nrmFin v τ f e y := by
  have hn : ((M.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast M.n.ne_zero
  simp only [Adl.nrmFin, Adl.twist]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  field_simp
  ring

theorem reindex {ι ι' : Type} [Fintype ι] [Fintype ι'] (ψ : ι ≃ ι') {n n' : ℕ} (h : n' = n) (u : ι' → Fin n' → ℤ) :
    (∑ t, ∑ i, |(u (ψ t) (Fin.cast h.symm i) : ℝ)| = ∑ τ, ∑ i, |(u τ i : ℝ)|) ∧
    (⨆ x : ι × Fin n, |(u (ψ x.1) (Fin.cast h.symm x.2) : ℝ)|) = (⨆ x : ι' × Fin n', |(u x.1 x.2 : ℝ)|) ∧
    (∑ t, ((⨆ i, (u (ψ t) (Fin.cast h.symm i) : ℝ)) - ⨅ i, (u (ψ t) (Fin.cast h.symm i) : ℝ)) =
      ∑ τ, ((⨆ i, (u τ i : ℝ)) - ⨅ i, (u τ i : ℝ))) ∧
    Formalism.DegreeFormula.weylProd (fun t i => (u (ψ t) (Fin.cast h.symm i) : ℝ)) = ((vdm u : ℤ) : ℝ) / (vdm (stdWt ι' n') : ℤ) := by
  subst h
  refine ⟨ψ.sum_comp fun τ => ∑ i, |(u τ i : ℝ)|, (ψ.prodCongr (Equiv.refl _)).iSup_comp (g := fun x => |(u x.1 x.2 : ℝ)|),
    ψ.sum_comp fun τ => (⨆ i, (u τ i : ℝ)) - ⨅ i, (u τ i : ℝ), ?_⟩
  rw [show ((vdm u : ℤ) : ℝ) = _ from map_vdm (Int.castRingHom ℝ) u, ← weylProd_eq]
  exact ψ.prod_comp fun τ => ∏ i, ∏ k, if i < k then ((u τ i : ℝ) - u τ k) / ((k : ℝ) - (i : ℝ)) else 1

theorem l1_nsmul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (τ : ℕ) (u : AllWt.Weight Dw) : l1 (τ • u) = τ * l1 u := by
  simp [l1, Finset.mul_sum, abs_mul]

section Small

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} {Φ : s.Flag}

theorem nonneg_mixVals (hP : Hypotheses2) (hH : HypothesesH) {k : s.Comp} {Z : Comp s.Xo κ.c} (hZ : Over Φ k Z)
    {la : AllWt.Weight S.Dw} {g : Rul s.Xo κ.c} (hg : g ∈ cuspOn (unf s) Z (wtOf S.Dw la 0))
    (h0 : (Φ.C k).val g ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la)) {B : ℝ}
    (hf : ∀ v e y, finN Φ k la v e y ((Φ.C k).val g) ≤ Real.exp (-(htLog κ B v * l1 la)))
    (pl : HeightOneSpectrum (𝓞 κ.c.F)) (w : Rul s.Xo κ.c → EReal) (hw : w ∈ (mixVals s.Xo κ.c B).1 pl) : 0 ≤ w g := by
  have hs : g ∈ secZ s.Xo κ.c (exOf S.Dw la 0) := cuspW_le_secZ _ hg.1
  have hl : 0 ≤ l1 la := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨-, -, hL⟩ := GlobalTheory.T.height_log_sum_and_prime_bound D A κ B
  by_cases h : ∃ p ∈ htPrimes κ.l B, ((p : ℕ) : 𝓞 κ.c.F) ∈ pl.asIdeal
  · obtain ⟨p, hp, hpl⟩ := h
    rw [mixVals_of_mem hp hpl] at hw
    have : IsGalois ℚ D.host.E := (GlobalTheory.PlaceInt.host_galois_discr_moves D A.H).1
    obtain ⟨v, hv, hle⟩ := GlobalTheory.T.height_valuation_le_recursive (GlobalTheory.T.diagonal_height_bound_of_lattice_bound (GlobalTheory.T.lattice_bound_of_height hP)) _ A.H S.Dw κ.l s.Xo κ.c p pl hp.1 hpl w hw
    have h1 := (GlobalTheory.T.cusp_section_valuation_bound_prime hP hH D A N j S κ s Φ k Z hZ la g hs hg.2 h0 pl p hp.1 hpl (htEx D.host.E p * l1 la)
      (fun v _ e y => (hf v e y).trans ?_) v hv).trans (hle la g hs)
    · rw [mul_assoc] at h1
      induction hx : w g using EReal.rec with
      | bot => rw [hx, EReal.bot_add] at h1; exact absurd h1 (EReal.bot_lt_coe _).not_ge
      | top => exact le_top
      | coe b =>
        rw [hx, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
        exact EReal.coe_nonneg.2 (by linarith)
    · have h2 : 0 < NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL) :=
        AbsoluteValue.pos _ (Nat.cast_ne_zero.2 hp.1.ne_zero)
      rw [Real.rpow_def_of_pos h2, Real.exp_le_exp]
      have := mul_le_mul_of_nonneg_right ((hL v).2 p hp) hl
      linarith
  · have e : (mixVals s.Xo κ.c B).1 pl = (recVals s.Xo κ.c).1 pl := if_neg h
    rw [e] at hw
    obtain ⟨p, hp, hpl⟩ : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 κ.c.F) ∈ pl.asIdeal := by
      have := pl.isMaximal
      have := Ideal.finiteQuotientOfFreeOfNeBot pl.asIdeal pl.ne_bot
      letI := Ideal.Quotient.field pl.asIdeal
      refine ⟨ringChar (𝓞 κ.c.F ⧸ pl.asIdeal), CharP.char_prime_of_ne_zero (𝓞 κ.c.F ⧸ pl.asIdeal)
        (CharP.ringChar_ne_zero_of_finite _), Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
      rw [map_natCast]
      exact ringChar.Nat.cast_ringChar
    have h1 := GlobalTheory.T.cusp_section_valuation_bound_prime hP hH D A N j S κ s Φ k Z hZ la g hs hg.2 h0 pl p hp hpl 0
      (fun v _ e y => (hf v e y).trans (by
        rw [Real.rpow_zero]
        exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (hL v).1 hl)))) w hw
    simpa using h1

theorem encard_small_le (hP : Hypotheses2) (hH : HypothesesH) {k : s.Comp} {Z : Comp s.Xo κ.c} (hZ : Over Φ k Z) (x : ToroidalCompactificationData s)
    {u : AllWt.Weight S.Dw} (hu : ∀ τ, Antitone (u τ)) (M : Adl (cxSt D.what₂.LL) (Φ.C k).Y) {B C r : ℝ} (t : ℝ)
    {cX : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ} {τ : ℕ} (h1 : ∀ f ∈ M.secs τ, IsCuspSec Φ k (τ • u) f)
    (h2 : ∀ f ∈ M.secs τ, ∀ σ, ∀ y ∈ offBd Φ k σ, infSq Φ k x (τ • u) σ f y ≤ (Real.exp (C * r * τ) * M.nrmInf σ τ f y) ^ 2)
    (h3 : ∀ f ∈ M.secs τ, ∀ v e y, finN Φ k (τ • u) v e y f ≤
      M.nrmFin v τ f e y * Real.exp (τ * (r * cX v + htLog κ B v * l1 u))) :
    ((M.twist (fun _ => t - C * r) fun v => -(r * cX v + 2 * (htLog κ B v * l1 u))).small τ).encard ≤
      (smallOn (unf s) (xiR D) (mixVals s.Xo κ.c B) Z (τ • wtOf S.Dw u 0) (Real.exp (τ * t))).encard := by
  rw [nsmul_wtOf, smul_zero]
  refine (Set.encard_le_encard fun f hf => ?_).trans
    (Set.encard_image_le (fun g : cuspOn (unf s) Z (wtOf S.Dw (τ • u) 0) => (Φ.C k).val g) _)
  have hs : f ∈ M.secs τ := hf.1
  obtain ⟨g, hg, rfl⟩ := GlobalTheory.T.cusp_section_extends_component D A N j S κ s Φ k Z hZ (τ • u)
    (fun a _ _ h => nsmul_le_nsmul_right (hu a h) τ) f (h1 f hs)
  refine ⟨⟨g, hg⟩, ⟨nonneg_mixVals hP hH hZ hg (h1 _ hs).1 fun v e y => (h3 _ hs v e y).trans ?_,
    fun σ hσ z hz => ?_⟩, rfl⟩
  · have h4 := hf.2.2 v e y
    rw [nrmFin_twist, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one] at h4
    refine (mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le).trans_eq ?_
    rw [← Real.exp_add, l1_nsmul]
    congr 1
    ring
  · obtain ⟨σ', y, hy, e⟩ := GlobalTheory.T.hom_norm_sq_eq_infinite_sq D A N j S κ s Φ x k Z hZ (τ • u) g hg σ hσ z hz
    have h4 := hf.2.1 σ' y
    rw [nrmInf_twist, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one] at h4
    have h5 : 0 ≤ M.nrmInf σ' τ ((Φ.C k).val g) y :=
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (CxSt.pn_nonneg _ _ _ _ _ _ _) _)
    refine (pow_le_pow_iff_left₀ (homN_nonneg _ _ _ _ _) (Real.exp_pos _).le two_ne_zero).1
      (e.trans_le ((h2 _ hs σ' y hy).trans (pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le h5) ?_ 2)))
    refine (mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le).trans_eq ?_
    rw [← Real.exp_add]
    congr 1
    ring

theorem dim_eq_dimFlag (L : CmList A) (k : s.Comp) : (Φ.C k).Y.dim = dimFlag S.Dw := by
  rw [(GlobalTheory.ShFam.CmDim.cm_dim D A).2.2 N j S κ s Φ k, dimFlag, Formalism.DegreeFormula.dimFl, Formalism.DegreeFormula.dimFl, S.rank_eq,
    Fintype.card_congr L.ψ]

theorem growthOn_le (hP : Hypotheses2) (L : CmList A) {k : s.Comp} {Z : Comp s.Xo κ.c} (hZ : Over Φ k Z)
    {u : AllWt.Weight S.Dw} (hu : ∀ τ, Antitone (u τ)) (hn : (Φ.C k).Y.nef ((Φ.C k).Lw u)) :
    growthOn (unf s) Z (wtOf S.Dw u 0) ≤ ENNReal.ofReal ((Φ.C k).Y.inter fun _ => (Φ.C k).Lw u : ℝ) := by
  refine le_trans ?_ (GlobalTheory.T.nef_section_growth_le_intersection hP.q7 _ _ _ hn)
  rw [growthOn, ← dim_eq_dimFlag (Φ := Φ) L k]
  refine limsup_le_limsup (Eventually.of_forall fun τ => ENNReal.div_le_div_right (mul_le_mul_right
    (ENat.toENNReal_le.2 ?_) _) _)
  have e : τ • (Φ.C k).Lw u = (Φ.C k).Lw (τ • u) := by
    induction τ with
    | zero => simp [FlagCpt.Lw_zero]
    | succ n ih => rw [succ_nsmul, succ_nsmul, FlagCpt.Lw_add, ih]
  beta_reduce
  rw [nsmul_wtOf, smul_zero, e]
  exact GlobalTheory.T.cusp_form_rank_le_sections D A N j S κ s Φ k Z hZ (τ • u) fun a _ _ h => nsmul_le_nsmul_right (hu a h) τ

end Small

section Weights

variable {D : D7} (O : Setup D)

def wtQ (u : AllWt.Weight O.S.Dw) : D.what₂.Tau → Fin O.Y.N → ℚ := fun t i => u (O.L.ψ t) (Fin.cast O.S.rank_eq.symm i)

def wtY (u : AllWt.Weight O.S.Dw) : D.what₂.Tau → Fin O.Y.N → ℝ := wtR O.L u

theorem realWt_wtQ (u : AllWt.Weight O.S.Dw) : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.realWt O.Y (wtQ O u) = wtY O u :=
  funext₂ fun _ _ => Rat.cast_intCast _

variable {O}

theorem weightHyp (hj : O.N - O.j < O.j) {u : AllWt.Weight O.S.Dw} {g : ℝ} (h : WtGap u g) :
    WeightThresholdDefs.WeightHyp O.Y (wtY O u) g := by
  have hp := O.S.p_eq
  have hr := O.S.rank_eq
  have hi := O.indef
  have h1 : ∀ τ (a b : Fin O.N), a < b → wtR O.L u τ b < wtR O.L u τ a := fun τ a b hab =>
    Int.cast_lt.2 (h.2.1 _ (show Fin.cast O.S.rank_eq.symm a < Fin.cast O.S.rank_eq.symm b from hab))
  have h2 : ∀ τ (a b : Fin O.N), O.j ≤ (a : ℕ) → a ≠ b → g ≤ |wtR O.L u τ a - wtR O.L u τ b| := fun τ a b ha hab =>
    h.2.2 _ _ _ (hp.trans_le ha) fun e => hab (Fin.cast_injective _ e)
  refine ⟨h.1, h1, fun τ => ?_, fun τ a b ha => h2 τ a b ?_⟩
  · have a1 := h2 τ ⟨O.j, hi.2⟩ ⟨O.j - 1, by omega⟩ le_rfl (fun e => by have := congrArg Fin.val e; simp at this; omega)
    have a2 := h1 τ ⟨O.j - 1, by omega⟩ ⟨O.j, hi.2⟩ (by simp [Fin.lt_def]; omega)
    rw [abs_of_neg (sub_neg.2 a2), neg_sub] at a1
    exact a1
  · exact (if_neg (show ¬ O.j ≤ O.N - O.j by omega)).mp ha

theorem bigB0_eq (u : AllWt.Weight O.S.Dw) (g : ℝ) : WeightThresholdDefs.bigB0 O.Y (wtY O u) g = bndB u g := by
  have e := (reindex O.L.ψ O.S.rank_eq u).2.1
  rw [bndB, ← e, ← Fintype.card_congr O.L.ψ, D.what₂.card_Tau]
  rw [show ((O.S.Dw.p + O.S.Dw.q : ℕ) : ℝ) = (O.N : ℝ) from congrArg Nat.cast O.S.rank_eq]
  rfl

theorem four_le_bndB (u : AllWt.Weight O.S.Dw) {g : ℝ} (hg : 0 < g) : 4 ≤ bndB u g := by
  have h1 : (1 : ℝ) ≤ Fintype.card (Psi O.A.H) := by
    have := (GlobalTheory.ShFam.CmDim.cm_dim D O.A).2.1
    have : Nonempty (Psi O.A.H) := ⟨⟨D.host.φ₀, by rw [O.A.rt_eq, O.A.cmHost_rootComplex_eq_pm_sqrt]⟩⟩
    exact_mod_cast Fintype.card_pos
  have h2 : (1 : ℝ) ≤ ((O.S.Dw.p + O.S.Dw.q : ℕ) : ℝ) ^ 2 :=
    one_le_pow₀ (by exact_mod_cast (one_le_two.trans O.S.two_le).trans O.S.rank_eq.ge)
  have h3 : (1 : ℝ) ≤ 1 + (⨆ k : Psi O.A.H × Fin (O.S.Dw.p + O.S.Dw.q), |(u k.1 k.2 : ℝ)|) / g :=
    le_add_of_nonneg_right (div_nonneg (Real.iSup_nonneg fun _ => abs_nonneg _) hg.le)
  rw [bndB, mul_assoc, mul_assoc]
  exact le_mul_of_one_le_right (by norm_num) (one_le_mul_of_one_le_of_one_le h1 (one_le_mul_of_one_le_of_one_le h2 h3))

theorem one_le_rd (D : D7) : 1 ≤ D.host.rdE :=
  Real.one_le_rpow (by exact_mod_cast Int.one_le_abs (discr_ne_zero D.host.E)) (by positivity)

theorem errTerm_eq (hj : O.N - O.j < O.j) (u : AllWt.Weight O.S.Dw) {g : ℝ} (hg : 0 < g) :
    GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.errTerm O.Y (bndB u g) (wtY O u) = errX (ell D) u g := by
  obtain ⟨e1, -, e3, -⟩ := reindex O.L.ψ O.S.rank_eq u
  have hp := O.S.p_eq
  have hr := O.S.rank_eq
  have hq : WeightThresholdDefs.jS O.Y = O.S.Dw.q := by
    change min O.j (O.N - O.j) = _
    omega
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.errTerm, errX, l1, ← e1, ← e3, hq, ell,
    Real.log_mul (by linarith [four_le_bndB u hg]) (by linarith [one_le_rd D]), add_assoc (Real.log _)]
  rfl

open Classical in

theorem flagDeg_eq (u : AllWt.Weight O.S.Dw) : Formalism.DegreeFormula.flagDeg D.what₂.Tau O.Y.N (wtY O u) =
    (Nat.factorial (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N) : ℝ) *
      (((vdm u : ℤ) : ℝ) / (vdm (stdWt (Psi O.A.H) (O.S.Dw.p + O.S.Dw.q)) : ℤ)) := by
  rw [GlobalTheory.FlagPoly.flagDegFormula, ← (reindex O.L.ψ O.S.rank_eq u).2.2.2]
  rfl

theorem wtGap_std : WtGap (Dw := O.S.Dw) (stdWt _ _) 1 := by
  refine ⟨one_pos, strictAnti_stdWt, fun τ a b _ hab => ?_⟩
  have : (a : ℕ) ≠ b := Fin.val_ne_of_ne hab
  have h : (1 : ℤ) ≤ |stdWt (Psi O.A.H) (O.S.Dw.p + O.S.Dw.q) τ a - stdWt (Psi O.A.H) (O.S.Dw.p + O.S.Dw.q) τ b| :=
    Int.one_le_abs (by simp only [stdWt]; omega)
  exact_mod_cast h

end Weights

open Classical in

theorem slope_le (hX : HypothesesXH) (hP : Hypotheses2) (hH : HypothesesH) (hR : RegSt) {D : D7} {O : Setup D} (hC : O.Core)
    (hf : 2 < D.R.f * (O.N - 1)) (hj : O.N - O.j < O.j) {w : O.Y.Comp → ℝ} (hw : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.IsCompVol O.Y w)
    {u : AllWt.Weight O.S.Dw} {g : ℝ} (hu : WtGap u g) {k : O.s.Comp} {Z : Comp O.s.Xo O.κ.c} (hZ : Over O.Φ k Z) {sl : ℝ}
    (hs : Tendsto (GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.slopeAt O.Y (bndB u g) (wtY O u) k) (𝓝[>] (0 : ℚ)) (𝓝 sl)) :
    ((sl - 2 * (htCost O.κ.l (bndB u g) * l1 u) : ℝ) : EReal) ≤
      compVolSlope (unf O.s) (xiR D) 8 (mixVals O.s.Xo O.κ.c (bndB u g)) Z u := by
  have hpos : ∀ (u : AllWt.Weight O.S.Dw) g, WtGap u g → ∀ᶠ r : ℚ in 𝓝[>] 0, ∀ k : O.s.Comp,
      (O.Mb (bndB u g) (wtR O.L u) r k).SemiPos ∧ (O.Mb (bndB u g) (wtR O.L u) r k).NefFib := fun u g hu => by
    rw [← bigB0_eq]
    exact GlobalTheory.T.mbar_semipositive_nef_small_r hX hP hH hR D O hC hf (wtR O.L u) g (fun _ _ => ⟨_, (Rat.cast_intCast _).symm⟩) (weightHyp hj hu)
  have hdeg := fun (u : AllWt.Weight O.S.Dw) g (hu : WtGap u g) => hw.2.2 (wtQ O u) g
    (by rw [realWt_wtQ]; exact weightHyp hj hu) k
  simp only [realWt_wtQ, bigB0_eq, flagDeg_eq] at hdeg
  obtain ⟨x, P, hc⟩ := hC
  have hM : ∀ B u r, O.Y.Mbar B u r k = mbarOf P B u r k := fun B u r => congrFun (congrFun (congrFun (congrFun hc.Mb B) u) r) k
  have hgeo : ∀ B u r, O.Y.geoC (O.Y.Mbar B u r) k = (mbarOf P B u r k).deg := fun B u r => congrArg Adl.deg (hM B u r)
  have har : ∀ B u r, O.Y.arSelfC (O.Y.Mbar B u r) k = (mbarOf P B u r k).arTop := fun B u r => congrArg Adl.arTop (hM B u r)
  replace hdeg := fun u g hu => (hdeg u g hu).congr fun r => hgeo _ _ r
  rw [hc.Mb] at hpos
  have hv0 : (0 : ℝ) < (vdm (stdWt (Psi O.A.H) (O.S.Dw.p + O.S.Dw.q)) : ℤ) := Int.cast_pos.2 (vdm_pos strictAnti_stdWt)
  have hv : (0 : ℝ) < (vdm u : ℤ) := Int.cast_pos.2 (vdm_pos hu.2.1)
  have hfac : (0 : ℝ) < Nat.factorial (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N) := Nat.cast_pos.2 (Nat.factorial_pos _)
  have htop : topDeg (unf O.s) Z u ≤ w k * ((Nat.factorial (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N) : ℝ) *
      (((vdm u : ℤ) : ℝ) / (vdm (stdWt (Psi O.A.H) (O.S.Dw.p + O.S.Dw.q)) : ℤ))) := by
    obtain ⟨a1, a2⟩ := GlobalTheory.T.mbar_degree_tendsto_intersection D O.A O.N O.j O.S O.κ O.s O.Φ O.L x P (bndB (Dw := O.S.Dw) (stdWt _ _) 1) (stdWt _ _) k
    have a3 := tendsto_nhds_unique a1 (hdeg _ _ wtGap_std)
    have a4 := growthOn_le hP O.L hZ (fun τ => (strictAnti_stdWt τ).antitone)
      (a2 ((hpos _ _ wtGap_std).mono fun r h => GlobalTheory.T.nef_of_semipositive_fibrewise hP hH _ _ _ _ (h k).1 (h k).2))
    rw [a3, div_self hv0.ne', mul_one] at a4
    have a5 := ENNReal.toReal_le_of_le_ofReal (mul_pos (hw.1 k) hfac).le a4
    rw [topDeg, vZero, div_mul_eq_mul_div, mul_div_assoc, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right a5 (div_pos hv hv0).le
  obtain ⟨C, hinf⟩ := GlobalTheory.T.infinite_norm_sq_exponential_bound hP hH hR D O x P hc hf u hu.2.1 (bndB u g) (by linarith [four_le_bndB u hu.1]) k
  obtain ⟨cX, hcX, hfin⟩ := GlobalTheory.T.finite_norm_bounded_mbar hP hH D O.A O.N O.j O.S O.κ O.s O.Φ O.L x P (bndB u g) u k
  obtain ⟨hL1, hL2, -⟩ := GlobalTheory.T.height_log_sum_and_prime_bound D O.A O.κ (bndB u g)
  have hd : (0 : ℝ) < Module.finrank ℚ D.what₂.LL := Nat.cast_pos.2 Module.finrank_pos
  refine le_volSlope_of_tendsto (C := C + (∑ᶠ v, cX v) / Module.finrank ℚ D.what₂.LL) (Dm := WeightThresholdDefs.dimY O.Y)
    (ar := fun r => (mbarOf P (bndB u g) (wtR O.L u) r k).arTop) htop (mul_pos (hw.1 k) (mul_pos hfac (div_pos hv hv0)))
    (hdeg u g hu) (hs.congr fun r => congrArg₂ (fun a b => a / (((WeightThresholdDefs.dimY O.Y : ℝ) + 1) * b)) (har _ _ r) (hgeo _ _ r)) ?_
  filter_upwards [hpos u g hu, hinf, self_mem_nhdsWithin] with r h1 h2 hr t
  have hr : 0 < r := hr
  have s1 : (Function.support fun v => (r : ℝ) * cX v).Finite := hcX.subset fun v h => right_ne_zero_of_mul h
  have s2 : (Function.support fun v => 2 * (htLog O.κ (bndB u g) v * l1 u)).Finite :=
    hL1.subset fun v h => left_ne_zero_of_mul (right_ne_zero_of_mul h)
  have h3 := GlobalTheory.T.arithmetic_volume_le_count hP.p2 hP.p4 hH.deg _ _ _ _ (h1 k).1 (h1 k).2 (t - C * r)
    (fun v => -(r * cX v + 2 * (htLog O.κ (bndB u g) v * l1 u)))
    ((s1.union s2).subset fun v h => Function.support_add _ _ (neg_ne_zero.1 h)) 8 (by norm_num)
  rw [finsum_neg_distrib, finsum_add_distrib s1 s2, ← mul_finsum, ← mul_finsum, ← finsum_mul, hL2] at h3
  have e1 : Module.finrank ℚ D.what₂.LL = Module.finrank ℚ O.κ.c.F :=
    (O.κ.e.toRingHom.toRatAlgHom.toLinearMap.finrank_le_finrank_of_injective O.κ.e.injective).antisymm
      (O.κ.e.symm.toRingHom.toRatAlgHom.toLinearMap.finrank_le_finrank_of_injective O.κ.e.symm.injective)
  refine le_of_eq_of_le (congrArg ENNReal.ofReal ?_) (h3.trans ?_)
  · rw [O.dim_eq k]
    congr 2
    field_simp
    ring
  · rw [compVol, ← e1, ← dim_eq_dimFlag (Φ := O.Φ) O.L k]
    exact countVol_mono_pos _ _ (by norm_num) fun τ hτ => encard_small_le hP hH hZ x (fun a => (hu.2.1 a).antitone) _ t
      (GlobalTheory.T.mbar_sections_cuspidal D O.A O.N O.j O.S O.κ O.s O.Φ O.L x P _ u r hr k τ hτ) (h2 τ hτ) (hfin r hr τ hτ)

theorem meanAll (hX : HypothesesXH) (hP : Hypotheses2) (hH : HypothesesH) (hR : RegSt) {D : D7} {O : Setup D} (hC : O.Core)
    (hf : 2 < D.R.f * (O.N - 1)) (hj : O.N - O.j < O.j) (hb : FewBad O.Y) {C : ℝ}
    (hV : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.VolEq O.Y) (hS : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.SlopeMean O.Y C) :
    MeanAll (unf O.s) (xiR D) (ell D) (C + 88) := fun u g hu => by
  obtain ⟨w, hw, -⟩ := hV
  obtain ⟨sl, h1, -, h2⟩ := hS (wtQ O u) g (by rw [realWt_wtQ]; exact weightHyp hj hu)
  rw [realWt_wtQ, bigB0_eq (O := O) u g] at h1 h2
  rw [errTerm_eq hj u hu.1] at h2
  obtain ⟨q, hq⟩ := GlobalTheory.T.flag_components_biject_moduli_components D O.A O.N O.j O.S O.κ O.s O.Φ
  refine ⟨fun Z => sl (q.symm Z) - 2 * (htCost O.κ.l (bndB u g) * l1 u), fun Z => ?_, ?_⟩
  · exact slope_le hX hP hH hR hC hf hj hw hu (by simpa using hq (q.symm Z)) (h1 (q.symm Z))
  · have hc : (0 : ℝ) < Fintype.card O.Y.Comp := Nat.cast_pos.2 Fintype.card_pos
    let q' : O.Y.Comp ≃ Comp O.s.Xo O.κ.c := q
    rw [← finsum_comp_equiv q', ← Nat.card_congr q', finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
    have e : ∀ k : O.Y.Comp, q.symm (q' k) = k := q.symm_apply_apply
    simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [sub_div, mul_div_cancel_left₀ _ hc.ne']
    have h4 := four_le_bndB u hu.1
    have h5 := (BudgetPf.htCost_le D O.κ.l (bndB u g) (by linarith) hb).2
    have h6 : 1 ≤ Real.log (bndB u g) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_d9]
    have hl : 0 ≤ l1 u := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h7 : (Real.log (bndB u g) + ell D) * l1 u ≤ errX (ell D) u g :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun τ _ => sub_nonneg.2 (by
        rcases isEmpty_or_nonempty (Fin (O.S.Dw.p + O.S.Dw.q)) with h | ⟨⟨i⟩⟩
        · simp
        · exact (ciInf_le (Set.finite_range _).bddBelow i).trans (le_ciSup (f := fun i => (u τ i : ℝ)) (Set.finite_range _).bddAbove i))))
    have h8 : htCost O.κ.l (bndB u g) ≤ 44 * (Real.log (bndB u g) + ell D) := by
      rw [ell]
      linarith [abs_nonneg (dlogL D 1), D.host.log_rdE_nonneg']
    have h9 := mul_le_mul_of_nonneg_right h8 hl
    rw [GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.compMean] at h2
    linarith

theorem srcSt_of_slopeSt : HypothesesXH → Hypotheses2 → HypothesesH → RegSt → SlopeSt → SrcSt := by
  rintro hX hP hH hR ⟨C, hC, h⟩
  refine ⟨C + 88, by linarith, fun D A N j S κ s hj hN hf hb => ?_⟩
  obtain ⟨L⟩ := (GlobalTheory.ShFam.CmDim.cm_dim D A).1
  obtain ⟨Φ⟩ := GlobalTheory.ShFam.KitEx.flag_nonempty s
  obtain ⟨ng, k, adm, met, -, hc⟩ := (GlobalTheory.Mean4.exists_setup_core D).2 A N j ⟨by omega, hN⟩ S κ s L Φ
    fun p _ _ => (GlobalTheory.WittFracComplex.nonempty_ringHom_complex p).some
  exact meanAll hX hP hH hR hc hf hj hb (h D _ hc hf hb).1 (h D _ hc hf hb).2

end GlobalTheory.CovHt.Link

end
