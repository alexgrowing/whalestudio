import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg.LawBddPf

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}

theorem nrm_add_le (Z : Comp Xo c) (G : WTZ E) (x y : AC Z) (P : Om Z →+* ℂ) :
    nrmC fn (yP Z) G (x + y) P ≤ nrmC fn (yP Z) G x P + nrmC fn (yP Z) G y P := by
  unfold nrmC
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => by positivity)
  have hc : (x + y).coeff G = x.coeff G + y.coeff G := by rfl
  rw [hc, map_add]
  exact norm_add_le _ _

theorem nrm_smul (Z : Comp Xo c) (G : WTZ E) (a : Om Z) (x : AC Z) (P : Om Z →+* ℂ) :
    nrmC fn (yP Z) G (a • x) P = ‖P a‖ * nrmC fn (yP Z) G x P := by
  unfold nrmC
  have hc : (a • x).coeff G = a * x.coeff G := by rfl
  rw [hc, map_mul, norm_mul, mul_assoc]

theorem bdd_gen [Fintype (Comp Xo c)] (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (sg : c.F →+* ℂ) :
    BddAbove (Set.range fun p : (Σ Z : Comp Xo c, ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) sg) =>
      nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) := by
  unfold ValAtCx at hcx
  obtain ⟨B, hBd⟩ := hB sg
  refine ⟨B, ?_⟩
  rintro _ ⟨⟨Z, P⟩, rfl⟩
  have hP : (P : Om Z →+* ℂ).comp (algebraMap c.F (Om Z)) = sg := P.2
  have key : ∀ (σ : c.F →+* ℂ), σ = sg → ∀ y : FrPt Xo c (CAt σ),
      cabs (evR Xo c f y) * ∏ i, |fn σ y i|⁻¹ ^ ex Dw a n i ≤ B := by
    rintro σ rfl y
    exact hBd ⟨y, rfl⟩
  have hex : ∀ i, exZ Dw (wtZ a n) i = (ex Dw a n i : ℤ) := by
    intro i
    unfold exZ wtZ ex
    cases i <;> rfl
  have hco : (valC h a n f Z).coeff (wtZ a n) = evC h Z f := by
    unfold valC
    simp
  show nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) (P : Om Z →+* ℂ) ≤ B
  unfold nrmC
  rw [hco, hcx Z P a n f hS]
  have hs : sgOf (P : Om Z →+* ℂ) = sg := hP
  refine Eq.trans_le ?_ (key _ hs (yP Z P))
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hex i, zpow_neg, zpow_natCast, inv_pow]

theorem bdd_span (G : WTZ E) (sg : c.F →+* ℂ) (S : Set (∀ Z : Comp Xo c, AC Z))
    (hS : ∀ f ∈ S, BddAbove (Set.range fun p : (Σ Z : Comp Xo c, ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) sg) =>
      nrmC fn (yP p.1) G (f p.1) p.2)) (f : ∀ Z : Comp Xo c, AC Z)
    (hf : f ∈ (letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun Z => Algebra.toModule
      Submodule.span (𝓞 c.F) S)) :
    BddAbove (Set.range fun p : (Σ Z : Comp Xo c, ReciprocityTheory.ChartRestriction.G.T0.PT (Ω := Om Z) sg) =>
      nrmC fn (yP p.1) G (f p.1) p.2) := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    refine ⟨0, ?_⟩
    rintro _ ⟨⟨Z, P⟩, rfl⟩
    have h0 := nrm_smul (fn := fn) (yP := yP) Z G (0 : Om Z) (0 : AC Z) (P : Om Z →+* ℂ)
    rw [zero_smul, map_zero, norm_zero, zero_mul] at h0
    exact h0.le
  | add x y _ _ hx hy =>
    obtain ⟨A, hA⟩ := hx
    obtain ⟨B, hB⟩ := hy
    refine ⟨A + B, ?_⟩
    rintro _ ⟨⟨Z, P⟩, rfl⟩
    exact (nrm_add_le Z G _ _ _).trans
      (add_le_add (hA ⟨⟨Z, P⟩, rfl⟩) (hB ⟨⟨Z, P⟩, rfl⟩))
  | smul a x _ hx =>
    obtain ⟨A, hA⟩ := hx
    refine ⟨‖sg (a : c.F)‖ * A, ?_⟩
    rintro _ ⟨⟨Z, P⟩, rfl⟩
    have hP : (P : Om Z →+* ℂ).comp (algebraMap c.F (Om Z)) = sg := P.2
    have hsm : (a • x) Z = (algebraMap c.F (Om Z) (a : c.F)) • x Z := by
      rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]
      congr 1
    have hv : (P : Om Z →+* ℂ) (algebraMap c.F (Om Z) (a : c.F)) = sg (a : c.F) := by
      exact RingHom.congr_fun hP _
    show nrmC fn (yP Z) G ((a • x) Z) (P : Om Z →+* ℂ) ≤ _
    rw [hsm, nrm_smul, hv]
    exact mul_le_mul_of_nonneg_left (hA ⟨⟨Z, P⟩, rfl⟩) (norm_nonneg _)

end

theorem lawBdd_dataOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)) (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E) (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c) (nu : HeightOneSpectrum (𝓞 c.F) → ℝ) (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ) (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ), ValAtCx h yP → (∀ k, wR k ∈ sec Xo c uL.1 uL.2 ∧ SupBdd Xo c fn uL.1 uL.2 (wR k)) → (∀ k, thpR k ∈ sec Xo c uF.1 uF.2 ∧ SupBdd Xo c fn uF.1 uF.2 (thpR k)) → (etR ∈ sec Xo c uet.1 uet.2 ∧ SupBdd Xo c fn uet.1 uet.2 etR) → (ta1R ∈ sec Xo c uta1.1 uta1.2 ∧ SupBdd Xo c fn uta1.1 uta1.2 ta1R) → (ta2R ∈ sec Xo c uta2.1 uta2.2 ∧ SupBdd Xo c fn uta2.1 uta2.2 ta2R) → wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2 → wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2) → wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2 → LawBdd (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) := by
  intro E _ _ _ H Dw l Xo c _ h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hcx hw hth het hta1 hta2 e1 e2 e3
  unfold LawBdd
  set D := dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r with hD
  intro sg G F
  rintro (⟨hF, rfl⟩ | ⟨hF, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · refine bdd_span _ sg _ ?_ F hF
    rintro _ ⟨k, rfl⟩
    exact bdd_gen hcx (hw k).1 (hw k).2 sg
  · refine bdd_span _ sg _ ?_ F hF
    rintro _ ⟨k, rfl⟩
    exact bdd_gen hcx (hth k).1 (hth k).2 sg
  · have hG : D.n1 • D.wde = wtZ uet.1 uet.2 := by rw [hD]; exact e1.symm
    rw [hG]
    exact bdd_gen hcx het.1 het.2 sg
  · have hG : 2 • D.G1 = wtZ uta1.1 uta1.2 := by rw [hD]; exact e2.symm
    rw [hG]
    exact bdd_gen hcx hta1.1 hta1.2 sg
  · have hG : D.G2 = wtZ uta2.1 uta2.2 := by rw [hD]; exact e3.symm
    rw [hG]
    exact bdd_gen hcx hta2.1 hta2.2 sg

end GlobalTheory.Reg.LawBddPf
