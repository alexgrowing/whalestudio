import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.PTNonempty

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

variable (Xo c) in

def supR (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : Rul Xo c) : ℝ :=
  supAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f

variable (Xo c) in

def SupBdd (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    Prop :=
  ∀ σ, BddAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f

variable (Xo c) in

def PTNe : Prop := ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), (PT (Ω := Om Z) σ).Nonempty

theorem ptNe_of_fnFG (hfg : FnFG Xo c) : PTNe Xo c := fun Z σ => exists_embedding_over (hfg Z) σ

def ValAtCx (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ‖P (evC h Z f)‖ = cabs (evR Xo c f (yP Z P))

def NZSome (h : GenFrEx Xo c) (f : Rul Xo c) : Prop := ∃ Z, evC h Z f ≠ 0

section Pf

variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}

theorem meanK_mono' {K : Type} [Field K] [NumberField K] {F G : (K →+* ℂ) → ℝ} (hFG : ∀ sg, F sg ≤ G sg) :
    meanK F ≤ meanK G := by
  unfold meanK
  gcongr with sg _
  exact hFG sg

theorem exZ_wtZ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (i : Ix Dw) : exZ Dw (wtZ a n) i = (ex Dw a n i : ℤ) := by
  cases i <;> rfl

theorem nrmC_valC_le (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (Z : Comp Xo c) (P : Om Z →+* ℂ) :
    nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P ≤ supR Xo c fn (sgOf P) a n f := by
  have hb := hB (sgOf P)
  unfold BddAt at hb
  have hle := le_ciSup hb (yP Z P)
  have hc : (valC h a n f Z).coeff (wtZ a n) = evC h Z f := by
    unfold valC
    simp
  have heq : nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P =
      ptNorm (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (sgOf P) (fn (sgOf P)) (ex Dw a n) f (yP Z P) := by
    unfold nrmC ptNorm
    rw [hc, hcx Z P a n f hS]
    simp only [exZ_wtZ, zpow_neg, zpow_natCast, inv_pow] <;> rfl
  rw [heq]
  exact hle

theorem log_supN_le (hfn : FnNe Xo c fn) (hPT : PTNe Xo c) (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul Xo c} (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (hN : NZSome h f) (σ : c.F →+* ℂ) :
    Real.log (⨆ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ), nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) ≤
      Real.log (supR Xo c fn σ a n f) := by
  have hbd : ∀ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ),
      nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2 ≤ supR Xo c fn σ a n f := by
    rintro ⟨Z, P, hP⟩
    have hσ : sgOf P = σ := hP
    have key := nrmC_valC_le (h := h) (yP := yP) hcx hS hB Z P
    rw [hσ] at key
    exact key
  obtain ⟨Z0, hZ0⟩ := hN
  obtain ⟨P0, hP0⟩ := hPT Z0 σ
  have hpos : 0 < nrmC fn (yP Z0) (wtZ a n) (valC h a n f Z0) P0 := by
    have hc : (valC h a n f Z0).coeff (wtZ a n) = evC h Z0 f := by
      unfold valC
      simp
    unfold nrmC
    rw [hc]
    apply mul_pos
    · exact norm_pos_iff.mpr ((map_ne_zero P0).mpr hZ0)
    · apply Finset.prod_pos
      intro i _
      exact zpow_pos (abs_pos.mpr (hfn _ _ i)) _
  have hne : Nonempty (Σ Z : Comp Xo c, PT (Ω := Om Z) σ) := ⟨⟨Z0, P0, hP0⟩⟩
  have hB' : BddAbove (Set.range fun p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ) =>
      nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) := ⟨_, Set.forall_mem_range.mpr hbd⟩
  apply Real.log_le_log
  · exact lt_of_lt_of_le hpos (le_ciSup hB' ⟨Z0, P0, hP0⟩)
  · exact ciSup_le hbd

end Pf

theorem htSup_of (h : GenFrEx Xo c)
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
    (hfn : FnNe Xo c fn) (hfg : FnFG Xo c) (hcx : ValAtCx h yP)
    (huta1 : wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2))
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hwS : ∀ k, wR k ∈ sec Xo c uL.1 uL.2) (hwB : ∀ k, SupBdd Xo c fn uL.1 uL.2 (wR k)) (hwN : ∀ k, NZSome h (wR k))
    (hpS : ∀ k, thpR k ∈ sec Xo c uF.1 uF.2) (hpB : ∀ k, SupBdd Xo c fn uF.1 uF.2 (thpR k))
    (hpN : ∀ k, NZSome h (thpR k))
    (h1S : ta1R ∈ sec Xo c uta1.1 uta1.2) (h1B : SupBdd Xo c fn uta1.1 uta1.2 ta1R) (h1N : NZSome h ta1R)
    (h2S : ta2R ∈ sec Xo c uta2.1 uta2.2) (h2B : SupBdd Xo c fn uta2.1 uta2.2 ta2R) (h2N : NZSome h ta2R)
    (mx : (c.F →+* ℂ) → ℝ) (hmx : ∀ σ k, Real.log (supR Xo c fn σ uL.1 uL.2 (wR k)) ≤ mx σ)
    (hmxm : meanK mx ≤ Gc * wsize (wtZ uL.1 uL.2))
    (hth : ∀ k, meanK (fun σ => Real.log (supR Xo c fn σ uF.1 uF.2 (thpR k))) ≤ Gc * wsize (wtZ uF.1 uF.2))
    (hta1 : meanK (fun σ => Real.log (supR Xo c fn σ uta1.1 uta1.2 ta1R)) ≤ 2 * PI4 * Dd * wsize (wtZ uL.1 uL.2))
    (hta2 : meanK (fun σ => Real.log (supR Xo c fn σ uta2.1 uta2.2 ta2R)) ≤ PI4 * Dd * wsize (wtZ uL.1 uL.2)) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip
      wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtSup := by
  have hPT : PTNe Xo c := ptNe_of_fnFG hfg
  unfold Data.HtSup
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans (meanK_mono' fun sg => ?_) hmxm
    exact ciSup_le fun j => (log_supN_le hfn hPT hcx (hwS j) (hwB j) (hwN j) sg).trans (hmx sg j)
  · intro k
    refine le_trans (meanK_mono' fun sg => ?_) (hth k)
    exact log_supN_le hfn hPT hcx (hpS k) (hpB k) (hpN k) sg
  · refine le_trans (meanK_mono' fun sg => ?_) hta1
    have e : (2 : ℕ) • (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR
        MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).G1 = wtZ uta1.1 uta1.2 := by
      rw [huta1] <;> rfl
    rw [e]
    exact log_supN_le hfn hPT hcx h1S h1B h1N sg
  · refine le_trans (meanK_mono' fun sg => ?_) hta2
    have e : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR
        MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).G2 = wtZ uta2.1 uta2.2 := by
      rw [huta2] <;> rfl
    rw [e]
    exact log_supN_le hfn hPT hcx h2S h2B h2N sg

end Formalism.L2.Pj
