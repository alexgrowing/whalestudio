import Formalism.LocalToGlobal.ProjectiveLattices.CompTie
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

variable (Xo c) in

def CombAlg {n : ℕ} (ws : Fin n → Rul Xo c) (et : Rul Xo c) (nu : HeightOneSpectrum (𝓞 c.F) → ℝ) (c' : ℝ) :
    Prop :=
  ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v et ∧
    (v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v et)

variable (c) in

def nuOf (nus : HeightOneSpectrum (𝓞 c.F) → ℝ) (la : HeightOneSpectrum (𝓞 c.F)) : ℝ :=
  (ramOverZ la : ℝ) * nus la

variable (c) in

def NumericalH1Condition (nus : HeightOneSpectrum (𝓞 c.F) → ℝ) (P s : ℝ) : Prop :=
  (∀ la, 0 ≤ nus la) ∧ (Function.support nus).Finite ∧
    (∑ᶠ la, (ramOverZ la : ℝ) * nus la * logNorm la) / (Module.finrank ℚ c.F : ℝ) ≤ P * s

def OrdTieOn (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)) (la : HeightOneSpectrum (𝓞 c.F)),
    IsNormDiscrete v → IsOver (K := c.F) v la →
    ∃ y : PtV Xo c cls (PY la) (lies la) la,
      (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
        (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) =
          (((ramIdx (K := c.F) v la : ℤ) : ℝ) : EReal) * vAtV y f) ∧
      (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f = 0 →
        (∃ g ∈ sec Xo c a n, evC h Z g ≠ 0) → vAtV y f = ⊤)

theorem OrdTieOn.ordTie {h : GenFrEx Xo c} {δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ}
    {cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop} {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (H : OrdTieOn h δ cls PY lies) : OrdTie h δ cls PY lies := fun Z v la hv ho =>
  let ⟨y, hy, _⟩ := H Z v la hv ho
  ⟨y, hy⟩

theorem one_le_ramIdx {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {v : AddValuation Ω (WithTop ℤ)} {la : HeightOneSpectrum (𝓞 K)} (hv : IsNormDiscrete v)
    (ho : IsOver (K := K) v la) : 1 ≤ ramIdx (K := K) v la := by
  unfold ramIdx
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
  have hK : ((a : K)) ≠ 0 := by exact_mod_cast ha0
  have hne : v (algebraMap K Ω (a : K)) ≠ ⊤ := hv.1 _ ((map_ne_zero _).2 hK)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
  refine le_csInf ⟨n, a, ha, ha0, hn.symm⟩ ?_
  rintro m ⟨b, hb, _, hbm⟩
  have h1 := (ho b).2 hb
  rw [hbm] at h1
  have h0 : (0 : ℤ) < m := by exact_mod_cast h1
  omega

section H1

variable [Fintype (Comp Xo c)] (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nus : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

theorem height_H1_of_data {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (hreg : regular₂ Xo c U)
    (hdL : Dom uL.1 uL.2) (hdE : Dom uet.1 uet.2) (hw : ∀ k, wR k ∈ cusp Xo c U uL.1 uL.2)
    (he : etR ∈ cusp Xo c U uet.1 uet.2) (hnz : NoCommonZero Xo c wR) (hetZ : NZAt h etR)
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2) (hcc : 0 ≤ cc)
    (hcomb : CombAlg Xo c wR etR (nuOf c nus) (cc / (2 * (i : ℝ))))
    (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop) (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop)
    (htie : OrdTieOn h δ cls PY lies) (hnu : NumericalH1Condition c nus PN (wsize (wtZ uL.1 uL.2))) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R
      (nuOf c nus) ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).FinitePlaceHyp := by
  classical
  refine ⟨fun la => mul_nonneg (Nat.cast_nonneg _) (hnu.1 la), ?_, hnu.2.2, ?_⟩
  · refine hnu.2.1.subset fun la hla => ?_
    rw [Function.mem_support] at hla ⊢
    intro h0
    apply hla
    show (ramOverZ la : ℝ) * nus la = 0
    rw [h0, mul_zero]
  · intro Z v la hadm hover
    show ((⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0},
        ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) : ℤ) : ℝ) ≤
      (ramIdx (K := c.F) v la : ℝ) * nuOf c nus la +
        cc / (2 * (i : ℝ)) * (ordC (δ Z v) v ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) : ℝ)
    rw [← huet]
    have hv : IsNormDiscrete v := hadm.1
    obtain ⟨y, hty, hzero⟩ := htie Z v la hv hover
    obtain ⟨T', io, e, ho, z, _, eta, _, hq⟩ := y.2
    let y1 : PtV Xo c (trivialClassCondition Xo c) Unit (fun _ _ _ _ => True) la := PtV.mk la ho z trivial () trivial
    have hyv : vAtV y1 = vAtV y := funext fun g => by
      show y1.1.1 g = y.1.1 g
      rw [hq]
      rfl
    have hc' : (0 : ℝ) ≤ cc / (2 * (i : ℝ)) := div_nonneg hcc (by positivity)
    have hR := (hreg.1.2 ⟨uL, hdL⟩ ⟨uet, hdE⟩ (N + 1) (fun k => ⟨wR k, hw k⟩) ⟨etR, he⟩ (nuOf c nus)
      (cc / (2 * (i : ℝ))) hc' hnz (fun la' y0 => hcomb la' y0.1 y0.2)).1 la ⟨vAtV y1, y1, rfl⟩
    have hR' : 0 ≤ vAtV y etR ∧ (vAtV y etR ≠ ⊤ →
        (⨅ k, vAtV y (wR k)) ≤ ((nuOf c nus la : ℝ) : EReal) + ((cc / (2 * (i : ℝ)) : ℝ) : EReal) * vAtV y etR) := by
      rw [← hyv]
      exact hR
    have he1 : 1 ≤ ramIdx (K := c.F) v la := one_le_ramIdx hv hover
    have hepos : (0 : ℝ) < (ramIdx (K := c.F) v la : ℝ) := by
      exact_mod_cast (show (0 : ℤ) < ramIdx (K := c.F) v la by omega)
    have hE := (hty uet.1 uet.2 etR (cusp_le_sec Xo c U _ _ he) (hetZ Z))
    have htopE : vAtV y etR ≠ ⊤ := by
      intro htop
      rw [htop, EReal.mul_top_of_pos (by exact_mod_cast hepos)] at hE
      exact EReal.coe_ne_top _ hE
    obtain ⟨x, hx⟩ : ∃ x : ℝ, vAtV y etR = (x : EReal) :=
      ⟨_, (EReal.coe_toReal htopE (vAtV_ne_bot y etR)).symm⟩
    have hB := hR'.2 htopE
    rw [hx, ← EReal.coe_mul, ← EReal.coe_add] at hB
    rw [hx, ← EReal.coe_mul, EReal.coe_eq_coe_iff] at hE
    obtain ⟨k0, hk0⟩ : ∃ k0, vAtV y (wR k0) = ⨅ k, vAtV y (wR k) := exists_eq_ciInf_of_finite
    rw [← hk0] at hB
    have hk0Z : evC h Z (wR k0) ≠ 0 := by
      intro h0
      rw [hzero uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hw k0)) h0
        ⟨wR (jc Z), cusp_le_sec Xo c U _ _ (hw (jc Z)), hwb Z⟩] at hB
      exact absurd hB (not_le.2 (EReal.coe_lt_top _))
    have hW := hty uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hw k0)) hk0Z
    have htopW : vAtV y (wR k0) ≠ ⊤ := fun ht => by
      rw [ht] at hB
      exact absurd hB (not_le.2 (EReal.coe_lt_top _))
    obtain ⟨t, ht⟩ : ∃ t : ℝ, vAtV y (wR k0) = (t : EReal) :=
      ⟨_, (EReal.coe_toReal htopW (vAtV_ne_bot y _)).symm⟩
    rw [ht, ← EReal.coe_mul, EReal.coe_eq_coe_iff] at hW
    rw [ht, EReal.coe_le_coe_iff] at hB
    calc ((⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0},
          ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) : ℤ) : ℝ)
        ≤ (ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) : ℝ) :=
          Int.cast_le.2 (ciInf_le (f := fun j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0} =>
            ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z)) (Set.finite_range _).bddBelow
            ⟨k0, valC_ne_zero (a := uL.1) (n := uL.2) hk0Z⟩)
      _ = (ramIdx (K := c.F) v la : ℝ) * t := hW
      _ ≤ (ramIdx (K := c.F) v la : ℝ) * (nuOf c nus la + cc / (2 * (i : ℝ)) * x) :=
          mul_le_mul_of_nonneg_left hB hepos.le
      _ = (ramIdx (K := c.F) v la : ℝ) * nuOf c nus la +
            cc / (2 * (i : ℝ)) * ((ramIdx (K := c.F) v la : ℝ) * x) := by ring
      _ = _ := by rw [← hE]

end H1

end Formalism.L2.Pj
