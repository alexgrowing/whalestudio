import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.CechPic GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nsq_pow_addFn_const {σ : k →+* ℂ} {B : LB X} (φ : Weight p σ B) (c : ℝ) (m : ℕ)
    (s : (lbPow B m).ι → CxPts p σ → ℂ) (y : CxPts p σ) :
    ((φ.addFn fun _ => c).pow m).nsq s y = (φ.pow m).nsq s y * Real.exp (-(m * c)) := by
  simp only [Weight.nsq]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  simp only [Weight.addFn]
  push_cast
  ring

theorem isometric_pull_id (L : HermLB p) : L.Isometric (L.pull (𝟙 X) (Category.id_comp p)) := by
  have hid {σ : k →+* ℂ} (y : CxPts p σ) : PtsOver.map (𝟙 X) (Category.id_comp p) _ y = y :=
    Subtype.ext (Category.comp_id _)
  refine HermLB.isometric_of_chart (fun c _ => c) (fun c y hy => Set.mem_iInter.2 fun _ => hy)
    (fun z c c' hc hc' => ?_) fun σ c y _ => ?_
  · refine Eq.trans ?_ (gm_pull_g L.B (𝟙 X) (𝟙 X) z (fun _ => c) (fun _ => c')
      (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm
    rw [Category.comp_id]
  · exact ((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).trans (congrArg _ (hid y))

theorem recursion_pull_id [IsLocallyNoetherian X] {D : ℕ} (hX : IsArithVar p D) (hD : 1 ≤ D) {L : HermLB p} {h : X → ℝ}
    (H : L.IsArithHeight h) (m : ℕ) {q : X ⟶ Sp k} (hq : 𝟙 X ≫ p = q)
    (r : ((L.pull (𝟙 X) hq).pow m).B.ι → X.functionFieldˣ) (hr : IsRatSec ((L.pull (𝟙 X) hq).pow m).B r) :
    (L.pull (𝟙 X) hq).ArchIntegrable ((L.pull (𝟙 X) hq).pow m) D hr ∧
      (m : ℝ) * h (genericPoint X) = ∑ᶠ z, ((((L.pull (𝟙 X) hq).pow m).div hr).mult z : ℝ) * h z -
        (L.pull (𝟙 X) hq).archInt ((L.pull (𝟙 X) hq).pow m) D hr := by
  subst hq
  have e := H.recursion X (𝟙 X) hX.charZero D hD hX.dim_eq m r hr
  simpa using e

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem height_add_mul_gdeg_nonneg_of_smallSec : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → ∀ (C : HermLB p) (h : X → ℝ), C.SemiPos D → C.IsArithHeight h → (∀ z, z ≠ genericPoint X → 0 ≤ h z) → ∀ (m : ℕ) (u : ℝ), 0 < m → 0 ≤ u → (∃ s ∈ ((C.shift (fun _ => u) fun _ => rfl).pow m).smallSec, s ≠ 0) → 0 ≤ h (genericPoint X) + u * gdeg C D := by
  intro HC k _ X _ p D hX hD C h hSP H hnn m u hm hu hex
  obtain ⟨s, hs, hs0⟩ := hex
  have := hX.isLocallyNoetherian
  have := hX.finite_emb
  have hiso := isometric_pull_id C
  set C' := C.pull (𝟙 X) (Category.id_comp p) with hC'
  let s' : (C.pow m).B.Sec := s
  have hg : genericPoint X ∈ nonzeroLocus s' := (sec_ne_zero_iff s').1 hs0
  obtain ⟨r', hr', hdiv, hlog⟩ := (hiso.pow m).exists_isRatSec (isRatSec_ratOfSec s' hg)
  obtain ⟨hI, hrec⟩ := recursion_pull_id hX hD H m (Category.id_comp p) r' hr'

  have hsum : 0 ≤ ∑ᶠ z, (((C'.pow m).div hr').mult z : ℝ) * h z := by
    refine finsum_nonneg fun z => ?_
    rw [hdiv]
    by_cases hz : ((C.pow m).div (isRatSec_ratOfSec s' hg)).mult z = 0
    · simp [hz]
    · exact mul_nonneg (by exact_mod_cast mult_divOfSec_nonneg z)
        (hnn z fun e => CartierDiv.genericPoint_notMem_supp _ (e ▸ CartierDiv.mem_supp_of_mult_ne_zero hz))

  have hneg (σ : k →+* ℂ) : (C.φ σ).chernPart D (-1) = 0 := Weight.chernPart_neg_eq_zero (C.cInf σ) (hSP σ)
  have hfin (σ : k →+* ℂ) : IsFiniteMeasure ((C.φ σ).chernPart D 1) := by
    have hu1 : ∀ σ (y : CxPts p σ), CInfAt (fun _ : CxPts p σ => (1 : ℝ)) y := fun σ y => cInfAt_const 1 y
    have hc1 : ∀ σ σ' : k →+* ℂ, (Weight.ofFun (fun _ : CxPts p σ => (1 : ℝ))).IsConj
        (Weight.ofFun (fun _ : CxPts p σ' => (1 : ℝ))) := fun _ _ _ _ _ _ _ => rfl
    obtain ⟨Φ, hΦ⟩ := ((HC.arExists k X p D hX).2 (Option Unit)
      (fun o : Option Unit => o.elim (ArInt.fnB (fun σ (_ : CxPts p σ) => (1 : ℝ)) hu1 hc1) fun _ => C)).1
    have h1 := ((HC.arMix.fnB HC.arExists hX hΦ (Pi.single () 1)).1 σ).1
    rw [(isometric_comb_single (fun _ : Unit => C) ()).chernPart_eq σ D 1] at h1
    exact (integrable_const_iff.1 (integrableOn_univ.1 h1)).resolve_left one_ne_zero

  have hpt (σ : k →+* ℂ) : ∀ y ∈ offSupp p σ ((C'.pow m).div hr'),
      logNorm ((C'.pow m).φ σ) r' y ≤ m * u := by
    intro y hy
    rw [hdiv] at hy
    rw [hlog σ hy]
    have hy' : y ∈ ptsIn p σ (nonzeroLocus s') := by
      have := hy
      rwa [offSupp_divOfSec] at this
    rw [logNorm_ratOfSec _ hy']
    have h1 := hs σ y
    change (((C.φ σ).addFn fun _ => 2 * u).pow m).nsq (secVal p σ s') y ≤ 1 at h1
    rw [nsq_pow_addFn_const] at h1
    have h2 : ((C.φ σ).pow m).nsq (secVal p σ s') y ≤ Real.exp (m * (2 * u)) := by
      have := Real.exp_pos (m * (2 * u))
      rw [Real.exp_neg] at h1
      rwa [mul_inv_le_iff₀ (Real.exp_pos _), one_mul] at h1
    have h0 := ((C.φ σ).pow m).nsq_nonneg (secVal p σ s') y
    have h3 : Real.log (((C.φ σ).pow m).nsq (secVal p σ s') y) ≤ m * (2 * u) := by
      rcases h0.eq_or_lt with e | e
      · rw [← e, Real.log_zero]; positivity
      · exact (Real.log_le_iff_le_exp e).2 h2
    change Real.log (((C.φ σ).pow m).nsq (secVal p σ s') y) / 2 ≤ _
    linarith
  have hA : C'.archInt (C'.pow m) D hr' ≤ m * u * gdeg C D := by
    rw [HermLB.archInt, gdeg, chInt, mul_finsum]
    refine finsum_le_finsum' (Set.toFinite _) (Set.toFinite _) fun σ => ?_
    have hS : MeasurableSet (offSupp p σ ((C'.pow m).div hr')) := (isOpen_offSupp _).measurableSet
    have hint := hI σ
    rw [← hiso.chernIntegrableOn_eq] at hint
    rw [← hiso.chernInt_eq]
    haveI := hfin σ
    simp only [Weight.chernInt, hneg σ, Measure.restrict_zero, integral_zero_measure, sub_zero,
      setIntegral_const, smul_eq_mul, mul_one]
    calc ∫ y in offSupp p σ ((C'.pow m).div hr'), logNorm ((C'.pow m).φ σ) r' y ∂(C.φ σ).chernPart D 1
        ≤ ∫ y in offSupp p σ ((C'.pow m).div hr'), (m * u : ℝ) ∂(C.φ σ).chernPart D 1 :=
          setIntegral_mono_on hint.1 (integrable_const _).integrableOn hS (hpt σ)
      _ = ((C.φ σ).chernPart D 1).real (offSupp p σ ((C'.pow m).div hr')) * (m * u) := by
          rw [setIntegral_const, smul_eq_mul]
      _ ≤ ((C.φ σ).chernPart D 1).real Set.univ * (m * u) :=
          mul_le_mul_of_nonneg_right (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _))
            (by positivity)
      _ = m * u * ((C.φ σ).chernPart D 1).real Set.univ := by ring
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have : 0 ≤ (m : ℝ) * (h (genericPoint X) + u * gdeg C D) := by
    have := hrec
    nlinarith
  exact nonneg_of_mul_nonneg_right this hmpos

end GlobalTheory.HSNef
