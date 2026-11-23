import Mathlib
import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarHaar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdConsA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef

noncomputable section

open MeasureTheory Finset
open scoped InnerProductSpace ENNReal ComplexOrder

namespace GlobalTheory.CompanionTheory.RgFdNorm

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgFd

variable {n : ℕ}

theorem cK_le_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) : cK T k ≤ 1 := by
  have h1 := norm_inner_le_norm (𝕜 := ℂ) T.w (T.op k T.w)
  have h2 : ‖T.op k T.w‖ = ‖T.w‖ := ContinuousLinearMap.norm_map_of_mem_unitary (T.τ k).2 _
  rw [h2, T.w_norm] at h1
  simpa [cK] using h1

theorem finrank_pos_KType {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    0 < Module.finrank ℂ T.V := by
  have hw : T.w ≠ 0 := fun h => by simpa [h] using T.w_norm
  have : Nontrivial T.V := ⟨T.w, 0, hw⟩
  exact Module.finrank_pos

abbrev IP (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

theorem prod_pairs (f : Fin n → Fin n → ℝ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), f a b = ∏ p : IP n, f p.1.1 p.1.2 := by
  simp_rw [Finset.prod_filter]
  rw [← Fintype.prod_prod_type' (fun a b => if a < b then f a b else 1)]
  rw [← Finset.prod_subtype (univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp)
    (fun p => f p.1 p.2), Finset.prod_filter]

def al (lam : Fin n → ℝ) (p : IP n) : ℝ := lam p.1.1 - lam p.1.2

def be (p : IP n) : ℝ := ((p.1.2 : ℕ) : ℝ) - ((p.1.1 : ℕ) : ℝ)

theorem al_pos {lam : Fin n → ℝ} (hlam : StrictAnti lam) (p : IP n) : 0 < al lam p :=
  sub_pos.2 (hlam p.2)

theorem be_nonneg (p : IP n) : 0 ≤ be p := by
  have : ((p.1.1 : ℕ) : ℝ) ≤ ((p.1.2 : ℕ) : ℝ) := by exact_mod_cast p.2.le
  exact sub_nonneg.2 this

theorem dimVlam_eq {lam : Fin n → ℝ} (hlam : StrictAnti lam) :
    dimVlam lam = (∏ p : IP n, al lam p) / ∏ p : IP n, be p := by
  unfold dimVlam
  rw [prod_pairs (fun a b => |lam a - lam b|), prod_pairs (fun a b => ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))]
  congr 1
  exact Finset.prod_congr rfl fun p _ => abs_of_pos (al_pos hlam p)

theorem one_div_dimVlam_lamT {lam : Fin n → ℝ} (hlam : StrictAnti lam) (t : ℕ) :
    1 / dimVlam (lamT lam t) = (∏ p : IP n, be p) / ∏ p : IP n, (al lam p + t * be p) := by
  rw [dimVlam_eq (strictAnti_lamT hlam t), one_div_div]
  congr 1
  exact Finset.prod_congr rfl fun p _ => by simp only [al, be, lamT_sub]

theorem one_div_dimVlam {lam : Fin n → ℝ} (hlam : StrictAnti lam) :
    1 / dimVlam lam = (∏ p : IP n, be p) / ∏ p : IP n, al lam p := by
  rw [dimVlam_eq hlam, one_div_div]

theorem isMu_step {lam : Fin n → ℝ} {μ : Fin n → ℤ} (hμ : IsMu lam μ) (t : ℕ) :
    IsMu (lamT lam t) (μ + (t : ℤ) • Dz n) := by
  intro a
  have := hμ a
  rw [lamT_apply]
  simp only [Pi.add_apply, Pi.smul_apply, Dz, smul_eq_mul]
  push_cast
  linarith

theorem hI_nonneg (hM : PhiMul) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (p : KG ε × KG ε) : 0 ≤ hI T μ x p := by
  have h1 := (hM n ε μ 0 x hx p.1).1
  have h2 := (hM n ε μ 0 x hx p.2).1
  unfold hI
  positivity

theorem hI_step (hM : PhiMul) (hC : CoefPow) {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : IsHCParam lam)
    (T : KType ε (lowK ε lam)) (TD : KType ε (Dvec n)) (t : ℕ) (Tt : KType ε (lowK ε (lamT lam t)))
    (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (p : KG ε × KG ε) :
    hI Tt (μ + (t : ℤ) • Dz n) x p = hI T μ x p * hI TD (Dz n) x p ^ t := by
  unfold hI
  rw [(hM n ε μ t x hx p.1).2, (hM n ε μ t x hx p.2).2, hC n ε lam hlam T TD t Tt]
  ring

def muS (ε : Fin n → Bool) : Measure (UJ ε) := muCD ε

instance muS_isHaar (ε : Fin n → Bool) : (muS ε).IsHaarMeasure := muCD_isHaar ε

def PP (ε : Fin n → Bool) : Measure (UJ ε × (KG ε × KG ε)) := (muS ε).prod ((dk ε).prod (dk ε))

theorem lintegral_hs (hS : HsInt) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) :
    ∫⁻ g : Formalism.REAL.UJ ε, ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) ∂(muCD ε) =
      ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) ^ 2) *
        ∫⁻ z, ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) ∂(PP ε) := by
  obtain ⟨hm, hg⟩ := hS n ε Λ T μ
  have hm' := hm.ennreal_ofReal
  rw [PP, lintegral_prod _ hm'.aemeasurable, ← lintegral_const_mul _ hm'.lintegral_prod_right']
  exact lintegral_congr fun g => hg g

theorem posDef_pP (hP : HsPol) {ε : Fin n → Bool} (g : UJ ε) : (pP (toM g)).PosDef := by
  obtain ⟨X, hX, e⟩ := (hP n ε (toM g) g.2).1
  rw [e]
  exact exp_noncompactPart_posDef hX

theorem phiK_le_one (hP : HsPol) (hL : PhiLe) {ε : Fin n → Bool} (g : UJ ε) (k : KG ε) :
    phiK (Dz n) (pP (toM g)) k ≤ 1 := by
  obtain ⟨X, hX, e⟩ := (hP n ε (toM g) g.2).1
  rw [e]
  exact hL n ε X hX k

theorem hI_le_one (hP : HsPol) (hM : PhiMul) (hL : PhiLe) {ε : Fin n → Bool} {Λ : Fin n → ℝ}
    (T : KType ε Λ) (g : UJ ε) (p : KG ε × KG ε) : hI T (Dz n) (pP (toM g)) p ≤ 1 := by
  have hx := posDef_pP hP g
  have a1 := (hM n ε (Dz n) 0 _ hx p.1).1
  have a2 := (hM n ε (Dz n) 0 _ hx p.2).1
  have b1 := phiK_le_one hP hL g p.1
  have b2 := phiK_le_one hP hL g p.2
  have c0 : 0 ≤ cK T (p.1⁻¹ * p.2) := norm_nonneg _
  have c1 := cK_le_one T (p.1⁻¹ * p.2)
  unfold hI
  have e1 : phiK (Dz n) (pP (toM g)) p.1 * phiK (Dz n) (pP (toM g)) p.2 ≤ 1 :=
    mul_le_one₀ b1 a2.le b2
  have e2 : cK T (p.1⁻¹ * p.2) ^ 2 ≤ 1 := pow_le_one₀ c0 c1
  exact mul_le_one₀ e1 (by positivity) e2

theorem mass_of_normAt (hS : HsInt) {ε : Fin n → Bool} {lam : Fin n → ℝ} (hN : NormAt ε lam)
    (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) :
    ∫⁻ z, ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) ∂(PP ε) = ENNReal.ofReal (1 / dimVlam lam) := by
  have h := hN T μ hμ
  rw [lintegral_hs hS] at h
  have hd : (0 : ℝ) < (Module.finrank ℂ T.V : ℝ) ^ 2 := by
    have := finrank_pos_KType T
    positivity
  have e : (Module.finrank ℂ T.V : ℝ) ^ 2 / dimVlam lam =
      (Module.finrank ℂ T.V : ℝ) ^ 2 * (1 / dimVlam lam) := by ring
  rw [e, ENNReal.ofReal_mul hd.le] at h
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hd).ne' ENNReal.ofReal_ne_top).1 h

theorem gap_of_le {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) {h0 : ℝ} {t : ℕ}
    (ht : ⌈h0⌉₊ ≤ t) : GapAtLeast ε (lamT lam t) h0 := by
  have g0 : GapAtLeast ε lam 0 := fun a b _ => abs_nonneg _
  have g1 := gap_lamT hlam g0 t
  intro a b hab
  have h1 := g1 a b hab
  have h2 : h0 ≤ (t : ℝ) := (Nat.le_ceil h0).trans (by exact_mod_cast ht)
  linarith

theorem ae_eq_indicator (hP : HsPol) (hM : PhiMul) (hK : KNull) {ε : Fin n → Bool} {lam : Fin n → ℝ}
    (hlam : IsHCParam lam) (T : KType ε (lowK ε lam)) (TD : KType ε (Dvec n)) (μ : Fin n → ℤ) :
    (fun z : UJ ε × (KG ε × KG ε) => ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2)) =ᵐ[PP ε]
      ({z : UJ ε × (KG ε × KG ε) | 0 < hI TD (Dz n) (pP (toM z.1)) z.2}).indicator
        (fun z => ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2)) := by
  have h1 := hK n ε lam hlam T TD
  have h2 : ∀ᵐ p ∂((dk ε).prod (dk ε)), cK TD (p.1⁻¹ * p.2) = 0 → cK T (p.1⁻¹ * p.2) = 0 :=
    (measurePreserving_prod_inv_mul (dk ε) (dk ε)).quasiMeasurePreserving.ae
      (Measure.quasiMeasurePreserving_snd.ae h1)
  have h3 : ∀ᵐ z ∂(PP ε), cK TD (z.2.1⁻¹ * z.2.2) = 0 → cK T (z.2.1⁻¹ * z.2.2) = 0 :=
    Measure.quasiMeasurePreserving_snd.ae h2
  filter_upwards [h3] with z hz
  by_cases hz0 : 0 < hI TD (Dz n) (pP (toM z.1)) z.2
  · rw [Set.indicator_of_mem (by exact hz0)]
  · rw [Set.indicator_of_notMem (by exact hz0)]
    have hx := posDef_pP hP z.1
    have a1 := (hM n ε (Dz n) 0 _ hx z.2.1).1
    have a2 := (hM n ε (Dz n) 0 _ hx z.2.2).1
    have hc : cK TD (z.2.1⁻¹ * z.2.2) = 0 := by
      by_contra hne
      have : 0 < cK TD (z.2.1⁻¹ * z.2.2) := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      exact hz0 (by unfold hI; positivity)
    have hT := hz hc
    simp [hI, hT]

theorem norm_induction_of_estimates : MomW → CoefPow → KNull → HsPol → PhiMul → PhiLe → PhiCont → HsInt → GapNorm → NormInd := by
  intro hMom hC hK hP hM hL _ hS hG n ε hp hq lam hlam T μ hμ
  obtain ⟨h0, hg⟩ := hG n ε hp hq
  obtain ⟨TD⟩ := HW.kType_exists_of_dom ε (Dvec n) (fun a => ⟨Dz n a, by simp [Dvec, Dz]⟩)
    (fun a b hab _ => dvec_antitone hab.le)
  have hUm : Measurable fun z : UJ ε × (KG ε × KG ε) => hI TD (Dz n) (pP (toM z.1)) z.2 :=
    (hS n ε _ TD (Dz n)).1
  have hhm : Measurable fun z : UJ ε × (KG ε × KG ε) => ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) :=
    (hS n ε _ T μ).1.ennreal_ofReal
  have hmom : ∀ t : ℕ, ⌈h0⌉₊ ≤ t →
      ∫⁻ z, ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) *
          ENNReal.ofReal (hI TD (Dz n) (pP (toM z.1)) z.2 ^ t) ∂(PP ε) =
        ENNReal.ofReal ((∏ p : IP n, be p) / ∏ p : IP n, (al lam p + t * be p)) := by
    intro t ht
    obtain ⟨Tt⟩ := HW.kType_exists ε (lamT lam t) (isHCParam_lamT hlam t)
    rw [← one_div_dimVlam_lamT hlam.1 t,
      ← mass_of_normAt hS (hg _ (isHCParam_lamT hlam t) (gap_of_le hlam.1 ht)) Tt _ (isMu_step hμ t)]
    refine lintegral_congr fun z => ?_
    rw [hI_step hM hC hlam T TD t Tt μ (posDef_pP hP z.1),
      ENNReal.ofReal_mul (hI_nonneg hM T μ (posDef_pP hP z.1) z.2)]
  have key := hMom _ (PP ε) _ _ (IP n) (al lam) be (∏ p : IP n, be p) ⌈h0⌉₊ hhm hUm
    (fun z => ⟨hI_nonneg hM TD _ (posDef_pP hP z.1) z.2, hI_le_one hP hM hL TD z.1 z.2⟩)
    (al_pos hlam.1) be_nonneg (Finset.prod_nonneg fun p _ => be_nonneg p) hmom
  rw [← one_div_dimVlam hlam.1] at key
  have hmass : ∫⁻ z, ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) ∂(PP ε) =
      ENNReal.ofReal (1 / dimVlam lam) := by
    rw [lintegral_congr_ae (ae_eq_indicator hP hM hK hlam T TD μ),
      lintegral_indicator (measurableSet_lt measurable_const hUm)]
    exact key
  rw [lintegral_hs hS, hmass, ← ENNReal.ofReal_mul (sq_nonneg _), mul_one_div]

end GlobalTheory.CompanionTheory.RgFdNorm
