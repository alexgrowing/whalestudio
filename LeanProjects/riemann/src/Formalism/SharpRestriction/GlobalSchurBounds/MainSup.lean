import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.GlobalSchurBounds.FirstClaimLemmaTwoFourOfLemmaTwoThree
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.GlobalSchurBounds.TopDensityNGeSixteen
import Formalism.SharpRestriction.GlobalSchurBounds.JointsL

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

theorem Closed.of_all {𝒞 : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop}
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), P Fm CH) : Closed 𝒞 P :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => h Fm CH⟩⟩

theorem logNE_le_of_rows (D : D7) {Y x eps : ℝ} (he : 0 < eps) (h1 : 1 < Y) (hY : Y ≤ x) (h : QDRows_at D Y eps) :
    Real.log (GlobalTheoryTheory.NE D) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlog⟩ := h
  have hY0 : 0 < Y := by linarith
  have hNE : Real.log (GlobalTheoryTheory.NE D) ≤ 2 * Y ^ (eps / 5) * Real.log Y ^ 2 := by
    first
      | (unfold GlobalTheoryTheory.NE; push_cast; exact hlog)
      | simpa [GlobalTheoryTheory.NE] using hlog
  have ha : Y ^ (eps / 5) ≤ x ^ (eps / 5) := Real.rpow_le_rpow hY0.le hY (by linarith)
  have hl0 : 0 ≤ Real.log Y := Real.log_nonneg h1.le
  have hl : Real.log Y ≤ Real.log x := Real.log_le_log hY0 hY
  have hsq : Real.log Y ^ 2 ≤ Real.log x ^ 2 := by nlinarith
  have hp : 0 ≤ Y ^ (eps / 5) := Real.rpow_nonneg hY0.le _
  have hm : Y ^ (eps / 5) * Real.log Y ^ 2 ≤ x ^ (eps / 5) * Real.log x ^ 2 :=
    mul_le_mul ha hsq (by positivity) (le_trans hp ha)
  linarith

theorem one_lt_of_win {eps : ℝ} (Fm : FamP eps) {x Y : ℝ} (hx : 1 < x) (h : x ^ (1 / Fm.J) ≤ Y) : 1 < Y := by
  obtain ⟨i⟩ := Fm.Ix_zero
  have hJ : 1 ≤ Fm.J := by
    have h0 := (Fm.L 0 i).sc.one_le_J
    rwa [Fm.L_J 0 i] at h0
  have hp : 0 < 1 / Fm.J := one_div_pos.mpr (by linarith)
  exact lt_of_lt_of_le (Real.one_lt_rpow hx hp) h

theorem eps_pos_of_fam {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  have h0 := (Fm.L 0 i).sc.eps_pos
  rwa [Fm.L_eps 0 i] at h0

theorem pair_and_box_hypothesis_of_congruence_data_and_boxes {eps : ℝ} (Fm : FamP eps) (hR : QDRowsF Fm) (hB : BoxesF Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      (∃ Y : ℝ, 1 < Y ∧ Y ≤ x ∧ ShortIntervalPrimes.PairAt Y eps (Fm.D x i).host.q (Fm.D x i).host.d) ∧ ShortIntervalPrimes.PropTwoSixBoxHypothesis (Fm.D x i) x eps := by
  obtain ⟨xR, hR⟩ := hR
  obtain ⟨xB, hB⟩ := hB
  refine ⟨max (max xR xB) 2, fun x hx i => ?_⟩
  have hxR : xR ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxB : xB ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : 1 < x := by linarith [le_max_right (max xR xB) 2]
  obtain ⟨Y, ⟨hY1, hY2⟩, hQ⟩ := hR x hxR i
  obtain ⟨Y', ⟨hY1', hY2'⟩, -, hE⟩ := hB x hxB i
  have hY : 1 < Y := one_lt_of_win Fm hx1 hY1
  have hY' : 1 < Y' := one_lt_of_win Fm hx1 hY1'
  have hlog := logNE_le_of_rows (Fm.D x i) (eps_pos_of_fam Fm) hY hY2 hQ
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -⟩ := hQ
  exact ⟨⟨Y, hY, hY2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, ⟨Y', hY', hY2', hE⟩, hlog⟩

theorem primesAsPropTwoFive_iff_pair_box_and_chQD (D : D7) (x eps C : ℝ) :
    ShortIntervalPrimes.PrimesAsPropTwoFive D x eps C ↔ (∃ Y : ℝ, 1 < Y ∧ Y ≤ x ∧ ShortIntervalPrimes.PairAt Y eps D.host.q D.host.d) ∧ ShortIntervalPrimes.PropTwoSixBoxHypothesis D x eps ∧
      ChQD_at D x eps C :=
  Iff.rfl

theorem family_recursion_of_congruences_and_boxes {eps : ℝ} (Fm : FamP eps) (hR : QDRowsF Fm) (hB : BoxesF Fm) (C5 : ℝ) (h0 : 0 < C5)
    (hQ : ChosenQD Fm C5) : ShortIntervalPrimes.FamilyPrimesAsPropTwoFive Fm := by
  obtain ⟨xa, ha⟩ := pair_and_box_hypothesis_of_congruence_data_and_boxes Fm hR hB
  obtain ⟨xb, hb⟩ := hQ
  refine ⟨C5, h0, max (max xa xb) 2, by linarith [le_max_right (max xa xb) 2], fun x hx i => ?_⟩
  have hxa : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : xb ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  obtain ⟨hp, hP⟩ := ha x hxa i
  exact (primesAsPropTwoFive_iff_pair_box_and_chQD _ _ _ _).2 ⟨hp, hP, hb x hxb i⟩

theorem boxes_of_family_recursion {eps : ℝ} (Fm : FamP eps) (h : ShortIntervalPrimes.FamilyPrimesAsPropTwoFive Fm) :
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ShortIntervalPrimes.PropTwoSixBoxHypothesis (Fm.D x i) x eps) ∧
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      ∃ Y : ℝ, 1 < Y ∧ Y ≤ x ∧ ShortIntervalPrimes.PairAt Y eps (Fm.D x i).host.q (Fm.D x i).host.d := by
  obtain ⟨C, -, x0, -, h⟩ := h
  exact ⟨⟨x0, fun x hx i => ((primesAsPropTwoFive_iff_pair_box_and_chQD _ _ _ _).1 (h x hx i)).2.1⟩,
    x0, fun x hx i => ((primesAsPropTwoFive_iff_pair_box_and_chQD _ _ _ _).1 (h x hx i)).1⟩

def LitThin : Prop :=
  (∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧ ∀ D : D7, ShortIntervalPrimes.adm6 D C1 c) ∧ (∃ C : ℝ, 0 < C ∧ ∀ D : D7, ShortIntervalPrimes.adm7 D C) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ D : D7, ShortIntervalPrimes.adm11 D C

theorem prop_two_six_congruence_family_of_literature {eps : ℝ} (Fm : FamP eps) (hL : LitThin) : ShortIntervalPrimes.FamilyPropTwoSixCongruenceForm Fm := by
  obtain ⟨⟨C1, c, hC1, hc, h6⟩, ⟨C7, hC7, h7⟩, C11, hC11, h11⟩ := hL
  exact ShortIntervalPrimes.proposition_six_norm_family_of_admitted Fm ⟨C1, c, hC1, hc, fun _ _ _ => h6 _⟩ ⟨C7, hC7, fun _ _ _ => h7 _⟩ ⟨C11, hC11, fun _ _ _ => h11 _⟩

theorem prop_two_six_family_of_literature {eps : ℝ} (Fm : FamP eps) (hL : LitThin) : ShortIntervalPrimes.Conclusion6Family Fm := by
  obtain ⟨c, hc, x0, hx0, h⟩ := prop_two_six_congruence_family_of_literature Fm hL
  refine ⟨c, hc, x0, hx0, fun x hx i => ?_⟩
  have hn := h x hx i
  unfold ShortIntervalPrimes.PropTwoSixThinScales at hn
  unfold ShortIntervalPrimes.Conclusion6
  rintro ⟨C5, h5⟩
  exact hn ((primesAsPropTwoFive_iff_pair_box_and_chQD _ _ _ _).1 h5).2.1

theorem chosenThin_of_boxesN {eps : ℝ} (Fm : FamP eps) (hL : LitThin) (hB : BoxesF Fm) (hR : QDRowsF Fm) :
    ∃ c6 : ℝ, 0 < c6 ∧ ChosenThin Fm c6 := by
  obtain ⟨c, hc, x0, -, h⟩ := prop_two_six_congruence_family_of_literature Fm hL
  obtain ⟨xa, ha⟩ := pair_and_box_hypothesis_of_congruence_data_and_boxes Fm hR hB
  refine ⟨c, hc, max x0 xa, fun x hx i => ?_⟩
  have h1 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have h2 : xa ≤ x := le_trans (le_max_right _ _) hx
  have hn := h x h1 i
  unfold ShortIntervalPrimes.PropTwoSixThinScales at hn
  exact hn (ha x h2 i).2

theorem chosenThin_closedN (𝒞 : FamClass) (hL : LitThin) :
    Closed 𝒞 (fun Fm _ => BoxesF Fm → QDRowsF Fm → ∃ c6 : ℝ, 0 < c6 ∧ ChosenThin Fm c6) :=
  Closed.of_all fun Fm _ hB hR => chosenThin_of_boxesN Fm hL hB hR

theorem chosenThin_of_boxes {eps : ℝ} (Fm : FamP eps) (hL : LitThin) (hB : BoxesF Fm) (hR : QDRowsF Fm)
    (_hQ : ∃ C5 : ℝ, 0 < C5 ∧ ChosenQD Fm C5) : ∃ c6 : ℝ, 0 < c6 ∧ ChosenThin Fm c6 :=
  chosenThin_of_boxesN Fm hL hB hR

theorem chosenThin_closed (𝒞 : FamClass) (hL : LitThin) :
    Closed 𝒞 (fun Fm _ => BoxesF Fm → QDRowsF Fm → (∃ C5 : ℝ, 0 < C5 ∧ ChosenQD Fm C5) →
      ∃ c6 : ℝ, 0 < c6 ∧ ChosenThin Fm c6) :=
  Closed.of_all fun Fm _ hB hR _ => chosenThin_of_boxesN Fm hL hB hR

theorem besselId_iff (D : D7) : BesselId D ↔ D.BuRational ∧ TR_at D :=
  Iff.rfl

theorem trF_sbF_of_linkDIV {eps : ℝ} (Fm : FamP eps) (Cabs CH : ℝ) (h : LinkDIV Fm Cabs CH) : TRF Fm ∧ SBF Fm CH := by
  obtain ⟨C, x0, h⟩ := h
  refine ⟨⟨x0, fun x hx i => ?_⟩, ⟨x0, fun x hx i => ?_⟩⟩
  · obtain ⟨-, -, -, ⟨-, hTR⟩, -⟩ := h x hx i
    exact hTR
  · obtain ⟨-, hSB, -⟩ := h x hx i
    exact hSB

theorem dGamMink_of (D : D7) (C : ℝ) (hC : 0 ≤ C) (hM : MinkLit C) (hc : DGamChoice_at D) :
    GlobalTheoryTheory.DGamMink D (4 * C) := by
  have hf : 2 ≤ D.R.f := by
    have := D.R.ord_pos
    show 2 ≤ 2 * D.R.ord
    omega
  have hN : 1 ≤ D.R.N D.R.m := by
    have h1 := D.R.k_ge
    have h2 : D.R.k ≤ D.R.N D.R.m := Nat.le_add_right _ _
    omega
  have hfN : 2 ≤ D.R.f * D.R.N D.R.m := by
    calc 2 = 2 * 1 := rfl
      _ ≤ D.R.f * D.R.N D.R.m := Nat.mul_le_mul hf hN
  obtain ⟨M, hM0, hmul, hlog⟩ := hM (2 * D.R.f * D.R.N D.R.m) (by rw [mul_assoc]; omega)
  refine ⟨M, hM0, hc M hmul, hlog.trans ?_⟩
  have hy : (2 : ℝ) ≤ (D.R.f : ℝ) * D.R.N D.R.m := by exact_mod_cast hfN
  have e : ((2 * D.R.f * D.R.N D.R.m : ℕ) : ℝ) = 2 * ((D.R.f : ℝ) * D.R.N D.R.m) := by push_cast; ring
  rw [e, Real.log_mul (by norm_num) (by linarith)]
  have h2 : Real.log 2 ≤ Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := Real.log_le_log (by norm_num) hy
  have h3 : 0 ≤ Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := Real.log_nonneg (by linarith)
  have h4 : 0 ≤ C * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) := by positivity
  calc C * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (Real.log 2 + Real.log ((D.R.f : ℝ) * D.R.N D.R.m))
      ≤ C * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (2 * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) :=
        mul_le_mul_of_nonneg_left (by linarith) h4
    _ = 4 * C * D.R.f * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by ring

theorem dGamSize_of {eps : ℝ} (Fm : FamP eps) (C : ℝ) (hC : 0 ≤ C) (hM : MinkLit C) (hc : DGamChoiceF Fm) : DGamSize Fm := by
  obtain ⟨x0, hc⟩ := hc
  refine ⟨4 * C, x0, fun x hx i => ?_⟩
  unfold FactDGam
  intro u
  obtain ⟨Mk, hMk, hdvd, hlog⟩ := dGamMink_of (Fm.D x i) C hC hM (hc x hx i)
  have hle : ((Fm.D x i).mem u).C.DGam ≤ Mk := Nat.le_of_dvd hMk (hdvd u)
  have hpos : 0 < ((Fm.D x i).mem u).C.DGam := Nat.pos_of_dvd_of_pos (hdvd u) hMk
  calc Real.log (((Fm.D x i).mem u).C.DGam : ℝ) ≤ Real.log (Mk : ℝ) :=
        Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
    _ ≤ _ := hlog

theorem dGamSize_closed (𝒞 : FamClass) (C : ℝ) (hC : 0 ≤ C) (hM : MinkLit C) :
    Closed 𝒞 (fun Fm _ => DGamChoiceF Fm → DGamSize Fm) :=
  Closed.of_all fun Fm _ hc => dGamSize_of Fm C hC hM hc

theorem tuSize_sup (C3 : ℝ) (hC3 : 0 ≤ C3) (eps : ℝ) (h1 : 0 < eps) (h2 : eps < 1 / 52) :
    ∃ cT : ℝ → ℝ, ∀ Fm : FamP eps, cT Fm.CYL ≤ Fm.CTu → StandardLattice.FamilyMassVolumeBounds Fm → StandardLattice.FamilyTheoremThree Fm C3 → StandardLattice.FamilyPartFour Fm C3 →
      TuSize Fm := by
  refine ⟨fun y => Classical.choose (StandardLattice.weylLawStatement_eventually eps (max 5 (y + 1)) C3 h1 h2 hC3), fun Fm hle p2 p3 p4 => ?_⟩
  have hC := Classical.choose_spec (StandardLattice.weylLawStatement_eventually eps (max 5 (Fm.CYL + 1)) C3 h1 h2 hC3)
  obtain ⟨x0, hx0⟩ := StandardLattice.familyLevelSectionB_holds Fm C3 p4 (max 5 (Fm.CYL + 1))
  refine GlobalTheoryTheory.tuSize_fam Fm _ x0 (fun x hx hx1 i => ?_) hle
  have q4 := p4 x hx1 i
  exact hC (Fm.D x i) (Fm.L x i).sc (Fm.L_eps x i) (p2 x i) (p3 x i) q4.1 q4.2.1 (hx0 x hx hx1 i)

section Proviso

variable {D : D7}

theorem proviso_e (L : SizeData₂ D) (h4f : LinkB.RankM D) (hDu : StandardLattice.FactDuStar D) (hDs : StandardLattice.FactDstar D) :
    ChProviso_at L (Real.exp 1) := by
  intro u
  have hΓ : 1 < (D.mem u).A.GamP := (D.mem u).A.one_lt_gammaP
  have hΓ0 : 0 < (D.mem u).A.GamP := lt_trans one_pos hΓ
  have hD : 0 < StandardLattice.DstarD D := by rw [← hDs, ← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos
  have hd : 0 < StandardLattice.duStarU D u := by rw [← hDu u]; exact_mod_cast (D.mem u).A.duStar_pos
  have hk := D.R.k_ge
  have hf : 1 ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    omega
  have hfk : 2 * D.R.f ≤ 2 ^ D.R.k := by
    have h1 : D.R.f ≤ D.R.k := D.R.f_le_k
    have h2 : D.R.k - 1 < 2 ^ (D.R.k - 1) := Nat.lt_two_pow_self
    have h3 : 2 ^ D.R.k = 2 * 2 ^ (D.R.k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  have hkR : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
  have hX : Real.exp (StandardLattice.logXuD D u) ^ (D.R.f * D.R.k) = StandardLattice.DstarD D / StandardLattice.duStarU D u := by
    rw [← Real.exp_nat_mul]
    unfold StandardLattice.logXuD StandardLattice.logXu
    push_cast
    rw [show (D.R.f : ℝ) * D.R.k * (1 / ((D.R.f : ℝ) * D.R.k) * Real.log (StandardLattice.DstarD D / StandardLattice.duStarU D u)) =
      Real.log (StandardLattice.DstarD D / StandardLattice.duStarU D u) by field_simp]
    exact Real.exp_log (div_pos hD hd)
  have hT : (2 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.two_le
  have hw := D.T_win u
  have hXe := LinkB.exp_logXu hDu hDs u
  have h1 : Real.exp (StandardLattice.logXuD D u) * (D.mem u).A.GamP ^ (-(2 : ℝ) / (D.R.f * D.R.k)) =
      (D.mem u).A.Tstar := by rw [hXe]; rfl
  obtain ⟨c1, c2, -, -⟩ := Formalism.HermitianLattices.GenusMassVolumes.mass_corollary D.R.f D.R.k ((D.mem u).A.T : ℝ)
    (Real.exp (StandardLattice.logXuD D u)) (D.mem u).A.GamP (StandardLattice.DstarD D) (StandardLattice.duStarU D u) (D.duS u : ℝ)
    (StandardLattice.logXuD D u) (StandardLattice.logXuD D u) hf (by omega) hfk hT (Real.exp_pos _) hΓ.le hD hd hX
    (by rw [h1]; exact hw.1) (by rw [h1, mul_comm]; exact hw.2) (h4f u)
    (by rw [Real.log_exp]) (by rw [Real.log_exp])
  rw [LinkB.gamL_eq L u, hDs]
  have hG2 : 0 ≤ (D.mem u).A.GamP ^ 2 := by positivity
  constructor
  · have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    refine (inv_anti₀ (by norm_num) he).trans ?_
    rw [le_div_iff₀ hD]
    calc (2 : ℝ)⁻¹ * StandardLattice.DstarD D = StandardLattice.DstarD D * ((D.mem u).A.GamP⁻¹) ^ 2 / 2 * (D.mem u).A.GamP ^ 2 := by
          field_simp
      _ ≤ (D.duS u : ℝ) * (D.mem u).A.GamP ^ 2 := mul_le_mul_of_nonneg_right c1 hG2
  · rw [div_le_iff₀ hD]
    calc (D.duS u : ℝ) * (D.mem u).A.GamP ^ 2
        ≤ Real.exp 1 * (StandardLattice.DstarD D * ((D.mem u).A.GamP⁻¹) ^ 2) * (D.mem u).A.GamP ^ 2 :=
          mul_le_mul_of_nonneg_right c2 hG2
      _ = Real.exp 1 * StandardLattice.DstarD D := by field_simp

end Proviso

theorem chosenProviso_sup {eps : ℝ} (Fm : FamP eps) (C3 C0 : ℝ) (hC0 : Real.exp 1 ≤ C0) (h4 : StandardLattice.FamilyPartFour Fm C3)
    (hR : LinkB.RankHypF Fm) : ChosenProviso Fm C0 := by
  unfold StandardLattice.FamilyPartFour at h4
  obtain ⟨x0, hR⟩ := hR
  unfold ChosenProviso
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have h0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have h1 : Fm.x1 < x := by linarith [le_max_right x0 (Fm.x1 + 1)]
  have hP := h4 x h1 i
  unfold StandardLattice.StandardLatticeProperties at hP
  have hM : LinkB.RankM (Fm.D x i) := LinkB.rank_formula_of_part_four _ hP.2.2.2.2.2.2.2.1 (hR x h0 i)
  have he := proviso_e (Fm.L x i) hM (StandardLattice.factDuStar_fam Fm x h1 i) (StandardLattice.factDstar_fam Fm x h1 i)
  unfold ChProviso_at at he ⊢
  intro u
  obtain ⟨ha, hb⟩ := he u
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hinv : C0⁻¹ ≤ (Real.exp 1)⁻¹ := by
    first
    | exact inv_anti₀ hepos hC0
    | exact inv_le_inv_of_le hepos hC0
  exact ⟨le_trans hinv ha, le_trans hb hC0⟩

theorem chosenProviso_closed (𝒞 : FamClass) (C3 C0 : ℝ) (hC0 : Real.exp 1 ≤ C0) :
    Closed 𝒞 (fun Fm _ => StandardLattice.FamilyPartFour Fm C3 → LinkB.RankHypF Fm → ChosenProviso Fm C0) :=
  Closed.of_all fun Fm _ h4 hR => chosenProviso_sup Fm C3 C0 hC0 h4 hR

def RankTiesF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (∀ j, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).host.g j)) ∧
    ∀ u : (Fm.D x i).what₂.Word, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).mem u).A.T ∧ StandardLattice.Mu0Tie (Fm.D x i) u

theorem rankHypF_of {eps : ℝ} (Fm : FamP eps) (h : RankTiesF Fm) : LinkB.RankHypF Fm := by
  obtain ⟨x0, h⟩ := h
  unfold LinkB.RankHypF
  refine ⟨max (max x0 3) (Fm.x1 + 1), fun x hx i => ?_⟩
  have h0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have h3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have h1 : Fm.x1 < x := by linarith [le_max_right (max x0 3) (Fm.x1 + 1)]
  obtain ⟨hg, hu⟩ := h x h0 i
  unfold LinkB.RankHyp
  exact ⟨GlobalTheoryTheory.JDB.gBig_fam Fm x h3 h1 i, hg, hu⟩

theorem chosenProviso_closed' (𝒞 : FamClass) (C3 C0 : ℝ) (hC0 : Real.exp 1 ≤ C0) :
    Closed 𝒞 (fun Fm _ => StandardLattice.FamilyPartFour Fm C3 → RankTiesF Fm → ChosenProviso Fm C0) :=
  Closed.of_all fun Fm _ h4 hT => chosenProviso_sup Fm C3 C0 hC0 h4 (rankHypF_of Fm hT)

theorem tuSize_thr (C3 : ℝ) (hC3 : 0 ≤ C3) (eps : ℝ) (h1 : 0 < eps) (h2 : eps < 1 / 52) :
    ∃ cT : ℝ → ℝ, ∀ K : TransportedAlt, (∀ l, cT (l.getD 6 0) ≤ K.mid l) → ∀ Fm : FamP eps, K.mid Fm.cOut ≤ Fm.CTu →
      StandardLattice.FamilyMassVolumeBounds Fm → StandardLattice.FamilyTheoremThree Fm C3 → StandardLattice.FamilyPartFour Fm C3 → TuSize Fm := by
  obtain ⟨cT, hcT⟩ := tuSize_sup C3 hC3 eps h1 h2
  refine ⟨cT, fun K hK Fm hFm hF2 hF3 hF4 => hcT Fm ?_ hF2 hF3 hF4⟩
  have e : Fm.cOut.getD 6 0 = Fm.CYL := by
    first
      | rfl
      | simp [FamP.cOut]
  have hk := hK Fm.cOut
  rw [e] at hk
  exact hk.trans hFm

end Formalism.MainNotions

end
