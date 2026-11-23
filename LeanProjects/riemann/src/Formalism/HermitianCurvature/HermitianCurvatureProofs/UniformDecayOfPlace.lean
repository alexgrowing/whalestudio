import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramLocSetCApp

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate

noncomputable section

theorem thr_plus3 (c0 Cc R X N A : ℝ) (hc : max (4 * c0) 0 ≤ Cc) (hR : 0 ≤ R) (hX : 1 ≤ X) (hN : 0 ≤ N)
    (hA : Cc * R * (N * X ^ 2 + X ^ 3) ≤ A) : c0 * R * ((N + 3) * X ^ 2 + X ^ 3) ≤ A := by
  have hX2 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have hY : 0 ≤ N * X ^ 2 + X ^ 3 := by positivity
  have hle : (N + 3) * X ^ 2 + X ^ 3 ≤ 4 * (N * X ^ 2 + X ^ 3) := by nlinarith
  have hY' : 0 ≤ (N + 3) * X ^ 2 + X ^ 3 := by positivity
  have h0 : 0 ≤ Cc := le_trans (le_max_right _ _) hc
  have h4 : 4 * c0 ≤ Cc := le_trans (le_max_left _ _) hc
  refine le_trans ?_ hA
  rcases le_or_gt c0 0 with hc0 | hc0
  · have : c0 * R * ((N + 3) * X ^ 2 + X ^ 3) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc0 hR) hY'
    exact le_trans this (by positivity)
  · calc c0 * R * ((N + 3) * X ^ 2 + X ^ 3) ≤ c0 * R * (4 * (N * X ^ 2 + X ^ 3)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (4 * c0) * R * (N * X ^ 2 + X ^ 3) := by ring
      _ ≤ Cc * R * (N * X ^ 2 + X ^ 3) := by gcongr

theorem bound_absorb (K C M y a b : ℝ) (_hM : 0 ≤ M) (hy : 0 ≤ y) (_hb : 0 ≤ b) (hK : 0 ≤ K)
    (ha : a ≤ C * y) (hyM : y ≤ M * b) : K * a ≤ (K * |C| * M) * b := by
  have h1 : C * y ≤ |C| * (M * b) := le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hy)
    (mul_le_mul_of_nonneg_left hyM (abs_nonneg C))
  calc K * a ≤ K * (|C| * (M * b)) := mul_le_mul_of_nonneg_left (le_trans ha h1) hK
    _ = (K * |C| * M) * b := by ring

def DecayUnifOfPlace : Prop :=
  P5.ThmPActualCpt → KB.RadHead → KB.HeadTop → Formalism.FourierDecayAlt.P.PBO.DecayUnif → Formalism.FourierDecayAlt.P.PBASM.DecayUnif

theorem decayUnif_of_place (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop)
    (hD : Formalism.FourierDecayAlt.P.PBO.DecayUnif) : Formalism.FourierDecayAlt.P.PBASM.DecayUnif := by
  have hPS : PStdC := pStdC_of hP hRH hHT
  intro Cb
  obtain ⟨c0, hc0⟩ := hD hP Cb
  obtain ⟨c1, hc1⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨max (max (4 * c0) 0) c1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB v ε hε i hi1 hir a ha h h' hsz hsz'
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : j ≤ S.G.r := by omega
  simp only [Nat.add_sub_cancel] at hsz hsz'
  have hgpos := g_pos_of_built hB
  have hB' := hB
  obtain ⟨-, -, -, hcut, -, -, -, -, -, -, hGo, -, -, -, hA, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, hCk, hCC⟩ := hv v
  have hCI : KB.CutInside S := Formalism.FourierDecayAlt.P.PBCut.cutInside_of_built hB
  obtain ⟨w, rfl⟩ := ha
  have hw : KB.CutWord (D.parOf S v) (S.l + 1) (w.1 v) := cutWord_of_adm S hGo hCI w v
  have hlen : (w.1 v).length ≤ S.Ntop := le_trans (Formalism.FourierDecayAlt.P.PBB.len_le_cnt S w v) w.2.2
  have hR : (0 : ℝ) ≤ ((S.G.r : ℝ) + 1) ^ 4 := by positivity
  have hX : (1 : ℝ) ≤ 2 * (S.G.r : ℝ) + S.G.k + 1 := by
    have : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ S.G.k := Nat.cast_nonneg _
    linarith
  have hNn : (0 : ℝ) ≤ S.Ntop := Nat.cast_nonneg _

  have hcpt : ∀ n, KB.CptCoef (p v).T.base (Formalism.FourierDecayAlt.P.PBASM.cutSeq S p f χ n v ε) := by
    intro n
    refine ((hc1 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop Formalism.FourierDecayAlt.P.PBASM.cutN
      (by rw [hl0]; exact hInD) hcut hε hCk hCC (le_trans ?_ hA) (fun n g => rfl)).1 n)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hR) (by positivity)
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · have hH : D.IsLocPt (stdS S h) j := (isLocPt_toStd_iff _ _ hgpos h 1 j).2 hloc.1
    have hH' : D.IsLocPt (stdS S h') j := (isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hloc.2
    have hroom : 10 * ((S.Ntop : ℝ) + 3 * (2 * (S.G.r : ℝ) + 1) + 1) ≤ S.cutHi v - S.cutLo v := by
      have hN : (S.Ntop : ℝ) = 20 * ((S.G.r : ℝ) + 1) := by
        unfold C.HidaSetting.Ntop C.Kst; push_cast; ring
      have h6 := (hGo v).1
      have hr : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
      have hN20 : (20 : ℝ) ≤ S.Ntop := by rw [hN]; linarith
      have hsq : (400 : ℝ) ≤ (S.Ntop : ℝ) ^ 2 := by nlinarith
      have hN3 : (400 : ℝ) * S.Ntop ≤ (S.Ntop : ℝ) ^ 3 := by
        calc (400 : ℝ) * S.Ntop ≤ (S.Ntop : ℝ) ^ 2 * S.Ntop := mul_le_mul_of_nonneg_right hsq hNn
          _ = (S.Ntop : ℝ) ^ 3 := by ring
      nlinarith
    obtain ⟨C, hC⟩ := hc0 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop
      Formalism.FourierDecayAlt.P.PBASM.cutN (S.cutLo v) (S.cutHi v) (by rw [hl0]; exact hInD) hcut hε hCk hCC
      (by
        have := thr_plus3 c0 (max (max (4 * c0) 0) c1) (((S.G.r : ℝ) + 1) ^ 4) (2 * (S.G.r : ℝ) + S.G.k + 1)
          S.Ntop A₀ (le_max_left _ _) hR hX hNn (by simpa [mul_assoc] using hA)
        push_cast
        linarith [this])
      (fun n g => rfl) (fun Y h1 h2 => by rw [hl0]; exact hCI v Y ⟨h1, h2⟩) (by push_cast; linarith [hroom])
      j hj (w.1 v) (by rw [hl0]; exact hw) hlen (stdS S h) (stdS S h') hH hH'
    set lam := lamS S j with hlam
    have hlam_pos : 0 < lam := lamS_pos S hgpos j
    set tw : ℝ := 2 * Real.pi / ((S.g : ℝ) * lam) with htw
    have htw_pos : 0 < tw := by rw [htw]; positivity
    have hsW : ∀ l : ℂ, ‖sW S j l‖ = tw * ‖l‖ := by
      intro l
      unfold sW
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg htw_pos.le, one_mul]
    set K1 : ℝ := |Kg S j h h'| with hK1
    set K2 : ℝ := abs (Kg S j h h' * |(lamS S j ^ 2)⁻¹|) with hK2
    refine ⟨K1 * |C| * (max 1 lam⁻¹) ^ 3 + K2 * |C| * (max 1 tw⁻¹) ^ 3, fun n => ⟨fun c hc => ?_, fun l => ?_⟩⟩
    · have hb : 0 ≤ ((1 + ‖c‖) ^ 3)⁻¹ := by positivity
      have hlc : (lam : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc
      have hb1 := (hC n).1 _ hlc
      rw [gramLoc_setC_app hB _ v ε j hj (w.1 v) h h' hsz hsz' c hc, mul_assoc, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
      have hnl : ‖(lam : ℂ) * c‖ = lam * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam_pos.le]
      rw [hnl] at hb1
      have := bound_absorb K1 C ((max 1 lam⁻¹) ^ 3) (((1 + lam * ‖c‖) ^ 3)⁻¹) _ _ (by positivity) (by positivity)
        hb (abs_nonneg _) hb1 (decay_scale lam ‖c‖ hlam_pos (norm_nonneg _))
      have h2 : 0 ≤ K2 * |C| * (max 1 tw⁻¹) ^ 3 * ((1 + ‖c‖) ^ 3)⁻¹ := by positivity
      calc K1 * _ ≤ (K1 * |C| * (max 1 lam⁻¹) ^ 3) * ((1 + ‖c‖) ^ 3)⁻¹ := this
        _ ≤ _ := by nlinarith
    · have hb : 0 ≤ ((1 + ‖l‖) ^ 3)⁻¹ := by positivity
      have hb1 := (hC n).2 (sW S j l)
      rw [hsW l] at hb1
      rw [int_gramLoc_setC hPS hB _ v ε (hcpt n) j hj (w.1 v) hw l h h' hloc.1 hloc.2, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      have := bound_absorb K2 C ((max 1 tw⁻¹) ^ 3) (((1 + tw * ‖l‖) ^ 3)⁻¹) _ _ (by positivity) (by positivity)
        hb (abs_nonneg _) hb1 (decay_scale tw ‖l‖ htw_pos (norm_nonneg _))
      have h2 : 0 ≤ K1 * |C| * (max 1 lam⁻¹) ^ 3 * ((1 + ‖l‖) ^ 3)⁻¹ := by positivity
      calc K2 * _ ≤ (K2 * |C| * (max 1 tw⁻¹) ^ 3) * ((1 + ‖l‖) ^ 3)⁻¹ := this
        _ ≤ _ := by nlinarith
  · have hz : ∀ (n : ℕ) (c : ℂ), (setC S p (Formalism.FourierDecayAlt.P.PBASM.cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v)
        (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
      intro n c
      rw [gramLoc_setC hB, rr_zero_of_not, mul_zero]
      unfold stdS
      rw [isLocPt_toStd_iff _ _ hgpos, isLocPt_toStd_iff _ _ hgpos]
      rintro ⟨h1, h2⟩
      exact hloc ⟨⟨fun b hb => h1.1 b (List.mem_append_left _ hb), hsz⟩,
        ⟨fun b hb => h2.1 b (List.mem_append_left _ hb), hsz'⟩⟩
    refine ⟨0, fun n => ⟨fun c _ => ?_, fun l => ?_⟩⟩
    · rw [hz n c]; simp
    · simp [hz n]

end

end Formalism.FourierDecayAlt.P.StandardPairingDecay

theorem Formalism.FourierDecayAlt.P.uniform_decay_of_place : Formalism.FourierDecayAlt.P.StandardPairingDecay.DecayUnifOfPlace :=
  fun hP hRH hHT hD => Formalism.FourierDecayAlt.P.StandardPairingDecay.decayUnif_of_place hP hRH hHT hD
