import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramLocSetCApp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramLocTendsto
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeAtMinusW

namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

open Classical

theorem uInv_zero_eq_self {X : Type} [AddCommGroup X] [Module ℂ X] :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → X), KB.uInv (0 : ℂ) w x = x
  | [], _ => rfl
  | l :: w, x => by
    funext e
    have he : (Fin.cons (e 0) (fun a => e a.succ) : Wd.Ix (Fin (w.length + 1))) = e := Fin.cons_self_tail e
    simp only [KB.uInv, map_zero, ite_self, zero_smul, add_zero, uInv_zero_eq_self w]
    by_cases h0 : e 0 = 0
    · rw [if_pos h0]
      conv_rhs => rw [← he]
      rw [h0]
    · have h1 : e 0 = 1 := by
        rcases Fin.exists_fin_two.1 ⟨e 0, rfl⟩ with h | h
        · exact absurd h h0
        · exact h
      rw [if_neg h0]
      conv_rhs => rw [← he]
      rw [h1]

theorem waveG_zero_eq_self {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) : KB.waveG Bs 0 w x = x := by
  funext e g
  simp only [KB.waveG, uInv_zero_eq_self, P5.fsv, zero_mul, map_zero, sub_zero, Complex.exp_zero, one_smul]

theorem psiL_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (c : ℂ) : KB.psiL S 0 c = 1 := by
  simp [KB.psiL]

theorem intB_of (hPS : StandardPairingDecay.PStdC) (hD : DecayUnif) : IntB := by
  intro Cb
  obtain ⟨c1, h1⟩ := limit_of_module_forms Cb
  obtain ⟨c7, h7⟩ := hD Cb
  refine ⟨max c1 c7, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n
  have hB7 := PBJoint.built_setting_to_model_place (le_max_right c1 c7) hB
  have hB' := hB
  obtain ⟨-, -, -, hcut, -, -, -, -, -, -, hGo, -, -, -, hA, hv⟩ := hB'
  have hCI : KB.CutInside S := PBCut.cutInside_of_built hB
  have hgpos := PBL.g_pos_of_built hB
  have hcpt : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (cutSeq S p f χ n v ε) := by
    intro v ε hε
    obtain ⟨hl0, hInD, -, hCk, hCC⟩ := hv v
    refine (h1 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop cutN (by rw [hl0]; exact hInD)
      hcut hε hCk hCC (le_trans ?_ hA) (fun n g => rfl)).1 n
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
  intro v ε hε i hi1 hi2 w h h' hsz hsz'
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : j ≤ S.G.r := Nat.le_of_succ_le_succ hi2
  have hsz1 : D.ptSize h = j := hsz.trans (Nat.add_sub_cancel j 1)
  have hsz1' : D.ptSize h' = j := hsz'.trans (Nat.add_sub_cancel j 1)
  rw [Nat.add_sub_cancel]
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hw : KB.CutWord (D.parOf S v) (S.l + 1) (w.1 v) := PBD.cutWord_of_adm S hGo hCI w v
  have hi2' : j + 1 ≤ S.G.r + 1 := Nat.succ_le_succ hj
  have hadm : D.AdmAt S v (w.1 v) := ⟨w, rfl⟩
  have h7' := h7 E Wp Wq S p f χ A₀ hB7 v ε hε (j + 1) hi1 hi2' (w.1 v) hadm h h' hsz hsz'
  refine h7'.elim fun Cd hC => ?_
  have hdec := (hC n).1
  have hloc_app : ∀ (H : C.LPt) (c : ℂ), D.ptSize H = j → D.IsLocPt (H ++ [(1, c)]) (j + 1) → D.IsLocPt H j :=
    fun H c hH hl => ⟨fun b hb => hl.1 b (List.mem_append_left _ hb), hH⟩
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (PBL.stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (PBL.stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    have hPS' := hPS (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (cutSeq S p f χ n v ε) j hj (w.1 v)
      (PBL.stdS S h) (PBL.stdS S h') hH hH' Cb (by rw [hl0]; exact hInD) (hcpt v ε hε) (by rw [hl0]; exact hw)
    refine hPS'.elim fun φ0 hφ0all => ?_
    obtain ⟨hφ0c, -, hφ0, -⟩ := hφ0all
    have hlam := PBL.lamS_pos S hgpos j
    set φ : ℂ → ℂ := fun c => ((StandardPairingDecay.Kg S j h h' : ℝ) : ℂ) * φ0 ((PBL.lamS S j : ℂ) * c) with hφdef
    have hφc : Continuous φ := continuous_const.mul (hφ0c.comp (continuous_const.mul continuous_id))
    have hφeq : ∀ c : ℂ, c ≠ 0 → φ c = (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v)
        (h ++ [(1, c)]) (h' ++ [(1, c)]) := by
      intro c hc
      have hlc : (PBL.lamS S j : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam.ne') hc
      rw [StandardPairingDecay.gramLoc_setC_app hB (cutSeq S p f χ n) v ε j hj (w.1 v) h h' hh.2 hh'.2 c hc, hφdef]
      simp only
      rw [hφ0 _ hlc]
      ring
    refine ⟨φ, hφc, hφeq, ⟨Cd, fun c => ?_⟩, ?_⟩
    · exact PBB.K8.bound_all hφc (fun c hc => by rw [hφeq c hc]; exact hdec c hc) c
    · have hae : (fun c => φ c) =ᵐ[volume] fun c => (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v)
          (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S 0 c := by
        filter_upwards [PBL.ae_ne_zero_complex] with c hc
        rw [psiL_zero, mul_one, hφeq c hc]
      rw [integral_congr_ae hae, StandardPairingDecay.int_gramLoc_setC hPS hB (cutSeq S p f χ n) v ε (hcpt v ε hε) j hj (w.1 v) hw 0
        h h' hh hh']
      have hs0 : PBL.sW S j 0 = 0 := by simp [PBL.sW]
      rw [hs0, waveG_zero_eq_self, ← PBL.rr_eq_form (p v) _ j hj (w.1 v) _ _ hH hH']
      erw [PBL.gramLoc_setC hB]
      have hsA := PBL.sizeAt_pos S hGo v (w.1 v) hadm
      have hk := PBL.kc_scal hB v j hj (w.1 v) h h'
      have hrd := PBD.rd_pos' E
      have hδ : 0 < D.deG (S.g : ℝ) (S6.rd E) := by unfold D.deG; positivity
      have hdl : 0 < KB.dlB S (j + 1) 1 := by unfold KB.dlB; exact div_pos (zpow_pos hrd _) hδ
      have key : StandardPairingDecay.Kg S j h h' * |(PBL.lamS S j ^ 2)⁻¹| =
          KB.dlB S (j + 1) 1 * (√(PBL.nnS S h) * √(PBL.nnS S h') * (1 / (PBL.bS S h * PBL.bS S h' * PBL.ΓS S j))) := by
        unfold PBL.Kc PBL.dW at hk
        unfold StandardPairingDecay.Kg
        field_simp at hk ⊢
        linear_combination hk
      show ((StandardPairingDecay.Kg S j h h' * |(PBL.lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * _ = ((KB.dlB S (j + 1) 1 : ℝ) : ℂ) * _
      rw [key]
      push_cast
      ring
  · have hz : ∀ c : ℂ, (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
      intro c
      erw [PBL.gramLoc_setC hB, PBL.rr_zero_of_not, mul_zero]
      rintro ⟨h1, h2⟩
      refine hloc ⟨hloc_app h c hsz1 ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h1),
        hloc_app h' c hsz1' ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h2)⟩
    have hz0 : (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε j (w.1 v) h h' = 0 := by
      erw [PBL.gramLoc_setC hB, PBL.rr_zero_of_not, mul_zero]
      rintro ⟨h1, h2⟩
      exact hloc ⟨(PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h1, (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h2⟩
    refine ⟨fun _ => 0, continuous_const, fun c _ => (hz c).symm, ⟨0, fun c => by simp⟩, ?_⟩
    rw [hz0, integral_zero, mul_zero]

def IntBOfParts : Prop := StandardPairingDecay.PStdC → DecayUnif → IntB

theorem intBOfParts : IntBOfParts := intB_of

end

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

theorem integral_bound_of_parts : PBASM.IntBOfParts := PBASM.intBOfParts

end Formalism.FourierDecayAlt.P
