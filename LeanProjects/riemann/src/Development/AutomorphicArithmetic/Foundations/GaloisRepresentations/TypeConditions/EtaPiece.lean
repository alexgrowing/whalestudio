import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCGal

open Formalism.MainNotions.SumRepresentations.At GlobalTheory.TwistLG

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem awayRepN_zero_lpZero : UpperTheory.GalS.AwayRepN N A i 0 A.lpZero := by
  refine ⟨1, continuous_const, ss_zero _, fun w hw _ => eq_lpZero N A _ ?_ (A.wdOf_dim i _ w)⟩
  exact (A.wdOf_unr i _ w hw continuous_const).2 fun σ _ => rfl

theorem awayRepN_congr {m m' : ℕ} {L L' : ∀ w, A.LP w} (h : UpperTheory.GalS.AwayRepN N A i m L) (hm : m = m')
    (hL : ∀ w, L w = L' w) : UpperTheory.GalS.AwayRepN N A i m' L' := by
  subst hm
  obtain ⟨r, c, s, f⟩ := h
  exact ⟨r, c, s, fun w hw => hL w ▸ f w hw⟩

theorem liftSetupOverExtendedData_classSum_eq (hGal : TieGal N A) {m m' : ℕ} {L L' : ∀ w, A.LP w} (h : UpperTheory.GalS.AwayRepN N A i m L)
    (h' : UpperTheory.GalS.AwayRepN N A i m' L') : UpperTheory.GalS.AwayRepN N A i (m + m') fun w => A.lpSum (L w) (L' w) := by
  obtain ⟨r, c, s, f⟩ := h
  obtain ⟨r', c', s', f'⟩ := h'
  obtain ⟨-, -, hsum, -⟩ := hGal.2.2.2 i
  refine ⟨sumRep r r', cont_sumRep r r' c c', ss_sumRep r r' s s', fun w hw hu => ?_⟩
  rw [(hsum m m' r r' c c').2.1 w (Or.inl hw) (Or.inl hw)]
  rw [f w hw ((A.unr_sum _ _).1 hu).1, f' w hw ((A.unr_sum _ _).1 hu).2]

theorem galois_relation_away_from_l (hLP : TieLP N A) (hAut : TieAut N A) (hGal : TieGal N A) (hG : UpperTheory.GalS.AutomorphicGaloisAdmissible N A)
    {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) (hc : A.csd π) (m : ℤ)
    (hinf : ∀ τ, (A.infG π τ).Nodup ∧
      ∀ z ∈ A.infG π τ, ∃ n : ℤ, z + (((m : ℝ) / 2 : ℝ) : ℂ) = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    ∃ r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)), ContQ N i r ∧ IsSSRep r ∧ ∀ w, w ∉ placesOver H.E (N.l i) →
      UpperTheory.GalS.RelW N A (A.wdOf i r w) (A.lpTw (A.locG π w) ((m : ℝ) / 2 + (1 - (a : ℝ)) / 2)) := by
  obtain ⟨-, -, -, htw⟩ := hGal.2.2.2 i
  rcases Int.even_or_odd' m with ⟨k, hk | hk⟩ <;> subst hk
  ·
    have hralg : A.ralg π := (A.ralg_def π).2 fun τ => ⟨(hinf τ).1, fun z hz => by
      obtain ⟨n, hn⟩ := (hinf τ).2 z hz
      exact ⟨n - k, by push_cast at hn ⊢; linear_combination hn⟩⟩
    obtain ⟨ρ1, c1, ss1, away1, -⟩ := (hG i).1 a ha π hc hralg
    obtain ⟨χA, cA, awayA, -⟩ := (hG i).2.2 A.etaT (1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut 0 τ).1 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    obtain ⟨χB, cB, awayB, -⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) - 1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut (k - 1) τ).2 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    let ρ2 := twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χA)
    have c2 : ContQ N i ρ2 := cont_twGL ρ1 χA c1 cA
    refine ⟨twGL ρ2 (Matrix.GeneralLinearGroup.det.comp χB), cont_twGL ρ2 χB c2 cB,
      isSSRep_twGL _ _ (isSSRep_twGL _ _ ss1), fun w hw => ?_⟩
    rw [(htw a ρ2 χB c2 cB).2.1 w (Or.inl hw) (Or.inl hw), (htw a ρ1 χA c1 cA).2.1 w (Or.inl hw) (Or.inl hw),
      awayA w hw, awayB w hw]
    have k1 := ((away1 w hw).char hLP (A.lpTw (A.locG A.etaT w) (1 / 2)) (by rw [A.lpDim_tw, A.locG_dim])
      ((A.unr_tw _ _).2 (A.etaT_unr w))).char hLP (A.lpTw (A.locG A.etaTinv w) ((k : ℝ) - 1 / 2))
      (by rw [A.lpDim_tw, A.locG_dim]) ((A.unr_tw _ _).2 (A.etaTinv_def w).1)
    rw [param_int N A hLP] at k1
    convert k1 using 2
    push_cast
    ring
  ·
    have hcsd : A.csd (A.tw π A.etaT) := A.csd_tw π A.etaT hAut.1.1 hc
    have hralg : A.ralg (A.tw π A.etaT) := (A.ralg_def _).2 fun τ => by
      obtain ⟨e, he⟩ := Multiset.card_eq_one.mp (A.infG_card A.etaT τ)
      rw [A.infG_tw π A.etaT τ e he]
      refine ⟨(hinf τ).1.map (add_left_injective e), fun y hy => ?_⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      obtain ⟨n, hn⟩ := (hinf τ).2 z hz
      obtain ⟨j, hj⟩ := (eta_alg N A hAut 0 τ).1 e (by rw [he]; exact Multiset.mem_singleton_self e)
      exact ⟨n + j - k - 1, by push_cast at hn hj ⊢; linear_combination hn + hj⟩
    obtain ⟨ρ1, c1, ss1, away1, -⟩ := (hG i).1 a ha _ hcsd hralg
    obtain ⟨χ1, cχ, awayχ, -⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) + 1 / 2) (eta_alg N A hAut k · |>.2)
    refine ⟨twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χ1), cont_twGL ρ1 χ1 c1 cχ, isSSRep_twGL _ _ ss1,
      fun w hw => ?_⟩
    rw [(htw a ρ1 χ1 c1 cχ).2.1 w (Or.inl hw) (Or.inl hw), awayχ w hw]
    have k1 := (away1 w hw).char hLP (A.lpTw (A.locG A.etaTinv w) ((k : ℝ) + 1 / 2))
      (by rw [A.lpDim_tw, A.locG_dim]) ((A.unr_tw _ _).2 (A.etaTinv_def w).1)
    rw [param_twist N A hLP] at k1
    convert k1 using 2
    push_cast
    ring

theorem awayRep_piece_alt (hLP : TieLP N A) (hAut : TieAut N A) (hGal : TieGal N A) (hG : UpperTheory.GalS.AutomorphicGaloisAdmissible N A)
    {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) (hc : A.csd π) (m : ℤ)
    (hinf : ∀ τ, (A.infG π τ).Nodup ∧
      ∀ z ∈ A.infG π τ, ∃ n : ℤ, z + (((m : ℝ) / 2 : ℝ) : ℂ) = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    UpperTheory.GalS.AwayRepN N A i a fun w => A.lpTw (A.locG π w) ((m : ℝ) / 2 + (1 - (a : ℝ)) / 2) := by
  obtain ⟨r, c, s, f⟩ := galois_relation_away_from_l N A i hLP hAut hGal hG ha π hc m hinf
  exact ⟨r, c, s, fun w hw => (f w hw).eq_of_unr⟩

end GlobalTheory.BCGal
