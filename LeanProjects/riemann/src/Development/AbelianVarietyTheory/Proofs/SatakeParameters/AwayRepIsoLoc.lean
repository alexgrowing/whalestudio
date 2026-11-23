import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCGal

open Formalism.MainNotions.SumRepresentations.At GlobalTheory.TwistLG

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a b : ℕ}

theorem sumRep_val (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl

theorem cont_sumRep [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k]
    (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k)
    (c : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (c' : Continuous fun g => ((ρ' g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) :
    Continuous fun g => ((sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) := by
  simp only [sumRep_val]
  exact (c.matrix_fromBlocks continuous_const continuous_const c').matrix_reindex _ _

theorem ss_sumRep (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (h : IsSSRep ρ) (h' : IsSSRep ρ') :
    IsSSRep (sumRep ρ ρ') := by
  refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod ((LinearEquiv.funCongrLeft k k finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) h h'
  rw [sumRep_val]
  ext i <;>
    simp [Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl

theorem ss_zero (ρ : Γ →* GL (Fin 0) k) : IsSSRep ρ := fun W _ =>
  ⟨⊥, fun g v hv => by simp [Subsingleton.elim v 0], by rw [Subsingleton.elim W ⊤]; exact isCompl_top_bot⟩

end Rep

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

def AwayRep (m : ℕ) (L : ∀ w, A.LP w) : Prop :=
  ∃ r : Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin m) (Qbar (N.l i)), ContQ N i r ∧ IsSSRep r ∧
    ∀ w, w ∉ placesOver H.E (N.l i) → A.wdOf i r w = L w

theorem eq_lpZero {w : PlE H} (x : A.LP w) (hu : A.unr x) (hd : A.lpDim x = 0) : x = A.lpZero w := by
  have h1 : A.frobEig x = 0 := Multiset.card_eq_zero.1 (by rw [A.frobEig_card _ hu, hd])
  have h2 := A.unr_eq_lpUnr _ (A.lpZero_unr w)
  rw [A.frobEig_zero] at h2
  rw [A.unr_eq_lpUnr _ hu, h1, h2]

theorem lpTw_lpZero (w : PlE H) (c : ℝ) : A.lpTw (A.lpZero w) c = A.lpZero w :=
  eq_lpZero N A _ ((A.unr_tw _ _).2 (A.lpZero_unr w)) (by rw [A.lpDim_tw, A.lpDim_zero])

theorem awayRep_zero : AwayRep N A i 0 A.lpZero := by
  refine ⟨1, continuous_const, ss_zero _, fun w hw => eq_lpZero N A _ ?_ (A.wdOf_dim i _ w)⟩
  exact (A.wdOf_unr i _ w hw continuous_const).2 fun σ _ => rfl

theorem AwayRep.congr {m m' : ℕ} {L L' : ∀ w, A.LP w} (h : AwayRep N A i m L) (hm : m = m')
    (hL : ∀ w, L w = L' w) : AwayRep N A i m' L' := by
  subst hm
  obtain ⟨r, c, s, f⟩ := h
  exact ⟨r, c, s, fun w hw => (f w hw).trans (hL w)⟩

theorem AwayRep.sum (hGal : TieGal N A) {m m' : ℕ} {L L' : ∀ w, A.LP w} (h : AwayRep N A i m L)
    (h' : AwayRep N A i m' L') : AwayRep N A i (m + m') fun w => A.lpSum (L w) (L' w) := by
  obtain ⟨r, c, s, f⟩ := h
  obtain ⟨r', c', s', f'⟩ := h'
  obtain ⟨-, -, hsum, -⟩ := hGal.2.2.2 i
  refine ⟨sumRep r r', cont_sumRep r r' c c', ss_sumRep r r' s s', fun w hw => ?_⟩
  rw [(hsum m m' r r' c c').2.1 w (Or.inl hw) (Or.inl hw), f w hw, f' w hw]

theorem param_int (hLP : TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) (u t : ℝ) :
    A.lpChar (A.lpChar (A.lpTw (A.locG π w) u) (A.lpTw (A.locG A.etaT w) (1 / 2)))
      (A.lpTw (A.locG A.etaTinv w) (t - 1 / 2)) = A.lpTw (A.locG π w) (u + t) := by
  have d1 : A.lpDim (A.locG A.etaT w) = 1 := A.locG_dim _ w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  set X := A.lpTw (A.locG π w) u
  have c3a := (hLP w (A.lpChar X (A.lpTw (A.locG A.etaT w) (1 / 2))) (A.lpZero w) (A.locG A.etaTinv w)
    (A.locG A.etaTinv w) (t - 1 / 2) d2 d2).2.2.1
  have c3b := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaT w) (1 / 2) d1 d1).2.2.1
  have c2 := (hLP w (A.lpChar X (A.locG A.etaT w)) (A.lpZero w) (A.locG A.etaTinv w) (A.locG A.etaTinv w)
    (1 / 2) d2 d2).2.1
  have c4 := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.1
  have c5 := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.2.1
  rw [c3a, c3b, c2, c4, etaT_char_etaTinv N A w, c5, A.lpTw_add, A.lpTw_add]
  congr 1
  ring

end Glob

section Piece

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem eta_alg (hAut : TieAut N A) (m : ℤ) (τ : H.E →+* ℂ) :
    (∀ z ∈ A.infG A.etaT τ, ∃ k : ℤ, z + (((m : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ)) ∧
    (∀ z ∈ A.infG A.etaTinv τ, ∃ k : ℤ, z + (((m : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ)) := by
  obtain ⟨h1, h2⟩ := hAut.2.1 τ
  rw [h2]
  rcases h1 with h1 | h1 <;> rw [h1] <;> refine ⟨fun z hz => ?_, fun z hz => ?_⟩ <;>
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hz <;> subst hz
  · exact ⟨m + 1, by push_cast; ring⟩
  · exact ⟨m, by push_cast; ring⟩
  · exact ⟨m, by push_cast; ring⟩
  · exact ⟨m + 1, by push_cast; ring⟩

theorem awayRep_piece (hLP : TieLP N A) (hAut : TieAut N A) (hGal : TieGal N A) (hG : exists_galois_rep_local_global_compatible N A)
    {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) (hc : A.csd π) (m : ℤ)
    (hinf : ∀ τ, (A.infG π τ).Nodup ∧
      ∀ z ∈ A.infG π τ, ∃ n : ℤ, z + (((m : ℝ) / 2 : ℝ) : ℂ) = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    AwayRep N A i a fun w => A.lpTw (A.locG π w) ((m : ℝ) / 2 + (1 - (a : ℝ)) / 2) := by
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
      (away1 w hw).1, awayA w hw, awayB w hw, param_int N A hLP]
    congr 1
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
    rw [(htw a ρ1 χ1 c1 cχ).2.1 w (Or.inl hw) (Or.inl hw), (away1 w hw).1, awayχ w hw, param_twist N A hLP]
    congr 1
    push_cast
    ring

end Piece

section List

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem awayRep_isoLoc (hGal : TieGal N A) (c : ℝ) (Pa : List (Part A.CG))
    (h : ∀ p ∈ Pa, ∀ k < p.d, AwayRep N A i p.a fun w =>
      A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + c)) :
    AwayRep N A i (rankIso N A Pa) fun w => A.lpTw (isoLoc N A Pa w) c := by
  induction Pa with
  | nil =>
    exact (awayRep_zero N A i).congr N A i rfl fun w => (lpTw_lpZero N A w c).symm
  | cons p Pa ih =>
    have h1 : ∀ ks : List ℝ, (∀ k ∈ ks, ∃ n : ℕ, n < p.d ∧ (n : ℝ) = k) → AwayRep N A i (p.a * ks.length)
        fun w => A.lpTw (ks.foldr
        (fun (k : ℝ) acc => A.lpSum (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) acc) (A.lpZero w)) c := by
      intro ks hks
      induction ks with
      | nil => exact (awayRep_zero N A i).congr N A i (by simp) fun w => (lpTw_lpZero N A w c).symm
      | cons k ks ihk =>
        obtain ⟨n, hn, rfl⟩ := hks k List.mem_cons_self
        refine ((h p List.mem_cons_self n hn).sum N A i hGal
          (ihk fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))).congr N A i
          (by rw [List.length_cons, mul_add, mul_one, add_comm]) fun w => ?_
        rw [List.foldr_cons, A.lpTw_sum, A.lpTw_add]
    have h2 := h1 ((List.range p.d : List ℕ) : List ℝ) fun k hk => by
      simp [Lean.Internal.coeM] at hk
      obtain ⟨n, hn, rfl⟩ := hk
      exact ⟨n, hn, rfl⟩
    refine (h2.sum N A i hGal (ih fun q hq => h q (List.mem_cons_of_mem _ hq))).congr N A i
      (by simp [rankIso, Lean.Internal.coeM]) fun w => ?_
    simp only [isoLoc, spehLoc, List.foldr_cons, A.lpTw_sum]

end List

theorem main : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.adm2 D → Formalism.MainNotions.SumRepresentations.adm7 D → ∀ i, GalIso D.nd D.naut i := by
  intro D hT hG _ i P Pa hB
  obtain ⟨hLP, hAut, hGal⟩ := hT
  have hreal := awayRep_isoLoc D.nd D.naut i hGal ((1 - (D.R.nV : ℝ)) / 2) Pa fun p hp k hk => by
    obtain ⟨ha, -, hc⟩ := hB.1 p hp
    refine (awayRep_piece D.nd D.naut i hLP hAut hGal hG ha p.π hc
      ((p.d : ℤ) - 1 - 2 * k + p.a - D.R.nV) fun τ => ?_).congr D.nd D.naut i rfl fun w => ?_
    · have hW : (D.naut.infWt i τ).Nodup ∧
          ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
        rw [D.nbc.embAV_inf i P]
        exact D.nbc.infW_alg _ _ τ
      have hle : (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k)) ≤ D.naut.infWt i τ := by
        rw [← hB.2.2.2.2.2 τ]
        refine le_trans (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ ?_)
          (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
        exact List.mem_map.2 ⟨k, by simpa using hk, rfl⟩
      refine ⟨(Multiset.nodup_of_le hle hW.1).of_map _, fun z hz => ?_⟩
      obtain ⟨n, hn⟩ := hW.2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz))
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    · congr 1
      push_cast
      ring
  exact (hreal.congr D.nd D.naut i hB.2.2.1 fun _ => rfl)

end GlobalTheory.BCGal

end
