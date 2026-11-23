import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOOneResGCompl
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LawStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumFixesLatticeVacuaAtInertPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharTrivialOnIdempotentIntegralUnits
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)
noncomputable section

namespace GlobalTheory.TopLevelInv

section Unr

variable {D : D7}

theorem unrOff_mul' {e : AE D} {χ χ' : (AE D)ˣ →* Circle} (h : Formalism.IndefR.Fin.UnrOff e χ)
    (h' : Formalism.IndefR.Fin.UnrOff e χ') : Formalism.IndefR.Fin.UnrOff e (χ * χ') :=
  fun x h1 h2 h3 h4 => by rw [MonoidHom.mul_apply, h x h1 h2 h3 h4, h' x h1 h2 h3 h4, one_mul]

theorem unrOff_inv' {e : AE D} {χ : (AE D)ˣ →* Circle} (h : Formalism.IndefR.Fin.UnrOff e χ) :
    Formalism.IndefR.Fin.UnrOff e χ⁻¹ :=
  fun x h1 h2 h3 h4 => by rw [MonoidHom.inv_apply, h x h1 h2 h3 h4, inv_one]

theorem pg_near_locPl {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    {PP : Pl D.host.E} (h : PP ∈ L.Pg) : ∃ w ∈ locPl G t, PP = w ∨ PP = GlobalTheory.IdemSupport.cP w := by
  classical
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
  have hm := GlobalTheory.LevelRamif.typePrime_mem hk
  set v := PP.under (𝓞 D.host.F) with hv
  have hvk : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal
    rwa [map_natCast]
  have hS1 : v ∈ S1 D := by
    rw [S1_mem_OmF]
    fin_cases k
    · exact Or.inl hvk
    · exact Or.inr (Or.inl hvk)
  have hS0 : v ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr hS1)
  refine ⟨G.pl.w v, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hS0), ?_⟩
  exact GlobalTheory.IdemSupport.eq_or_eq_cP (by rw [G.pl.under_w hS0])

theorem conjPrime_conjPrime₂ (P : HeightOneSpectrum (𝓞 D.host.E)) : GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO])

theorem unrOff_mu_locPl {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t μ₀ : T}
    (hL : L.Is μ₀) (j : Fin D.R.m) {e : AE D} (he : IsIdemSum e (locPl G t)) :
    Formalism.IndefR.Fin.UnrOff e (L.mu t ((j : ℕ) + 1)) ∧ Formalism.IndefR.Fin.UnrOff e L.eta := by
  classical
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.LevelRamif.ramif_at_levels D T L μ₀ hL t j
  have hmu : Formalism.IndefR.Fin.UnrOff e (L.mu0 ((j : ℕ) + 1)) :=
    GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e (hL.mu0 j) he fun PP' h1 h2 => by
      refine h4 PP' (fun h => ?_) fun PP h h' => ?_
      · obtain ⟨w, hw, hw'⟩ := pg_near_locPl G hL t h
        rcases hw' with rfl | rfl
        · exact h1 hw
        · exact h2 w hw ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 rfl)
      · obtain ⟨w, hw, hw'⟩ := pg_near_locPl G hL t h
        have e1 := (GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h'
        rcases hw' with rfl | rfl
        · exact h2 PP hw h'
        · rw [conjPrime_conjPrime₂] at e1
          exact h1 (e1 ▸ hw)
  have hxi : Formalism.IndefR.Fin.UnrOff e (L.xi t) :=
    GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e (hL.xi t) he fun PP' h1 h2 => by
      by_contra hn
      rcases (hL.Q_ram t PP').1 hn with h | ⟨PP, h, h'⟩
      · exact h1 (Finset.mem_union_right _ h)
      · exact h2 PP (Finset.mem_union_right _ h) h'
  exact ⟨unrOff_mul' hmu hxi, GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e hL.eta he fun PP' _ _ => L.C.isEta.unr PP'⟩

end Unr

set_option maxHeartbeats 1000000 in

theorem vacFix_conjPt_off : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.top (j + 1))), finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj →
    ∀ e : AE D, IsIdemSum e (locPl G t) → ∀ ε : AF D.host.F, IsIdempotentElem ε →
    algebraMap (AF D.host.F) (AE D) ε = e + cA D e →
    W.om (.top t j) (1, resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) (S.Z.vac (.top t j)) =
      S.Z.vac (.top t j) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he ε hε halg
  have hε' : IsIdempotentElem (1 - ε) := hε.one_sub
  have hdp : DefPair D.R.m (.top t j : Pair T) := by show j + 1 ≤ D.R.m; omega
  have hW := W.om_is (.top t j) (by simp only [Pair.InRange, Node.InRange]; omega)
  have hv := S.Z.vac_is _ hdp
  have hdS : DefNode D.R.m (.top j) := by show j ≤ D.R.m; omega
  have hdT : DefNode D.R.m (.top (j + 1)) := by show j + 1 ≤ D.R.m; omega
  have hS := S.N.selfDual (X := .top j) hdS
  have hT := S.N.selfDual (X := .top (j + 1)) hdT
  have hfS := GlobalTheory.OffPartLattice.isFrame_moved (colLat (S.N.fr (.top j))) (G.Λ (.top j)) (S.βp j)
    (Lev.finE (G.V (.top j)) (S.N.u (.top j)).1) (S.βp_is j hdS) (S.N.u_lat _ hdS)
  have hfT := GlobalTheory.OffPartLattice.isFrame_moved (colLat (S.N.fr (.top (j + 1)))) (G.Λ (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (S.βp_is (j + 1) hdT) (S.N.u_lat _ hdT)
  have hrkS : (G.V (.top j)).rank = rankX D j := (G.isV (X := .top j) hdS fun _ e => by cases e).rank
  have hrkT : (G.V (.top (j + 1))).rank = rankX D (j + 1) := (G.isV (X := .top (j + 1)) hdT fun _ e => by cases e).rank
  have hrk : (G.V (.top j)).rank ≠ (G.V (.top (j + 1))).rank := by
    intro h
    rw [hrkS, hrkT] at h
    simp only [rankX, add_mul, one_mul] at h
    omega
  have hev : Even (G.V (.top j)).rank := hrkS ▸ even_rankX D j
  obtain ⟨hμ, hη⟩ := unrOff_mu_locPl G hL ⟨j, by omega⟩ he
  have hatt : ∀ n, Formalism.IndefR.Fin.UnrOff e (Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta n) := by
    intro n
    unfold Formalism.IndefR.Lift.attChr
    split_ifs
    · exact unrOff_mul' hμ (unrOff_inv' hη)
    · exact hμ
  have hn : ∃ (μ : Measure (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (𝓕 : Set (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)))),
      IsCovolOne (ratL (G.pT (.top t j : Pair T)) (G.pS (.top t j : Pair T))) μ 𝓕 ∧
        nrm2 μ 𝓕 (S.Z.vac (.top t j)) = 1 := by
    obtain ⟨⟨p, hp⟩, hall⟩ := hv.2.norm
    exact ⟨p.1, p.2, hp, hall p hp⟩

  have hf := GlobalTheory.ExpansionInvariance.idem_conj_sum (GlobalTheory.PlaceVec.idemSum_mul_self he) he.2
  have h2 := GlobalTheory.ExpansionInvariance.idem_compl hf
  have hcut : resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k) =
      GlobalTheory.ExpansionInvariance.cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) (conjPt S j k) := by
    apply Formalism.IndefR.Fin.LevelGroupLemmas.gaExt
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG _ hε', GlobalTheory.ExpansionInvariance.mt_cutPart h2.1 h2.2, map_sub, map_one, halg]
    unfold Formalism.IndefR.Fin.LevelGroupLemmas.resM
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hSt : Lev.finE (G.V (.top (j + 1))) (resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) ∈
      St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) := by
    have hk2 : finG (G.V (.top (j + 1))) k ∈ prodLev (S.βp (j + 1)) (locPl G t) (fun w => topRank_eq G t w hj.le)
        (fun w => (S.term t Φ β w).pr _ j.succ_pos hj) := hk
    rw [hcut]
    exact GlobalTheory.OffPartLattice.finE_cut_mem_St (G.V (.top (j + 1))) (S.βp (j + 1))
      (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (finG (G.V (.top (j + 1))) k) (conjPt S j k)
      (by simp only [conjPt, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]; rfl) he (fun Q hQ => by
        have h3 := (Subgroup.mem_inf.1 hk2).2
        rw [Subgroup.mem_iInf] at h3
        have h4 := h3 Q
        rw [Subgroup.mem_iInf] at h4
        exact Subgroup.mem_comap.1 (h4 hQ))
  have hP : ∀ a b, (e + cA D e) * (mt (G.V (.top (j + 1))) (resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) - 1) a b = 0 := by
    intro a b
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG_sub hε' _ a b, ← mul_assoc, map_sub, map_one, halg]
    have h0 : (e + cA D e) * (1 - (e + cA D e)) = 0 := by
      linear_combination (-1 : AE D) * hf.1
    rw [h0, zero_mul]
  exact Formalism.IndefR.Fin.LevelGroupLemmas.vacFixOff (Formalism.IndefR.Fin.splitLinF D) (Formalism.IndefR.Fin.placeModelAtF D)
    (Formalism.IndefR.Fin.splitOrInert D) W.ψ _ _ _ _ _ hW (GlobalTheory.InertAll.inertAllO D _ _ _ _ _ _ hW) hrk (Or.inl hev) _ _ hS hT _ _
    hfS hfT (locPl G t) e he (hatt _) (hatt _) _ hv.2.theta hv.2.lat hn 1 _ (one_mem _)
    (Formalism.IndefR.Fin.LevelGroupLemmas.resG_mem_GfC _ hε' (SetLike.coe_mem _)) (by rw [map_one]; exact one_mem _) hSt
    (fun a b => by rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_one', sub_self, Matrix.zero_apply, mul_zero]) hP

end GlobalTheory.TopLevelInv
