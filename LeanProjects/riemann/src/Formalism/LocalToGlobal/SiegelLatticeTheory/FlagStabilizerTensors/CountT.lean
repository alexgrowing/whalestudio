import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.CovolumeGaugeFrames
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarVolPf
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DegreeRatioFormulaStatement

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.StandardLattice

namespace Formalism.L2.SG.ThmSOwn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def InstTie (I : AutInst) : Prop :=
  ∃ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (P Q : ℕ),
    I = Formalism.IndefR.Eqv.UI.instV fr ∧ fr.Λ = Formalism.IndefR.Eqv.UI.Lv D V ∧
    (∀ v, (Finset.univ.filter fun i => fr.ε v i = true).card = P) ∧ V.SigOK ∧ (∀ τ, V.sig τ = (P, Q)) ∧
    VolTie D ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep D ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D V.rank ∧ cdScaleTie D

theorem instTie_of_inst {D : D7} {I : AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (hSig : (VS D).SigOK) (Q : ℕ)
    (hs : ∀ τ, (VS D).sig τ =
      ((Finset.univ.filter fun i => Formalism.L2.SG.InstExistsPf.epsV D i = true).card, Q))
    (hV : VolTie D) (hI : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep D) (hC : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D (VS D).rank)
    (hcd : cdScaleTie D) : InstTie I :=
  ⟨D, VS D, Formalism.L2.SG.Pf.DstarVolPf.frOf D, _, Q, h, rfl, fun _ => rfl, hSig, hs, hV, hI, hC, hcd⟩

def PLevT : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop :=
  fun I μf g₀ e => I.IsLevelCharIdem μf g₀ e ∧ InstTie I

theorem rowsTiePT_of {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) (hI : InstTie T.X.B.I) :
    CountE.RowsTieP PLevT D T.X.B :=
  ⟨(rowsTieP_of T).1, (rowsTieP_of T).2, hI⟩

def qqI (I : AutInst) : ℕ := Finset.univ.sup fun v => Formalism.MainNotions.PlaceDegreeData.q0At I v

def PLevT' : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop :=
  fun I μf g₀ e => PLevT I μf g₀ e ∧ 1 ≤ qqI I

theorem rowsTiePT'_of {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) (hI : InstTie T.X.B.I) (hq : 1 ≤ qqI T.X.B.I) :
    CountE.RowsTieP PLevT' D T.X.B :=
  ⟨(rowsTieP_of T).1, ⟨(rowsTieP_of T).2, hI⟩, hq⟩

theorem instTie_of_record {D : D7} {I : AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (hV : VolTie D)
    (hI : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep D) (hC : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D (VS D).rank) (hcd : cdScaleTie D) :
    InstTie I :=
  instTie_of_inst h (D.sp.Y_sig 0) (D.R.rS + 1)
    (fun τ => by rw [Formalism.L2.SG.InstExistsPf.card_epsV D]; exact D.sp.baseSpace_signature_eq τ) hV hI hC hcd

theorem one_le_qqI_instOf (D : D7) : 1 ≤ qqI (Formalism.L2.SG.InstExistsPf.instOf D) := by
  have hk := Formalism.MainNotions.BridgeLemma.five_le_k D
  obtain ⟨v⟩ : Nonempty (NumberField.InfinitePlace (Formalism.L2.SG.InstExistsPf.instOf D).F) := inferInstance
  refine le_trans ?_ (Finset.le_sup (f := fun v => Formalism.MainNotions.PlaceDegreeData.q0At (Formalism.L2.SG.InstExistsPf.instOf D) v)
    (Finset.mem_univ v))
  have ht : (Formalism.L2.SG.InstExistsPf.instOf D).pAt v = D.R.k + D.R.rS := Formalism.L2.SG.InstExistsPf.card_epsV D
  have hn : (Finset.univ : Finset (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n)).card = D.R.k + 2 * D.R.rS + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact (Formalism.L2.SG.InstExistsPf.rank_eq D).trans (Formalism.MainNotions.BridgeLemma.sza_r_eq D)
  have hq : 1 ≤ (Formalism.L2.SG.InstExistsPf.instOf D).qAt v := by
    unfold AutInst.qAt
    apply Finset.card_pos.mpr
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
    have hall : (Finset.univ.filter fun a => (Formalism.L2.SG.InstExistsPf.instOf D).ε v a = true) = Finset.univ :=
      Finset.filter_true_of_mem fun a _ => by
        cases h : (Formalism.L2.SG.InstExistsPf.instOf D).ε v a
        · exact absurd h (hne (Finset.mem_univ a))
        · rfl
    have := congrArg Finset.card hall
    unfold AutInst.pAt at ht
    rw [ht, hn] at this
    omega
  show 1 ≤ min _ _
  exact le_min (by rw [ht]; omega) hq

theorem one_le_qqI_of_inst {D : D7} {I : AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D) : 1 ≤ qqI I := by
  rw [h]; exact one_le_qqI_instOf D

theorem linkS_concreteEvP (P : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop)
    (𝒞 : FamClass) (C0 : ℝ) (c30 : List ℝ → CountingConstants) (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hRows : Closed 𝒞 fun Fm _ => ∃ xR : ℝ, ∀ x ≥ xR, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut,
      CountE.RowsTieP P (Fm.D x i) X)
    (hK1 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppOff D)
    (hK2 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppDiag D)
    (hK3 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D L => ClOff D L)
    (hK4 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClDiag D)
    (S30 : Closed 𝒞 fun Fm _ => CountE.ShareFamilyAtConstant P Fm (c30 Fm.cOut).Cres (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).Cb (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (A30 : Closed 𝒞 fun Fm _ => PlaceDegreeData.AdmF Fm (c30 Fm.cOut).Cres) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  closed_of_large (linkThresholds (fun _ => caZero) c30)
    (hRes.and (hRows.and (hK1.and (hK2.and (hK3.and (hK4.and (S30.and A30)))))))
    fun Fm CH hL h a0 => by
      obtain ⟨-, g2, g3, g4⟩ := link_thresholds_spec Fm CH (fun _ => caZero) c30 hL
      obtain ⟨a1, a2, k1, k2, k3, k4, a6, a7⟩ := h
      exact linkS_of_thmSPEv P Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 _ _ _ _ _ _ _ h1
        (hc30 Fm).1 (hc30 Fm).2 g2 g3 (standing_hypotheses_hold_family Fm C0 h1 ⟨g4, a0, a1⟩) a2 (thmSOwn_of_clauses k1 k2 k3 k4) a6 a7

variable (C0 : ℝ)

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in

theorem theoremS_link_transport_zero (𝒞 : FamClass) (sel : SSel 𝒞)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (hLoc : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.SG.Pf.LocCP.LocTied (Fm.D x i))
    (hInst : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      InstTie ((sel Fm hc).2 x hx h0 i).X.B.I)
    (hTF : Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0)
    (c30 : List ℝ → CountingConstants) (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hTy : Formalism.L2.SG.KappaOffDiagonal.TypeC) (hNG : Formalism.L2.SG.RowsConc.RowNGC) (hM : Formalism.L2.SG.RowsConc.RowMainEqC)
    (hLp : LoopRowS C0 𝒞 sel)
    (hO : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, TheoremSSelected Fm C0 (sel Fm hc))
    (S30 : Closed 𝒞 fun Fm _ => CountE.ShareFamilyAtConstant PLevT Fm (c30 Fm.cOut).Cres (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).Cb (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (A30 : Closed 𝒞 fun Fm _ => PlaceDegreeData.AdmF Fm (c30 Fm.cOut).Cres) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  have hFX := Formalism.L2.SG.Pf.finXC_of hWu hRF
  have hOK := selOK_of C0 hFX hWu sel hLoc hTF
  have hE : Closed 𝒞 fun Fm _ => ConcEv C0 Fm :=
    closed_with hOK (fun _ => 0) (fun _ => 0) fun Fm _ hc h _ _ _ => concEv_of_sel C0 (h hc)
  have hRows : Closed 𝒞 fun Fm _ => ∃ xR : ℝ, ∀ x ≥ xR, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut,
      CountE.RowsTieP PLevT (Fm.D x i) X :=
    closed_of_th (fun _ => 0) (fun _ => 0) fun Fm _ hc _ _ _ =>
      ⟨(sel Fm hc).1, fun x hx0 hx i => ⟨_, rowsTiePT_of ((sel Fm hc).2 x hx hx0 i) (hInst Fm hc x hx hx0 i)⟩⟩
  linkS_concreteEvP PLevT 𝒞 C0 c30 h1 hc30 hRes hRows (hypOwnE_kppOff C0 Formalism.L2.SG.Closed.KppOffC_holds hE)
    (hypOwnE_kppDiag C0 (Formalism.L2.SG.KappaOffDiagonal.kloostermanDiagonal_of_type hTy) absConvTied_holds hE)
    (hypOwnS_off C0 Formalism.L2.SG.Closed.KppOffC_holds kExpTied_holds absConvTied_holds sel hOK hO)
    (closed_clDiag_of_selOK C0 (Formalism.L2.SG.RowsConc.diagonal_contribution_of_equal_words hNG hM) kExpTied_holds absConvTied_holds sel hOK hLp) S30 A30

end Formalism.L2.SG.ThmSOwn
