import Formalism.HermitianCurvature.HermitianCurvatureProofs.PlaceSwapExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFHatProdKBStmt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThresholdOfLargeConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds

namespace CompanionTheory.WaveGrid.EqShift

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix
  MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem placeSwap_dd : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (P : M.Par) (Wp Wq Wq' : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    (p : KB.Pl P Wp Wq) (u'' : ℕ → ℝ) (π'' : B.Mat P.k P.r → (Wq' →L[ℂ] Wq')) (l0 : ℕ),
    Q.IsType P.k P.r p.T.base.z' π'' u'' → (shP P P.u u'').OK → 1 ≤ l0 → l0 ≤ P.k →
    ∃ q : KB.Pl (shP P P.u u'') Wp Wq', SwapTie p q ∧ q.T.base.π' = π'' ∧ q.l0 = l0 ∧
      KB.InDDplus2 (shP P P.u u'') q.l0 q.T.base Cb q.Θ := by
  obtain ⟨Cb, hCb, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, hCb, ?_⟩
  intro P Wp Wq Wq' _ _ _ _ _ _ _ _ _ p u'' π'' l0 hty hOK hl1 hl2
  obtain ⟨q, htie, hπ, hl⟩ := place_swap_exists P Wp Wq Wq' p u'' π'' l0 hty hOK hl1 hl2
  obtain ⟨X, μ, L, st, hD, -⟩ := q.hΘ
  obtain ⟨Θ, hI, hDD⟩ := hTL Wp Wq' (shP P P.u u'') q.T.base X μ L st q.l0 q.hl.1 q.hl.2.1 hD
  exact ⟨{ q with Θ := Θ, hΘ := ⟨X, μ, L, st, hD, hI⟩ }, htie, hπ, hl, hDD⟩

section swap

variable {k r : ℕ} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']

theorem jf_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (hπ : Ds'.π = Ds.π) (hW : Ds'.μW = Ds.μW) (hN : Ds'.μN = Ds.μN)
    (hW' : Ds'.μW' = Ds.μW') (A : B.Mat k r → (Wq' →L[ℂ] Wq)) (hA : WigEquiv Ds.z Ds.z' Ds.π' Ds'.π' A)
    (f : B.Mat k r → (Wq →L[ℂ] Wp)) {A₀ : ℝ} (hThr : JF.TransportedAlt k r A₀ 0) (hf : B.InCC A₀ 0 f)
    {γ : B.Mat k r} (hγ : γ ∈ JF.Om k r Ds.z Ds.z') :
    B.JF Ds' (fun g => (f g).comp (A g)) γ = (B.JF Ds f γ).comp (A γ) := by
  set L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq' →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq' Wq Wp).flip (A γ) with hL
  have hi0 := (bessel_integral_converges k r Wp Wq Ds A₀ f hThr hf).1 γ hγ
  have hi : Integrable (fun q => D.orbIntegrand Ds γ f q) Ds.μSS := by
    refine hi0.congr (ae_of_all _ fun q => ?_)
    unfold JF.integrand D.orbIntegrand
    rw [xi_eq_xiTau_one_one]
  have hae : ∀ᵐ q ∂Ds.μSS, D.orbIntegrand Ds' γ (fun g => (f g).comp (A g)) q = L (D.orbIntegrand Ds γ f q) := by
    filter_upwards [TBBx2.ae_inSS Ds] with q hq
    rw [orbIntegrand_swap Ds Ds' hz hz' hπ A hA f γ hγ.1 hγ.2.2 q hq]
    rfl
  rw [← bessel_function_trivial_index k r Wp Wq' Ds' _ γ, ← bessel_function_trivial_index k r Wp Wq Ds f γ]
  change ∫ q, D.orbIntegrand Ds' γ (fun g => (f g).comp (A g)) q ∂Ds'.μSS =
    L (∫ q, D.orbIntegrand Ds γ f q ∂Ds.μSS)
  rw [muSS_swap Ds Ds' hW hN hW', integral_congr_ae hae, L.integral_comp_comm hi]

theorem jf_ff_of_smooth (Db : B.RealPlaceData k r Wp Wq) (H : B.Mat k r → (Wq →L[ℂ] Wp)) (O : Set (B.Mat k r))
    (hs : Q.SmoothLev k r 0 O (B.JF Db H)) : B.JF Db H ∈ Q.FFl k r Db.z Db.z' Db.π Db.π' 0 O := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Db.z Db.z' cStd Db.π Db.π' Db.μW Db.μN Db.μW' H Db.z_mem Db.z'_mem
    Db.haarN.conc (fun n₀ h => Db.haarN.left n₀ h)
  refine ⟨hs, ?_, ?_, ?_⟩
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Db.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Db.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact Formalism.FourierDecayAlt.P5.jf_uEquiv Db H g hh hh'

def omZ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {g | 0 < Gf k r z z' g ∧ ∀ a : Fin r, Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

theorem ff_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (hπ : Ds'.π = Ds.π) (hW : Ds'.μW = Ds.μW) (hN : Ds'.μN = Ds.μN)
    (hW' : Ds'.μW' = Ds.μW') (A : B.Mat k r → (Wq' →L[ℂ] Wq)) (hA : WigEquiv Ds.z Ds.z' Ds.π' Ds'.π' A)
    (hAs : B.CkOn ⊤ (B.GV k r) A) (f : B.Mat k r → (Wq →L[ℂ] Wp)) {A₀ : ℝ} (hThr : JF.TransportedAlt k r A₀ 0)
    (hf : B.InCC A₀ 0 f) (hJ : Q.SmoothLev k r 0 (omZ k r Ds.z Ds.z') (B.JF Ds f)) :
    B.JF Ds' (fun g => (f g).comp (A g)) ∈ Q.FFl k r Ds'.z Ds'.z' Ds'.π Ds'.π' 0 (omZ k r Ds'.z Ds'.z') := by
  refine jf_ff_of_smooth Ds' _ _ fun g₀ hg₀ => ?_
  rw [hz, hz'] at hg₀
  have hOm : g₀ ∈ JF.Om k r Ds.z Ds.z' := CutMP.jdc_om_of _ _ hg₀.1.1 hg₀.2
  obtain ⟨U, J', hU, hgU, hJ', hJJ⟩ := hJ g₀ hg₀
  obtain ⟨V, A', hV, hgV, hA', hAA⟩ := hAs g₀ hg₀.1.1
  refine ⟨U ∩ V ∩ Q.OmPlus k r Ds.z Ds.z', fun g => (J' g).comp (A' g),
    (hU.inter hV).inter (SmoothnessOnGoodSet.isOpen_OmPlus _ _), ⟨⟨hgU, hgV⟩, hOm.2⟩, ?_, fun g hg hG => ?_⟩
  · exact isBoundedBilinearMap_compSh.contDiff.comp_contDiffOn
      ((hJ'.mono (Set.inter_subset_left.trans Set.inter_subset_left)).prodMk
        (hA'.mono (Set.inter_subset_left.trans Set.inter_subset_right)))
  · have e := jf_swap Ds Ds' hz hz' hπ hW hN hW' A hA f hThr hf (γ := g) ⟨hG.1, hg.2⟩
    rw [hJJ g hg.1.1 hG, hAA g hg.1.2 hG.1] at e
    exact e

end swap

section place

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] {u u' : ℕ → ℝ}

theorem ffkb_swap (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hT : SwapTie p q)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq))
    (hA : WigEquiv p.T.base.z p.T.base.z' p.T.base.π' q.T.base.π' A) (hAs : B.CkOn ⊤ (B.GV P.k P.r) A)
    {A₀ : ℝ} (hThr : JF.TransportedAlt P.k P.r A₀ 0) (hf : B.InCC A₀ 0 f) (hJ : B.JF p.T.base f ∈ FFKB p) :
    B.JF q.T.base (fun g => (f g).comp (A g)) ∈ FFKB q := by
  obtain ⟨hz, hz', hπ, hW, hN, hW', -, -⟩ := hT
  exact ff_swap (k := P.k) (r := P.r) p.T.base q.T.base hz hz' hπ hW hN hW' A hA hAs f hThr hf hJ.1

end place

theorem shiftAtR_full (hW : WigExists) : ∃ Cb c₃ : ℝ, 0 ≤ Cb ∧ ∀ (P : M.Par) (Wp Wq : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ l : ℕ) (A₀ : ℝ),
    P.u = P.u' → 1 ≤ l → l < P.k → (2 * n₀ + 1 : ℝ) ≤ P.u' l - P.u' (l + 1) → 3 ≤ b →
    (∀ i ∈ Finset.Icc 1 P.k, |P.u' i| ≤ b) →
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ → JF.TransportedAlt P.k P.r A₀ 0 →
    B.InCC A₀ 1 f → B.InCC A₀ 0 f → B.JF p.T.base f ∈ FFKB p →
    ∃ S : ShiftAtR p f b n₀, S.up = P.u ∧ S.up' = uPlus P.u' l n₀ ∧ S.um = P.u ∧ S.um' = uMinus P.u' l n₀ ∧
      S.pp.l0 = l + 1 ∧ S.pm.l0 = l ∧
      KB.InDDplus2 (shP P S.up S.up') S.pp.l0 S.pp.T.base Cb S.pp.Θ ∧
      KB.InDDplus2 (shP P S.um S.um') S.pm.l0 S.pm.T.base Cb S.pm.Θ ∧
      B.JF S.pp.T.base (fun g => (f g).comp (S.Ap g)) ∈ FFKB S.pp ∧
      B.JF S.pm.T.base (fun g => (f g).comp (S.Am g)) ∈ FFKB S.pm := by
  obtain ⟨Cb, hCb, hPS⟩ := placeSwap_dd
  obtain ⟨c₃, hC⟩ := cell_identity_shifted
  refine ⟨Cb, c₃, hCb, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b n₀ l A₀ hu hl1 hlk hposition hb hub hA₀ hThr hf hf0 hJ
  have hOK : P.OK := p.hP.1
  have hdec : ∀ i ∈ Finset.Ico 1 P.k, P.u' (i + 1) + 1 ≤ P.u' i := by
    intro i hi
    have hi' : i ∈ Finset.Icc 1 (P.k - 1) := by
      rw [Finset.mem_Ico] at hi; rw [Finset.mem_Icc]; omega
    have hg := hOK.gap i hi'
    unfold M.Par.lo M.Par.hi at hg
    rw [hu, max_self, min_self] at hg
    linarith
  obtain ⟨_, hz, hz', _, _, _, hty'⟩ := p.hP
  obtain ⟨W⟩ := hW P.k P.r p.T.base.z p.T.base.z' Wq p.T.base.π' P.u' l n₀ b hz hz' p.T.base.T_pos
    p.T.base.T'_pos hty' hdec hl1 hlk hposition hb hub
  obtain ⟨qp, htp, hπp, hlp, hDp⟩ := hPS P Wp Wq W.Wqp p (uPlus P.u' l n₀) W.πp (l + 1) W.typeP
    (okPlus P l n₀ hOK hu hl1 hlk hposition) (by omega) (by omega)
  obtain ⟨qm, htm, hπm, hlm, hDm⟩ := hPS P Wp Wq W.Wqm p (uMinus P.u' l n₀) W.πm l W.typeM
    (okMinus P l n₀ hOK hu hl1 hlk hposition) hl1 hlk.le
  have hep : WigEquiv p.T.base.z p.T.base.z' p.T.base.π' qp.T.base.π' W.Ap := by
    rw [hπp]; exact W.equivP
  have hem : WigEquiv p.T.base.z p.T.base.z' p.T.base.π' qm.T.base.π' W.Am := by
    rw [hπm]; exact W.equivM
  refine ⟨⟨P.u, uPlus P.u' l n₀, P.u, uMinus P.u' l n₀, W.Wqp, W.Wqm, qp, qm, W.Ap, W.Am,
    fun γ => W.Ap (ptRep p γ), fun γ => W.Am (ptRep p γ), htp.1, htp.2.1, htm.1, htm.2.1, W.polyP, W.polyM, ?_⟩,
    rfl, rfl, rfl, rfl, hlp, hlm, hDp, hDm,
    ffkb_swap p qp htp f W.Ap hep (ckOn_of_polyOp W.polyP) hThr hf0 hJ,
    ffkb_swap p qm htm f W.Am hem (ckOn_of_polyOp W.polyM) hThr hf0 hJ⟩
  refine ⟨fun γ hγ hG => hC P Wp Wq W.Wqp _ _ p qp f W.Ap A₀ htp hep hA₀ hf γ hγ hG,
    fun γ hγ hG => hC P Wp Wq W.Wqm _ _ p qm f W.Am A₀ htm hem hA₀ hf γ hγ hG, ?_, ?_, ?_⟩
  · intro γ hγ hG v
    obtain ⟨hmem, hGf⟩ := ptRep_spec p hγ hG
    have h := W.lower _ hmem (by rw [hGf]; exact hG) v
    rw [hGf] at h
    exact h
  · intro γ hγ hG
    obtain ⟨hmem, hGf⟩ := ptRep_spec p hγ hG
    have h := W.upperP _ hmem
    rw [hGf] at h
    exact h
  · intro γ hγ hG
    obtain ⟨hmem, hGf⟩ := ptRep_spec p hγ hG
    have h := W.upperM _ hmem
    rw [hGf] at h
    exact h

end

end CompanionTheory.WaveGrid.EqShift
