import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ZsCovSum

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
  Formalism.MainNotions.LeviCoordinates
open scoped ENNReal Pointwise

namespace Formalism.L2.S.S7.ZsCovTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (fr : Formalism.IndefR.Eqv.UI.Frames D V)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem isFund_image (hc0 : ∀ v, D.s.cdScale V.rank (fr.ε v) ≠ 0)
    (μf : Measure (Formalism.IndefR.Eqv.UI.instV fr).Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    {s : Set (Formalism.IndefR.Eqv.UI.instV fr).GA} (hsm : MeasurableSet s)
    (hs : IsFundamentalDomain (rr_GF (Formalism.IndefR.Eqv.UI.instV fr)) s ((Formalism.IndefR.Eqv.UI.instV fr).muA μf)) :
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig V.gram) (Formalism.IndefR.Eqv.UI.brg fr '' s)
      (ZsCovMeas.muV fr μf) := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := Formalism.IndefR.Eqv.ga_facts D V
  have hH := ZsCovMeas.isHaar_muV fr hc0 μf
  have hGF : (Formalism.IndefR.Eqv.UI.brg fr) '' (Formalism.IndefR.Eqv.UI.instV fr).GFset =
      Formalism.L2.SG.AdBridge.ratHA (Formalism.IndefR.Eqv.UI.instV fr) :=
    (Formalism.L2.SG.Closed.adelic_isomorphism_statement (Formalism.IndefR.Eqv.UI.instV fr)).2.1 (Formalism.IndefR.Eqv.UI.brg fr)
      (Formalism.IndefR.Eqv.UI.brg_isBridge fr)
  have hto : ∀ γ : rr_GF (Formalism.IndefR.Eqv.UI.instV fr),
      Formalism.IndefR.Eqv.UI.brg fr (γ : (Formalism.IndefR.Eqv.UI.instV fr).GA) ∈ HFinIn (AF D.host.F) D.sp.cm.sig V.gram := by
    intro γ
    have : Formalism.IndefR.Eqv.UI.brg fr (γ : (Formalism.IndefR.Eqv.UI.instV fr).GA) ∈
        Formalism.L2.SG.AdBridge.ratHA (Formalism.IndefR.Eqv.UI.instV fr) := hGF ▸ ⟨γ, γ.2, rfl⟩
    exact this
  have hfrom : ∀ g : HFinIn (AF D.host.F) D.sp.cm.sig V.gram, ∃ γ : rr_GF (Formalism.IndefR.Eqv.UI.instV fr),
      Formalism.IndefR.Eqv.UI.brg fr (γ : (Formalism.IndefR.Eqv.UI.instV fr).GA) = (g.1 : GA D V) := by
    intro g
    have h : (g.1 : GA D V) ∈ Formalism.L2.SG.AdBridge.ratHA (Formalism.IndefR.Eqv.UI.instV fr) := g.2
    rw [← hGF] at h
    obtain ⟨γ, hγ, hγg⟩ := h
    exact ⟨⟨γ, hγ⟩, hγg⟩
  have hsm1 : ∀ (γ : rr_GF (Formalism.IndefR.Eqv.UI.instV fr)) (y : (Formalism.IndefR.Eqv.UI.instV fr).GA),
      Formalism.IndefR.Eqv.UI.brg fr (γ • y) =
        (⟨Formalism.IndefR.Eqv.UI.brg fr γ, hto γ⟩ : HFinIn (AF D.host.F) D.sp.cm.sig V.gram) • Formalism.IndefR.Eqv.UI.brg fr y := by
    intro γ y
    show Formalism.IndefR.Eqv.UI.brg fr ((γ : (Formalism.IndefR.Eqv.UI.instV fr).GA) * y) = _
    rw [map_mul]
    rfl
  have hsmul : ∀ (γ : rr_GF (Formalism.IndefR.Eqv.UI.instV fr)) (t : Set (Formalism.IndefR.Eqv.UI.instV fr).GA),
      Formalism.IndefR.Eqv.UI.brg fr '' (γ • t) =
        (⟨Formalism.IndefR.Eqv.UI.brg fr γ, hto γ⟩ : HFinIn (AF D.host.F) D.sp.cm.sig V.gram) •
          (Formalism.IndefR.Eqv.UI.brg fr '' t) := by
    intro γ t
    ext z
    simp only [Set.mem_image, Set.mem_smul_set]
    constructor
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨Formalism.IndefR.Eqv.UI.brg fr y, ⟨y, hy, rfl⟩, (hsm1 γ y).symm⟩
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨γ • y, ⟨y, hy, rfl⟩, hsm1 γ y⟩
  have hmuV : ∀ t, ZsCovMeas.muV fr μf (Formalism.IndefR.Eqv.UI.brg fr '' t) =
      ZsCovMeas.cdProd fr * (Formalism.IndefR.Eqv.UI.instV fr).muA μf t := by
    intro t
    rw [ZsCovMeas.muV, Measure.smul_apply, smul_eq_mul]
    congr 1
    refine ((Formalism.IndefR.Eqv.UI.brg fr).toHomeomorph.toMeasurableEquiv.map_apply _).trans ?_
    exact congrArg _ (Set.preimage_image_eq _ (Formalism.IndefR.Eqv.UI.brg fr).injective)
  refine IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_
  · exact ((Formalism.IndefR.Eqv.UI.brg fr).toHomeomorph.measurableEmbedding.measurableSet_image.2 hsm).nullMeasurableSet
  · have hc := hs.ae_covers
    have h2 : ∀ᵐ z ∂(((Formalism.IndefR.Eqv.UI.instV fr).muA μf).map (Formalism.IndefR.Eqv.UI.brg fr)),
        ∃ g : HFinIn (AF D.host.F) D.sp.cm.sig V.gram, g • z ∈ Formalism.IndefR.Eqv.UI.brg fr '' s := by
      refine ((Formalism.IndefR.Eqv.UI.brg fr).toHomeomorph.measurableEmbedding.ae_map_iff).2 ?_
      filter_upwards [hc] with x hx
      obtain ⟨γ, hγ⟩ := hx
      exact ⟨⟨Formalism.IndefR.Eqv.UI.brg fr γ, hto γ⟩, γ • x, hγ, hsm1 γ x⟩
    exact Measure.ae_smul_measure h2 _
  · intro g hg
    obtain ⟨γ, hγ⟩ := hfrom g
    have hγ1 : γ ≠ 1 := by
      intro h1
      apply hg
      apply Subtype.ext
      rw [← hγ, h1]
      first | rfl | (simp; rfl)
    have hd : (Formalism.IndefR.Eqv.UI.instV fr).muA μf (γ • s ∩ (1 : rr_GF (Formalism.IndefR.Eqv.UI.instV fr)) • s) = 0 :=
      hs.aedisjoint hγ1
    rw [one_smul] at hd
    have hg' : g = ⟨Formalism.IndefR.Eqv.UI.brg fr γ, hto γ⟩ := Subtype.ext hγ.symm
    rw [hg', ← hsmul]
    show ZsCovMeas.muV fr μf (Formalism.IndefR.Eqv.UI.brg fr '' (γ • s) ∩ Formalism.IndefR.Eqv.UI.brg fr '' s) = 0
    rw [← Set.image_inter (Formalism.IndefR.Eqv.UI.brg fr).injective, hmuV, hd, mul_zero]
  · intro g
    exact (measurePreserving_mul_left (ZsCovMeas.muV fr μf) (g.1 : GA D V)).quasiMeasurePreserving

theorem covolSum_of_tie (X : Formalism.MainNotions.BridgeLemma.CData) (hX : X.I = Formalism.IndefR.Eqv.UI.instV fr)
    (hΛ : fr.Λ = Formalism.IndefR.Eqv.UI.Lv D V) {P Q : ℕ} (hV : V.SigOK) (hs : ∀ τ, V.sig τ = (P, Q))
    (hε : ∀ v, (Finset.univ.filter fun i => fr.ε v i = true).card = P)
    (hT : VolTie D) (hI : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep D) (hC : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt D V.rank)
    (hcd : cdScaleTie D) (hCG : ∀ v, Formalism.MainNotions.S.Gauge.CdGauge D V.rank (fr.ε v))
    (hVU : Formalism.MainNotions.S.Gauge.VolUn V.rank) :
    Formalism.MainNotions.FundamentalDomainUnfolding.CovolSum X (IwasawaCovolume.covolR X) := by
  have key : ∀ (ys : Finset (Formalism.IndefR.Eqv.UI.instV fr).Gf)
      (Dy : (Formalism.IndefR.Eqv.UI.instV fr).Gf → Set (Formalism.IndefR.Eqv.UI.instV fr).Ginf),
      Formalism.MainNotions.FundamentalDomainUnfolding.ClassReps (Formalism.IndefR.Eqv.UI.instV fr) ys →
      (∀ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.IsFundInf (Formalism.IndefR.Eqv.UI.instV fr) y
        (Formalism.MainNotions.FundamentalDomainUnfolding.muInf (Formalism.IndefR.Eqv.UI.instV fr)) (Dy y)) →
      ∑ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.muInf (Formalism.IndefR.Eqv.UI.instV fr) (Dy y) =
        ENNReal.ofReal ((Formalism.IndefR.Eqv.UI.instV fr).gaugeU *
          (IwasawaCovolume.volgU V.rank ^ Fintype.card (InfinitePlace D.host.F) * massI D V.rank)) := by
    intro ys Dy hys hD
    obtain ⟨g1, g2, g3⟩ := Formalism.IndefR.Eqv.gf_facts fr
    obtain ⟨k1, k2, k3, k4, k5⟩ := Formalism.IndefR.Eqv.ga_facts D V
    set ν : Measure (Formalism.IndefR.Eqv.UI.instV fr).Gf := Measure.haar with hν
    have hKc : IsCompact (Formalism.IndefR.Eqv.UI.instV fr).Kset := PI.WAU.Cpt.isCompact_Kset (Formalism.IndefR.Eqv.UI.instV fr)
    have hKo : IsOpen (Formalism.IndefR.Eqv.UI.instV fr).Kset := PI.WAU.kset_open (Formalism.IndefR.Eqv.UI.instV fr)
    have hk0 : ν (Formalism.IndefR.Eqv.UI.instV fr).Kset ≠ 0 := (hKo.measure_pos ν ⟨1, UnfoldingVolume.kone (Formalism.IndefR.Eqv.UI.instV fr)⟩).ne'
    have hkt : ν (Formalism.IndefR.Eqv.UI.instV fr).Kset ≠ ⊤ := hKc.measure_lt_top.ne
    set μf : Measure (Formalism.IndefR.Eqv.UI.instV fr).Gf := (ν (Formalism.IndefR.Eqv.UI.instV fr).Kset)⁻¹ • ν with hμfdef
    have hμf : μf.IsHaarMeasure :=
      Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr hkt) (ENNReal.inv_ne_top.mpr hk0)
    have hK1 : μf (Formalism.IndefR.Eqv.UI.instV fr).Kset = 1 := by
      rw [hμfdef, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hk0 hkt]

    have hg : ∀ v, (D.s.cdScale V.rank (fr.ε v) : ℝ) * Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) *
        IwasawaCovolume.volgU V.rank = 1 := by
      intro v
      have h := hCG v
      unfold Formalism.MainNotions.S.Gauge.CdGauge at h
      rw [hVU, ← ZsCovSum.volgU_eq_Icc] at h
      exact h
    have hc0 : ∀ v, D.s.cdScale V.rank (fr.ε v) ≠ 0 := by
      intro v h0
      have h := hg v
      rw [h0] at h
      simp at h
    have hw := IwasawaCovolume.volgU_pos V.rank
    have hgpos : ∀ v, 0 < Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) := by
      intro v
      have h : ((D.s.cdScale V.rank (fr.ε v) : ℝ) * IwasawaCovolume.volgU V.rank) * Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) = 1 := by
        rw [← hg v]; ring
      exact pos_of_mul_pos_right (h ▸ one_pos) (mul_nonneg (D.s.cdScale V.rank (fr.ε v)).2 hw.le)

    have hn : P + Q = V.rank := by
      have := Formalism.BasicNotions.sig_sum V hV D.host.φ₀
      rw [hs] at this
      exact this
    choose e h1 h2 using fun v => ZsCovSum.blockEquiv (fr.ε v) (hε v) hn

    have hvol := ZsCovMeas.isVolMeas_muV fr hcd hΛ e h1 h2 hc0 μf hK1
    have hFD := UnfoldingVolume.fd_isFund (Formalism.IndefR.Eqv.UI.instV fr) μf ys hys Dy hD
    have hF := isFund_image fr hc0 μf (ZsCovSum.FD_meas (Formalism.IndefR.Eqv.UI.instV fr) ys Dy hD) hFD
    have htie : ZsCovMeas.muV fr μf (Formalism.IndefR.Eqv.UI.brg fr '' UnfoldingVolume.FD (Formalism.IndefR.Eqv.UI.instV fr) ys Dy) =
        ENNReal.ofReal (D.vol V) := ((hT V P Q hV hs).2 _ hvol).2 _ hF
    have hvm := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.vol_eq_mass_of_indep D V.rank hT hI hC V P Q hV hs rfl
    have hmu : ZsCovMeas.muV fr μf (Formalism.IndefR.Eqv.UI.brg fr '' UnfoldingVolume.FD (Formalism.IndefR.Eqv.UI.instV fr) ys Dy) =
        ZsCovMeas.cdProd fr * ∑ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.muInf (Formalism.IndefR.Eqv.UI.instV fr) (Dy y) := by
      rw [ZsCovMeas.muV, Measure.smul_apply, smul_eq_mul]
      congr 1
      refine ((Formalism.IndefR.Eqv.UI.brg fr).toHomeomorph.toMeasurableEquiv.map_apply _).trans ?_
      refine (congrArg _ (Set.preimage_image_eq _ (Formalism.IndefR.Eqv.UI.brg fr).injective)).trans ?_
      rw [ZsCovSum.muA_FD (Formalism.IndefR.Eqv.UI.instV fr) μf ys hys Dy hD, hK1, one_mul]
    rw [hmu, hvm] at htie

    have hm0 : 0 ≤ massI D V.rank := hvm ▸ (D.vol_pos V).le
    have hG : (Formalism.IndefR.Eqv.UI.instV fr).gaugeU * IwasawaCovolume.volgU V.rank ^ Fintype.card (InfinitePlace D.host.F) =
        ∏ v : InfinitePlace D.host.F, (Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) * IwasawaCovolume.volgU V.rank) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      rfl
    have hG0 : ∀ v : InfinitePlace D.host.F, 0 ≤ Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) * IwasawaCovolume.volgU V.rank :=
      fun v => (mul_pos (hgpos v) hw).le
    have hone : ZsCovMeas.cdProd fr * ENNReal.ofReal
        (∏ v : InfinitePlace D.host.F, (Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) * IwasawaCovolume.volgU V.rank)) = 1 := by
      rw [ENNReal.ofReal_prod_of_nonneg fun v _ => hG0 v, ZsCovMeas.cdProd, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _), ← mul_assoc, hg v,
        ENNReal.ofReal_one]
    calc ∑ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.muInf (Formalism.IndefR.Eqv.UI.instV fr) (Dy y)
        = (ZsCovMeas.cdProd fr * ∑ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.muInf (Formalism.IndefR.Eqv.UI.instV fr) (Dy y)) *
            ENNReal.ofReal (∏ v : InfinitePlace D.host.F,
              (Formalism.MainNotions.S.Gauge.gaugeU (fr.ε v) * IwasawaCovolume.volgU V.rank)) := by
          rw [mul_comm (ZsCovMeas.cdProd fr), mul_assoc, hone, mul_one]
      _ = ENNReal.ofReal (massI D V.rank) * ENNReal.ofReal ((Formalism.IndefR.Eqv.UI.instV fr).gaugeU *
            IwasawaCovolume.volgU V.rank ^ Fintype.card (InfinitePlace D.host.F)) := by
          rw [htie, hG]
      _ = ENNReal.ofReal ((Formalism.IndefR.Eqv.UI.instV fr).gaugeU * (IwasawaCovolume.volgU V.rank ^ Fintype.card (InfinitePlace D.host.F) *
            massI D V.rank)) := by
          rw [← ENNReal.ofReal_mul hm0]
          congr 1
          ring
  have gen : ∀ J : AutInst, J = Formalism.IndefR.Eqv.UI.instV fr → ∀ (ys : Finset J.Gf) (Dy : J.Gf → Set J.Ginf),
      Formalism.MainNotions.FundamentalDomainUnfolding.ClassReps J ys → (∀ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.IsFundInf J y (Formalism.MainNotions.FundamentalDomainUnfolding.muInf J) (Dy y)) →
      ∑ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.muInf J (Dy y) ≤ ENNReal.ofReal (J.gaugeU * (IwasawaCovolume.volgU J.n ^
        Fintype.card (InfinitePlace J.F) * Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm J.E J.n) (Formalism.MainNotions.StandardLattice.stdLat J.E J.n))) := by
    rintro J rfl ys Dy hys hD
    exact (key ys Dy hys hD).le
  unfold Formalism.MainNotions.FundamentalDomainUnfolding.CovolSum IwasawaCovolume.covolR
  exact gen X.I hX

end Formalism.L2.S.S7.ZsCovTie
