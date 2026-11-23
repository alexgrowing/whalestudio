import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseCmp

open GlobalTheory.PlaceModel

open Classical in

theorem resC_eq_of_kerDat {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
    {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    (hK : KerDat R i ξ χ ξR B.de.Q ω φ) (hc : ChrEq B.de.chi ξ) {PP : Pl D.host.E} (hPP : PP ∈ B.de.Q) :
    ξR PP = B.de.resC PP := by
  refine MonoidHom.ext fun u => Units.ext ?_
  obtain ⟨x, hx⟩ := exists_isLocUnit (hB.de.split.isIdemAt hPP) u
  obtain ⟨k1, k2⟩ := hx.res
  have e1 := eq_res_of_chrEq hc (hB.de.split.isIdemAt hPP) (hK.tame PP) (hK.res PP hPP) x hx.off k1 u k2
  have e2 := hx.eq (hB.de.res PP hPP)
  rw [← e1, e2]
  rfl

open Classical in

theorem omegaFlat_eq_locFn_empty {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
    {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    (hK : KerDat R i ξ χ ξR B.de.Q ω φ) (hc : ChrEq B.de.chi ξ) (y : Reds D (Wc D i).rank (Vc D i).rank) :
    omegaFlat B.de.Q (Wc D i).rank ξR y = (GlobalTheory.FlatVecSum.princ B).locFn ∅ (fun _ _ => 1) y := by
  rw [GlobalTheory.FlatVecSum.omegaFlat_eq_prod, Base.locFn]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  exact Finset.prod_congr rfl fun PP hP => by rw [resC_eq_of_kerDat hB hK hc hP]; rfl

open Classical in

theorem flatTwoStep_holds : FlatTwoStep := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR ω φ B hB h hK hc
  obtain ⟨hvac, e, he, -⟩ := hK.vec
  have hψ := hvac.1
  have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βV i))
  have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βW i))
  have hdisj : Disjoint R.Pg B.de.Q := h.Pg ▸ hB.places.disj
  obtain ⟨eg, eQ, hg, hq, h1, h2, h3⟩ := GlobalTheory.FlatVecExist.idemSum_split he hdisj
  have hinfg := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
  obtain ⟨fg, hfg⟩ := GlobalTheory.PlaceVec.exists_isThetaAt hψ sV sW (a := cA D eg)
    (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self hg]) hinfg
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D R.ψ hψ _ _ _ _ sV sW _ eg hg _ hvac.2.theta hvac.2.lat).2
    (GlobalTheory.PlaceVec.isSBHalf_of_red sV.1 sW.1 hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) R.Pg
      (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h)
  have hoQ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hq
  have fix : ∀ u, (∀ a b, cA D eg * u a b = 0 ∧ eg * u a b = 0) →
      heisO R.ψ (Vc D i) (Wc D i) u (R.vacP i) = R.vacP i → heisO R.ψ (Vc D i) (Wc D i) u fg = fg :=
    fun u hu h0 => GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ (cA D eg) _ 1 _ _ fg hfg u
      (fun a b => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hu a b) h0
  have hPM := GlobalTheory.FlatVecExist.exists_model_of_fix hψ sV sW hoQ hq.2
    (fun u hu => fix u (fun a b => (GlobalTheory.FlatVecExist.off_of_half h1 (by rw [mul_comm, h3])
        ((isHalf_iff _ _).2 hu.2) a b).symm)
      (hoQ.heisO_eq (by rw [mul_comm, hq.2]) hvac.2.lat u hu))
    (fun u hu => fix u (fun a b => (GlobalTheory.FlatVecExist.off_of_half h2
        (by rw [← RingHom.map_mul, h1, map_zero]) ((isHalf_iff _ _).2 hu.2) a b).symm)
      (hoQ.conj.heisO_eq (by rw [GlobalTheory.DualPairCheck.cA_cA, hq.2]) hvac.2.lat u hu))
  have hinfQ := GlobalTheory.PlaceDatum.infPart_idemSum hq
  obtain ⟨K, hK', hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO sV.1 sW.1 (R.βV i) (R.βW i)
  obtain ⟨f, hf⟩ := GlobalTheory.PlaceDatum.exists_isThetaAt hψ sV sW (GlobalTheory.PlaceDatum.idemSum_mul_self hq) hinfQ hPM
    (GlobalTheory.PlaceDatum.isSBHalf_of_red eQ _ (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (GlobalTheory.PlaceDatum.frMapO_add _ _)
      (GlobalTheory.PlaceDatum.exists_den_frMapO sV.1.fg sW.1.fg _ _)
      ⟨K, hK', fun x hx => hC x (GlobalTheory.PlaceDatum.infPart_of_half hinfQ hx)⟩ B.de.Q
      (fun y => GlobalTheory.ConjTwist.omegaFlat B.de.Q (Wc D i).rank ξR y) fun y y' h => GlobalTheory.FlatVecExist.omegaFlat_congr _ _ _ h)
  have hfeq : f = (GlobalTheory.FlatVecSum.princ B).vecBase := by
    have k1 := hfg
    have k2 := hf
    simp only [omegaFlat_eq_locFn_empty hB hK hc] at k2
    rw [← idem_eq hg] at k1
    rw [← idem_eq hq] at k2
    rw [← h.ψ, ← h.ΛS, ← h.ΛT, ← h.βS, ← h.βT] at k1 k2
    rw [← h.vac, ← h.Pg] at k1
    unfold Base.vecBase Base.vecAt
    rw [Finset.union_empty]
    refine GlobalTheory.FlatVecSum.eq_vec_of_two_steps (G := GlobalTheory.FlatVecSum.princG B.G) hB.frame hB.places (fun y y' hy => ?_)
      (fg := fg) ?_ k2
    · unfold Base.locFn
      rw [Finset.prod_congr rfl fun PP hPP => by rw [hy PP hPP]]
    · simp only [GlobalTheory.FlatVecSum.omegaG_princ]
      exact k1
  refine ⟨eg, eQ, fg, hg, hq, hfg, ?_⟩
  rw [← hfeq]
  exact hf

end GlobalTheory.BaseCmp
