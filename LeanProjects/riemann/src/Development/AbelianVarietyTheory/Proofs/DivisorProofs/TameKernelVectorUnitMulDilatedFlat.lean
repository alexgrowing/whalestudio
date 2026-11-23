import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorIsThetaFunctionTwoStepModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TowerIsChain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepRealThetaRuleOfNodesFarApart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParParBLast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOKAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHFrameDtPackPre
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IoYStOfIoPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsLevelCharacterConditionsHold
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftMultiplicitySpacesOfPublishedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartsAtTwistPlacesChain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftsCharOfResidueCharAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSplittingCharactersResidueUnramifiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageFiniteLevelEqProductLocalLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DilatedFlatDatumIsSBHalfTameKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftDatumConjugateHalfFiniteFourierSumStatement

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseCmp

open Classical in

theorem kerDat_twoStep {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    {i : Fin D.R.m} {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Pl D.host.E)} {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} (hK : KerDat R i ξ χ ξR Q ω φ)
    (hQ : ∃ t, Q ⊆ R.Q t) {eg eQ : AE D} {fg : WO (Vc D i) (Wc D i) → ℂ} (hg : IsIdemSum eg R.Pg) (hq : IsIdemSum eQ Q)
    (hfg : IsTypeVec R i eg fg) :
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eQ) (lattice₂ R i) 1 fg
      (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) φ := by
  obtain ⟨⟨hψ, -⟩, e, he, hTe⟩ := hK.vec
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  obtain ⟨t, ht⟩ := hQ
  have hd : Disjoint R.Pg Q := Disjoint.mono_right ht (GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces R F hC t)
  have hsum : e = eg + eQ := by
    rw [← GlobalTheory.ExportSeries.idem_eq he, ← GlobalTheory.ExportSeries.idem_eq hg, ← GlobalTheory.ExportSeries.idem_eq hq]
    exact Finset.sum_union hd
  subst hsum
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hgQ : eg * eQ = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - heg - heQ
  have hcg : cA D eg * cA D eg = cA D eg := by rw [← map_mul, heg]
  have hcQ : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, heQ]
  have hQg : cA D eQ * cA D eg = 0 := by rw [← map_mul, mul_comm, hgQ, map_zero]
  have hgQ' : cA D eg * cA D eQ = 0 := by rw [mul_comm, hQg]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfg : infPart D (cA D eg) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
  have hinfQ : infPart D (cA D eQ) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hq)
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBQ := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinfQ (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    Q (fun y => omegaQ Q (Wc D i).rank ξR (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := hTe
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add, add_comm]
  have hc' : cA D (eg + eQ) = cA D eg + cA D eQ := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hcQ hcg hQg hΛ hSBg (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hcg hcQ hgQ' hΛ (hc' ▸ hTe1)
  have hbase := hfg.2 _ hm2
  simp only [LinearMap.comp_apply] at hbase
  rw [← hbase] at hm1
  refine ⟨⟨_, hm1⟩, fun T' hT' => ?_⟩
  rw [hTe2 Te hTe1, GlobalTheory.TwoStepModel.datum_eq_tensorHalf (R.βV i) (R.βW i) hg hq hd he ξR]
  exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hcQ hinfQ hm1 hT' hSBQ

end GlobalTheory.BaseCmp

namespace GlobalTheory.BaseCmp

open GlobalTheory.ChainOnto in

theorem kerDat_xiR_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ),
    KerDat R i ξ χ ξR Q ω φ → ∀ PP ∈ Q, ξR PP ≠ 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _ i ξ χ ξR Q ω φ hK
  intro PP hP h1
  refine (hK.ram PP).2 (Or.inl hP) fun x hx => ?_
  have hc := hK.res PP hP
  rw [h1] at hc
  have hU : IsOpen {z : PP.adicCompletion D.host.E | Valued.v (z - x) < 1} :=
    (GlobalTheory.ChainOnto.TameRes.isOpen_ltOne PP).preimage (continuous_sub_right _)
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap D.host.E PP).exists_mem_open hU ⟨x, by simp⟩
  have hk' : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) < Valued.v (x : PP.adicCompletion D.host.E) := by
    rw [hx]; exact hk
  have hv : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k) = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ hk']; exact hx
  have hv1 : PP.valuation D.host.E k = 1 := by rw [← GlobalTheory.ChainOnto.TameRes.val_alg]; exact hv
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hv1
  obtain ⟨a, s, h⟩ := PP.exists_primeCompl_mul_eq_of_integer k hv1.le
  have hs : (s : 𝓞 D.host.E) ∉ PP.asIdeal := s.2
  have hsv := GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem PP _ hs
  have hav : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) = 1 := by
    rw [← h, map_mul, hv1, hsv, one_mul]
  have ha : a ∉ PP.asIdeal := fun hm =>
    absurd hav (ne_of_lt ((PP.valuation_lt_one_iff_mem (K := D.host.E) a).mpr hm))
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  have key : ∀ (b : 𝓞 D.host.E), b ∉ PP.asIdeal → ∀ y : D.host.Eˣ, (y : D.host.E) = b → ξ.locK PP y = 1 := by
    intro b hb y hy
    have hms : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hb
    obtain ⟨b', hb'⟩ := Ideal.Quotient.exists_inv hms
    exact (hc b y (Units.mkOfMulEqOne _ b' hb') hy rfl).symm
  have hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hsv; exact zero_ne_one hsv
  have ha0 : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hav; exact zero_ne_one hav
  have hkk : Units.mk0 k hk0 * Units.mk0 _ hs0 = Units.mk0 _ ha0 := Units.ext h
  have hk1 : ξ.locK PP (Units.mk0 k hk0) = 1 := by
    have := congrArg (ξ.locK PP) hkk
    rwa [map_mul, key _ hs (Units.mk0 _ hs0) rfl, key _ ha (Units.mk0 _ ha0) rfl, mul_one] at this
  set y := Formalism.L2.Host.atFin PP (Units.mk0 k hk0) with hy
  have hyv : (y : PP.adicCompletion D.host.E) = algebraMap D.host.E (PP.adicCompletion D.host.E) k := rfl
  have ht := hK.tame PP (y * x⁻¹) (by
    unfold Formalism.L2.Host.IsUnitAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hyv, hv, hx, inv_one, mul_one]) (by
    have e : ((y * x⁻¹ : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) - 1 =
        (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) * (x : PP.adicCompletion D.host.E)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hyv, sub_mul, mul_inv_cancel₀ x.ne_zero]
    unfold Formalism.L2.Host.IsUnitAt at hx
    rw [e, map_mul, map_inv₀, hx, inv_one, mul_one]
    have hlt : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) < 1 := hk
    generalize Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) = z at hlt
    rcases eq_or_ne z 0 with rfl | hz
    · exact zero_le'
    · rw [← WithZero.exp_log hz] at hlt ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]
      push_cast
      omega)
  have hk2 : ξ.loc PP y = 1 := hk1
  rw [map_mul, hk2, one_mul, map_inv, inv_eq_one] at ht
  exact ht

end GlobalTheory.BaseCmp

namespace GlobalTheory.BaseCmp

open Classical in

theorem liftKer_of_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ),
    KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg →
    ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
      ∃ Gc : ℂ, UnitOff N Gc ∧ IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) ∧
        ∀ Tm, IsModel R i eQ fg Tm → φ = Tm (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i hV ξ χ ξR Q ω φ hK hQ N hN hNQ eg eQ fg hg hq hfg ϖ hϖ0 hϖ
  have hθ := kerDat_twoStep hC hK hQ hg hq hfg
  obtain ⟨Y, a, Gc, hU, hY, hΦ, hS⟩ := GlobalTheory.T.lift_datum_conjugate_half_finite_fourier_sum D G Pl0 T0 A Ks R F hC hG i hV ξR Q hQ
    (kerDat_xiR_ne D G Pl0 T0 A Ks R F hC i ξ χ ξR Q ω φ hK) N hN hNQ eQ hq ϖ hϖ0 hϖ
  refine ⟨Gc, hU, GlobalTheory.T.dilatedFlatDatum_isSBHalf_tameKernel D G Pl0 T0 A Ks R F hC hG i hV ξR Q hQ eQ hq ϖ hϖ0 hϖ Gc, fun Tm hTm => ?_⟩
  have h1 := GlobalTheory.DatumFourier.thetaAt_eq_sum (fun q : Y => q.1) (fun q : Y => a q.1) hθ
    (fun q => by rw [GlobalTheory.LatVac.cA_cA]; exact hY q.1 q.2)
    (fun t => by rw [hΦ t]; congr 1; exact (Finset.sum_coe_sort Y fun y => a y * R.ψ (symplO (Vc D i) (Wc D i) t y)).symm)
  have h2 : (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) =
      ∑ y ∈ Y, a y • fun t => halfInd eQ (lattice₂ R i) (t + y) := by
    funext t
    rw [← hS t, Finset.sum_apply]
    rfl
  have hvac : Tm (halfInd eQ (lattice₂ R i)) = fg := by simpa using hTm.vac
  rw [h1, h2, map_sum, ← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, hTm.trans _ (GlobalTheory.isSBHalf_halfInd eQ (lattice₂ R i)) _ (hY q.1 q.2), hvac]

end GlobalTheory.BaseCmp
