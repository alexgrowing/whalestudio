import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumVectorTransformsByLevelCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDatumInvLeftMulTargetLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTwoDiagBlocksProperties

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SourceLaw
variable {D : D7}

theorem omegaG_levelDatum_zero_indep_chars (a r t : ℕ) (ha : r ≤ a) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) {b : ℕ}
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaG (Lev.datY a r t 0 ha Pg ∅ P χ ξ Lev.Frm.B) χj y = omegaG (Lev.datY a r t 0 ha Pg ∅ P χ' ξ' Lev.Frm.B) χj y := by
  unfold omegaG
  rfl

open GlobalTheory.AdjDatumMove in

theorem levelDatum_target_under_sourceLevel_element (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (r t : ℕ) (ha : r ≤ T.rank) (hb : r ≤ S.rank) (hTS : T.rank ≤ S.rank) (ea : T.rank = r + 0 * t)
    (eb : S.rank = r + (0 + 1) * t)
    (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D)
    (g : GA D S) (sg : finE S g ∈ St βS)
    (hG : ∀ PP ∈ Pg, redFn βS PP (finE S g) ∈ blockTri (blkOf r t))
    (hP : (fun PP : ↥Pg => upperLeftBlock hb (redFn βS PP.1 (finE S g))) ∈ P.H)
    (hQ : ∀ PP ∈ Q, redFn βS PP (finE S g) ∈ blockTri (blk2 T.rank)) (x : WO S T) :
    GlobalTheory.FinZeta.levDatum S T βS βT (Lev.datY T.rank r t 0 ha Pg ∅ P (fun _ _ => 1) (fun _ => 1) Lev.Frm.B) Q m e
                 (actO S T g⁻¹ 1⁻¹ x) =
      ((((P.chi ⟨_, hP⟩ * ∏ PP ∈ Pg, ∏ i ∈ Finset.range (0 + 1),
            m PP (dBlk (blkOf r t) (i + 1) (redFn βS PP (finE S g))))⁻¹ *
          ∏ PP ∈ Pg, m PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ) *
        ∏ PP ∈ Q, (((m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hTS (redFn βS PP (finE S g))⁻¹)))⁻¹ : ℂˣ) : ℂ)) *
      GlobalTheory.FinZeta.levDatum S T βS βT (Lev.datY T.rank r t 0 ha Pg ∅ P (fun _ _ => 1) (fun _ => 1) Lev.Frm.B) Q m e x := by
  have sg' : finE S g⁻¹ ∈ St βS := by rw [map_inv]; exact inv_mem sg
  have s1 : finE T (1 : GA D T)⁻¹ ∈ St βT := by rw [inv_one, map_one]; exact one_mem _
  have hγ : ∀ PP, redFn βS PP (finE S g⁻¹) = (redFn βS PP (finE S g))⁻¹ := fun PP => by rw [map_inv, redFn_inv sg]
  have h1' : ∀ PP, (redFn βT PP (finE T (1 : GA D T)⁻¹))⁻¹ = 1 := fun PP => by
    rw [inv_one, map_one, redFn_one, inv_one]
  unfold GlobalTheory.FinZeta.levDatum
  by_cases hx : IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x)
  · have h1 := red_actO S T βS βT sg' s1 hx.2
    have h2 : ∀ PP, redM PP (frMapAdj S T βS βT (actO S T g⁻¹ 1⁻¹ x)) =
        ((redFn βS PP (finE S g))⁻¹).val * redM PP (frMapAdj S T βS βT x) := fun PP => by
      rw [h1.2 PP, hγ PP, h1' PP, Units.val_one, Matrix.mul_one]
    have hq := omegaQ_mul hTS Q m (fun PP => (redFn βS PP (finE S g))⁻¹) (fun _ => 1) (fun PP hP => inv_mem (hQ PP hP))
      (fun PP => redM PP (frMapAdj S T βS βT x))
    simp only [inv_one, Units.val_one, Matrix.mul_one, map_one, mul_one] at hq
    have hm := GlobalTheory.ChainOnto.omegaG_levelP_move D T.rank S.rank r t 0 ha hb ea eb Pg P (fun _ => m) (fun _ => 1)
      (fun PP => redFn βS PP (finE S g)) hG hP (fun PP => redM PP (frMapAdj S T βS βT x))
    rw [if_pos hx, if_pos ⟨isHalf_actO' _ _ hx.1, h1.1⟩, funext h2, hq,
      omegaG_levelDatum_zero_indep_chars T.rank r t ha Pg P (fun _ _ => 1) (fun _ => m) (fun _ => 1) (fun _ => 1) m
        (fun PP => ((redFn βS PP (finE S g))⁻¹).val * redM PP (frMapAdj S T βS βT x)),
      omegaG_levelDatum_zero_indep_chars T.rank r t ha Pg P (fun _ _ => 1) (fun _ => m) (fun _ => 1) (fun _ => 1) m
        (fun PP => redM PP (frMapAdj S T βS βT x)), hm]
    ring
  · rw [if_neg hx, if_neg, mul_zero]
    rintro ⟨h1, h2⟩
    have e' := GlobalTheory.AdelicLatMove.actO_actO_inv S T g (1 : GA D T) x
    have h3 := isHalf_actO' g (1 : GA D T) h1
    have h4 := (red_actO S T βS βT sg (by rw [map_one]; exact one_mem _) h2).1
    rw [e'] at h3 h4
    exact hx ⟨h3, h4⟩

end GlobalTheory.SourceLaw

namespace GlobalTheory.SourceLaw

open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues in
set_option maxHeartbeats 1000000 in

theorem om_src_law {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (P : LevelP R.Pg D.R.r ℂ) (cμ cη : (AE D)ˣ →* Circle)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (h : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io) (κ : GA D (Vc D i))
    (hκ : κ ∈ Lev.levA (Vc D i) (levV R i t P m)) :
    ω (κ, 1) f = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m) κ)⁻¹ • f := by
  classical
  obtain ⟨hC, -, -, -, hch, hW, -, hlv, -, -, -⟩ := h
  rw [GlobalTheory.FinZeta.isLevelVec_iff] at hlv
  obtain ⟨hvac, e, he, hth⟩ := hlv
  have hL := hC.lev
  have hκG : κ ∈ GfC (Vc D i) := (Subgroup.mem_inf.1 hκ).1
  have hκL : finE (Vc D i) κ ∈ lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m) := (Subgroup.mem_inf.1 hκ).2
  have sV : finE (Vc D i) κ ∈ St (R.βV i) := parLev_St hκL.1
  have sW : finE (Wc D i) 1 ∈ St (R.βW i) := by rw [map_one]; exact one_mem _
  have dV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i)
  have dW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)
  have fV := (hL.βV i).choose_spec.1
  have fW := (hL.βW i).choose_spec.1
  have hch' := GlobalTheory.T.conjugatedThetaCharacters_restriction_ramification R hL i t s cμ cη m hch
  have hres : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t, GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP) :=
    fun PP hP => hch'.1 PP (Finset.mem_union.1 hP)
  have hun := hch'.2.1 ((R.datWp i P).Pg ∪ R.Q t) (fun PP h => Finset.mem_union.2 h)
  have hvac1 := GlobalTheory.StepVecLaw.om_vac hW (D.sp.V_sig _) (D.sp.W_sig _)
    (fun τ => GlobalTheory.ZetaLaw.isCartanInv_one_of_onb (hC.models.BV i τ)) (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)) dV dW
    fV fW hvac he (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) hun.1 hun.2 hκG (one_mem _) sV sW
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hr : (Wc D i).rank ≤ (Vc D i).rank := by omega
  have hb : D.R.r ≤ (Vc D i).rank := (datV i R.Pg (R.Q t) P m).hr
  have hQ : ∀ PP ∈ R.Q t, redFn (R.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blk2 (Wc D i).rank) := fun PP hP => by
    rw [rW]; exact parLev_q hκL.1 hP
  have hlaw := levelDatum_target_under_sourceLevel_element (Vc D i) (Wc D i) (R.βV i) (R.βW i) D.R.r D.R.t (r_le_rank_Wc i) hb hr (by rw [rW]; ring)
    (by rw [rV]; ring) R.Pg (R.Q t) P m e κ sV (fun PP hP => parLev_g hκL.1 hP) hκL.2 hQ
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hfin := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hW (cA D e) _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D R.ψ hW.std (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) dV dW (cA D e) hcc hinf f₀ hvac.2.theta) hth κ 1
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) dV dW fV fW κ 1 sV sW) _ _ (Units.ne_zero _)
    hvac1 hlaw
  rw [hfin]
  congr 1
  have hd : Disjoint (R.datWp i P).Pg (R.Q t) := (GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D T R.toLevCh A.μ0 hL t).1
  have hQf : ∀ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ *
      (m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹)))⁻¹ =
      (m PP (dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ := fun PP hP => by
    have h1 := (GlobalTheory.VecInv.TwoBlockDet.det_blocks (kP PP) _ _ 0 hr (redFn (R.βV i) PP (finE (Vc D i) κ))).1 (hQ PP hP)
    have e1 : dBlk (blk2 (Wc D i).rank) 1 (redFn (R.βV i) PP (finE (Vc D i) κ)) =
        dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ)) := by rw [rW]
    have e2 : upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹ = (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ)))⁻¹ :=
      extendOne_inv _ (hQ PP hP)
    rw [e2, map_inv, map_inv, inv_inv, h1, e1, map_mul, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel,
      one_mul]
  have hone : ∀ PP, m PP (Matrix.GeneralLinearGroup.det (redFn (R.βW i) PP (finE (Wc D i) 1))) = 1 := fun PP => by
    rw [map_one, redFn_one, map_one, map_one]
  unfold Lev.levChi levFn
  rw [extendOne_of_mem _ hκL.2]
  have hchi : (datV i R.Pg (R.Q t) P m).P.chi ⟨rTup (R.βV i) (datV i R.Pg (R.Q t) P m) (finE (Vc D i) κ), hκL.2⟩ =
      P.chi ⟨fun PP => upperLeftBlock hb (redFn (R.βV i) PP.1 (finE (Vc D i) κ)), hκL.2⟩ := rfl
  rw [hchi]
  simp only [IndefiniteRowSideFullHecke.TwistedLevelValues.datV, hone, mul_one]
  rw [← Units.coe_prod, ← Units.val_mul, ← Units.val_mul, ← Units.val_inv_eq_inv_val]
  congr 1
  rw [Finset.prod_union hd]
  have hX2 : (∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹) *
      ∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹)))⁻¹ =
      (∏ PP ∈ R.Q t, m PP (dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl hQf, Finset.prod_inv_distrib]
  generalize (∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹) = X2 at hX2 ⊢
  generalize (∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹)))⁻¹) = Z at hX2 ⊢
  obtain rfl : X2 = (∏ PP ∈ R.Q t, m PP (dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ * Z⁻¹ := by
    rw [← hX2, mul_inv_cancel_right]
  rw [Finset.prod_inv_distrib]
  simp only [zero_add]
  rw [show (R.datWp i P).Pg = R.Pg from rfl]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.SourceLaw

namespace GlobalTheory.SourceLaw

theorem sourceLevelLaw : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → SourceLevelLawC R F := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io h κ hκ Q
  have hf := om_src_law R F i t σ s P cμ cη m ω BW f₀ f c io h κ hκ
  obtain ⟨hC, -, -, -, -, hW, -, -, hpt, -, -⟩ := h
  exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ ω hC.models.inf hW _ _ _ _ f hpt κ
    (Subgroup.mem_inf.1 hκ).1 1 (one_mem _) _ hf Q

end GlobalTheory.SourceLaw
