import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedThetaCharactersRestrictionRamificationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZetaLaw

open GlobalTheory.AdjDatumMove

variable {D : D7}

open Matrix in
open scoped ComplexOrder in

theorem isCartanInv_one_of_onb {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : IsCartanInv G 1 := by
  obtain ⟨e, he, h1, -⟩ := h
  have h2 : Bᴴ * G * B = 1 := by
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases he a with h | h
    · simp [h.1]
    · exact absurd a.2 (not_lt.2 h.2)
  have hu : IsUnit B := IsUnit.of_mul_eq_one_right _ h2
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h3 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h4 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_one]
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    calc G = ((B⁻¹)ᴴ * Bᴴ) * G * (B * B⁻¹) := by rw [h3, h4, Matrix.one_mul, Matrix.mul_one]
      _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hu))

theorem topL_mul_right {κ : Type} [CommRing κ] {a b : ℕ} (y : Matrix (Fin b) (Fin a) κ) (γ : Matrix (Fin a) (Fin a) κ) :
    topL a (y * γ) = topL a y * γ := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, Matrix.mul_apply, hi]
  · simp [topL, Matrix.mul_apply, hi]

theorem lowZero_mul_right {κ : Type} [CommRing κ] {a b : ℕ} {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero a y)
    (γ : Matrix (Fin a) (Fin a) κ) : LowZero a (y * γ) := by
  intro i j hi _
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [hy i l hi l.2, zero_mul]

abbrev GCond {a b : ℕ} (L : LevDat D.host.E ℂ a) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : Prop :=
  (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧ ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (kP PP.1),
    (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
    (∀ PP : ↥L.Pg, g PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (g PP)) ∈ L.P.H

theorem gCond_mul {a b : ℕ} (L : LevDat D.host.E ℂ a) (γ : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP))
    (hγ : ∀ PP ∈ L.Pg, γ PP ∈ blockTri (blkOf L.r L.t)) (hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) ∈ L.P.H)
    (y z : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hz : ∀ PP, z PP = y PP * (γ PP).val)
    (h : GCond L y) : GCond L z := by
  obtain ⟨h1, g, h2, h3, h4⟩ := h
  refine ⟨fun PP hP' => (hz PP).symm ▸ lowZero_mul_right (h1 PP hP') _, fun PP => g PP * γ PP.1, fun PP => ?_,
    fun PP => mul_mem (h3 PP) (hγ PP.1 PP.2), ?_⟩
  · rw [Units.val_mul, h2, hz, topL_mul_right]
  · have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (g PP * γ PP.1)) =
        (fun PP => upperLeftBlock L.hr (g PP)) * (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) := by
      funext PP
      exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (h3 PP)) (blockTri_blkOf_le _ _ (hγ PP.1 PP.2))
    rw [e]
    exact mul_mem h4 hP

theorem omegaG_mul_right {a b : ℕ} (L : LevDat D.host.E ℂ a) (hs : L.s = 0)
    (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (γ : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP))
    (hγ : ∀ PP ∈ L.Pg, γ PP ∈ blockTri (blkOf L.r L.t)) (hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) ∈ L.P.H)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaG L χj (fun PP => y PP * (γ PP).val) =
      ((L.P.chi ⟨_, hP⟩ : ℂˣ) : ℂ) * (∏ PP ∈ L.Pg, ((χj PP (Matrix.GeneralLinearGroup.det (γ PP)) : ℂˣ) : ℂ)⁻¹) *
        omegaG L χj y := by
  have hγi : ∀ PP ∈ L.Pg, (γ PP)⁻¹ ∈ blockTri (blkOf L.r L.t) := fun PP h => inv_mem (hγ PP h)
  have hPi : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)⁻¹) ∈ L.P.H := by
    have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)⁻¹) = (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1))⁻¹ := by
      funext PP
      exact extendOne_inv _ (blockTri_blkOf_le _ _ (hγ PP.1 PP.2))
    rw [e]
    exact inv_mem hP
  unfold omegaG
  by_cases hy : GCond L y
  · have hy' : GCond L (fun PP => y PP * (γ PP).val) := gCond_mul L γ hγ hP y _ (fun _ => rfl) hy
    rw [dif_pos hy', dif_pos hy]
    have key : ∀ PP : ↥L.Pg, hy'.2.choose PP = hy.2.choose PP * γ PP.1 := fun PP => Units.ext (by
      rw [Units.val_mul, hy'.2.choose_spec.1 PP, hy.2.choose_spec.1 PP, topL_mul_right])
    have hc : (⟨fun PP => upperLeftBlock L.hr (hy'.2.choose PP), hy'.2.choose_spec.2.2⟩ : L.P.H) =
        ⟨fun PP => upperLeftBlock L.hr (hy.2.choose PP), hy.2.choose_spec.2.2⟩ * ⟨_, hP⟩ :=
      Subtype.ext (funext fun PP => by
        show upperLeftBlock L.hr (hy'.2.choose PP) = upperLeftBlock L.hr (hy.2.choose PP) * upperLeftBlock L.hr (γ PP.1)
        rw [key]
        exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (hy.2.choose_spec.2.1 PP)) (blockTri_blkOf_le _ _ (hγ PP.1 PP.2)))
    rw [hc, map_mul]
    simp only [hs, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one, key, map_mul, Units.val_mul, mul_inv]
    rw [Finset.prod_mul_distrib, ← Finset.prod_coe_sort L.Pg (fun PP => ((χj PP (Matrix.GeneralLinearGroup.det (γ PP)) : ℂˣ) : ℂ)⁻¹)]
    ring
  · have hy' : ¬ GCond L (fun PP => y PP * (γ PP).val) := fun h => hy (gCond_mul L (fun PP => (γ PP)⁻¹) hγi hPi _ y
      (fun PP => by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]) h)
    rw [dif_neg hy', dif_neg hy, mul_zero]

theorem omegaQ_mul_right {n r : ℕ} (hr : r ≤ n) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (γ : ∀ PP : Pl D.host.E, GL (Fin r) (kP PP)) (u : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)) :
    omegaQ Q r ξ (-1) (fun PP => u PP * (γ PP).val) =
      (∏ PP ∈ Q, ((ξ PP (Matrix.GeneralLinearGroup.det (γ PP)) : ℂˣ) : ℂ)⁻¹) * omegaQ Q r ξ (-1) u := by
  have h := omegaQ_mul hr Q ξ (fun PP => (1 : GL (Fin n) (kP PP))) (fun PP => (γ PP)⁻¹) (fun _ _ => one_mem _) u
  simp only [inv_inv, Units.val_one, Matrix.one_mul] at h
  rw [h]
  congr 1
  refine Finset.prod_congr rfl fun PP _ => ?_
  have e1 : upperLeftBlock hr (1 : GL (Fin n) (kP PP)) = 1 := blockDiagonalExtendByOnePrimeField_one _ _
  rw [e1, map_one, map_one, inv_one, one_mul, map_inv, map_inv, Units.val_inv_eq_inv_val]

open Formalism.IndefR.Lev (finE) in

theorem levDatum_actO (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (L : LevDat D.host.E ℂ T.rank) (hs : L.s = 0) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (e : AE D) (hr : T.rank ≤ S.rank) (h : GA D T) (sh : finE T h ∈ St βT)
    (hγ : ∀ PP ∈ L.Pg, redFn βT PP (finE T h) ∈ blockTri (blkOf L.r L.t))
    (hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (redFn βT PP.1 (finE T h))) ∈ L.P.H) (x : WO S T) :
    levDatum S T βS βT L Q m e (actO S T 1⁻¹ h⁻¹ x) =
      ((L.P.chi ⟨_, hP⟩ : ℂˣ) : ℂ) *
        (∏ PP ∈ L.Pg, ((m PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)⁻¹) *
        (∏ PP ∈ Q, ((m PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)⁻¹) *
        levDatum S T βS βT L Q m e x := by
  have s1 : finE S (1 : GA D S) ∈ St βS := by rw [map_one]; exact one_mem _
  have s1' : finE S (1 : GA D S)⁻¹ ∈ St βS := by rw [inv_one]; exact s1
  have sh' : finE T h⁻¹ ∈ St βT := by rw [map_inv]; exact inv_mem sh
  have hG1 : ∀ PP, redFn βS PP (finE S (1 : GA D S)⁻¹) = 1 := fun PP => by rw [inv_one, map_one, redFn_one]
  have hH : ∀ PP, (redFn βT PP (finE T h⁻¹))⁻¹ = redFn βT PP (finE T h) := fun PP => by
    rw [map_inv, redFn_inv sh, inv_inv]
  unfold levDatum
  by_cases hx : IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x)
  · have h1 := red_actO S T βS βT s1' sh' hx.2
    have h2 : ∀ PP, redM PP (frMapAdj S T βS βT (actO S T 1⁻¹ h⁻¹ x)) =
        redM PP (frMapAdj S T βS βT x) * (redFn βT PP (finE T h)).val := fun PP => by
      rw [h1.2 PP, hG1 PP, hH PP, Units.val_one, Matrix.one_mul]
    rw [if_pos hx, if_pos ⟨isHalf_actO' _ _ hx.1, h1.1⟩, funext h2,
      omegaG_mul_right L hs m (fun PP => redFn βT PP (finE T h)) hγ hP, omegaQ_mul_right hr Q m]
    ring
  · rw [if_neg hx, if_neg, mul_zero]
    rintro ⟨h1, h2⟩
    have e' := GlobalTheory.AdelicLatMove.actO_actO_inv S T (1 : GA D S) h x
    have h3 := isHalf_actO' (1 : GA D S) h h1
    have h4 := (red_actO S T βS βT s1 sh h2).1
    rw [e'] at h3 h4
    exact hx ⟨h3, h4⟩

open Formalism.IndefR.Lev (finE) in
set_option maxHeartbeats 1000000 in

theorem zeta_law : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ k ∈ levG (Wc D i) (R.βW i) (R.datWp i P), ω (1, k) f = levChi (Wc D i) (R.βW i) (R.datWp i P) k • f := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h k hk
  classical
  obtain ⟨hC, -, -, -, hch, hW, -, hlv, -, -, -⟩ := h
  rw [GlobalTheory.FinZeta.isLevelVec_iff] at hlv
  obtain ⟨hvac, e, he, hth⟩ := hlv
  have hL := hC.lev
  have hkG : k ∈ GfC (Wc D i) := (Subgroup.mem_inf.1 hk).1
  have hkL : finE (Wc D i) k ∈ lev D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i P) := (Subgroup.mem_inf.1 hk).2
  have sW : finE (Wc D i) k ∈ St (R.βW i) := parLev_St hkL.1
  have sV : finE (Vc D i) 1 ∈ St (R.βV i) := by rw [map_one]; exact one_mem _
  have dV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i)
  have dW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)
  have fV := (hL.βV i).choose_spec.1
  have fW := (hL.βW i).choose_spec.1
  have hch' := GlobalTheory.T.conjugatedThetaCharacters_restriction_ramification R hL i t s cμ cη m hch
  have hres : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t, GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP) :=
    fun PP hP => hch'.1 PP (Finset.mem_union.1 hP)
  have hun := hch'.2.1 ((R.datWp i P).Pg ∪ R.Q t) (fun PP h => Finset.mem_union.2 h)
  have hvac1 := GlobalTheory.StepVecLaw.om_vac hW (D.sp.V_sig _) (D.sp.W_sig _)
    (fun τ => isCartanInv_one_of_onb (hC.models.BV i τ)) (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)) dV dW fV fW hvac he
    (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) hun.1 hun.2 (one_mem _) hkG sV sW
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hr : (Wc D i).rank ≤ (Vc D i).rank := by omega
  have hlaw := levDatum_actO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (R.datWp i P) rfl (R.Q t) m e hr k sW
    (fun PP hP => parLev_g hkL.1 hP) hkL.2
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hfin := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hW (cA D e) _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D R.ψ hW.std (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) dV dW (cA D e) hcc hinf f₀ hvac.2.theta) hth 1 k
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) dV dW fV fW 1 k sV sW) _ _ (Units.ne_zero _)
    hvac1 hlaw
  rw [hfin]
  congr 1
  have hd : Disjoint (R.datWp i P).Pg (R.Q t) := (GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D T R.toLevCh A.μ0 hL t).1
  have hone : ∀ PP, redFn (R.βV i) PP (finE (Vc D i) 1) = 1 := fun PP => by rw [map_one, redFn_one]
  unfold levChi levFn
  rw [extendOne_of_mem _ hkL.2]
  have hs0 : (R.datWp i P).s = 0 := rfl
  have hQ0 : (R.datWp i P).Q = ∅ := rfl
  simp only [map_one, redFn_one, inv_one, one_mul, hs0, hQ0, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one,
    mul_one, Finset.prod_union hd, Units.val_mul, Units.coe_prod]
  have hne : ∀ s : Finset (Pl D.host.E),
      (∏ PP ∈ s, ((m PP (Matrix.GeneralLinearGroup.det (redFn (R.βW i) PP (finE (Wc D i) k))) : ℂˣ) : ℂ)) ≠ 0 :=
    fun s => Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  field_simp
  rw [mul_comm (_ * _), mul_div_assoc, div_self (mul_ne_zero (hne _) (hne _)), mul_one]
  rfl

end GlobalTheory.ZetaLaw
