import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionVacuumEqResidueDetCharOfFrameStabilizeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepSchrodingerModelHalfSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReductionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesLocalDatumBlockTriangularLawStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistPlacesLocalDatumBlockTriangularLawStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFixedNonsplitPlaceOfCharacterFrameStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

variable {D : D7}

theorem resEta_one_of_step {μ : ℕ → ((AE D)ˣ →* Circle)} {η : (AE D)ˣ →* Circle} {n a b : ℕ}
    (h1 : ResEta D (Lift.chrStep μ η n).1 a) (h2 : ResEta D (Lift.chrStep μ η n).2 b) (hab : (a + b) % 2 = 1 % 2) :
    ResEta D η 1 := by
  unfold Lift.chrStep at h1 h2
  split_ifs at h1 h2
  · have h := resEta_parity (resEta_mul (resEta_inv h1) h2) hab
    rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right] at h
  · have h := resEta_parity (resEta_mul h1 (resEta_inv h2)) hab
    rwa [mul_inv, inv_inv, mul_inv_cancel_left] at h

theorem levChi_flag_datY (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (κ : GA D V) :
    levChi V β (flagL (datY V.rank r t j hr Pg Q P χ ξ Frm.B)) κ =
      ((∏ PP ∈ Pg, ∏ c ∈ Finset.range j, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (redFn β PP (finE V κ))) : ℂˣ) : ℂ) *
        ∏ PP ∈ Q, ((ξ PP (dBlk (blk2 r) 1 (redFn β PP (finE V κ))) : ℂˣ) : ℂ)⁻¹ := by
  have h := subgroupCharExtension_one_apply (N := ℂˣ) (⊤ : Subgroup (G0 Pg r)) (rTup β (datY V.rank r t j hr Pg Q P χ ξ Frm.B) (finE V κ))
  unfold levChi levFn
  rw [Units.val_mul, Units.val_mul]
  refine congrArg₂ _ ((congrArg₂ _ (congrArg Units.val h) rfl).trans ?_) ?_
  · rw [Units.val_one, one_mul]; rfl
  · rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun PP _ => ?_
    exact Units.val_inv_eq_inv_val _

theorem vacScal_resChr {T0 : Type} (L : LevCh D T0) (t : T0) (n : ℕ) (hd : Disjoint L.Pg (L.Q t)) {S T : HSp D}
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) (g : GA D S) (h : GA D T) :
    vacScal βS βT P (resChr L t n) (resChr L t n) g h =
      (∏ PP ∈ L.Pg, (((L.chi n PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ) *
        ((L.chi n PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)⁻¹)) *
      ∏ PP ∈ L.Q t, (((L.xiR t PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ)⁻¹ *
        ((L.xiR t PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)) := by
  have e : P = L.Pg.disjUnion (L.Q t) hd := Finset.ext fun PP => (hP PP).trans Finset.mem_disjUnion.symm
  unfold vacScal
  rw [e, Finset.prod_disjUnion]
  refine congrArg₂ _ (Finset.prod_congr rfl fun PP hPP => ?_) (Finset.prod_congr rfl fun PP hPP => ?_)
  · simp only [resChr, if_pos hPP, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
  · simp only [resChr, if_neg (Finset.disjoint_right.1 hd hPP)]

theorem regroup (A B G q q' H : ℂ) : A * B⁻¹ * G * (q * q' * H) = A * q * ((B * q'⁻¹)⁻¹ * (G * H)) := by
  rw [mul_inv, inv_inv]; ring

theorem step_law {T0 : Type} (L : LevCh D T0) {μ0 : T0} (hL : L.Is μ0) (t : T0) (j n : ℕ) (hn : n = j + 1) (hj : j < D.R.m)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} (hS : S.SigOK) (hT : T.SigOK)
    (ha : D.R.r ≤ S.rank) (hb : D.R.r ≤ T.rank) (ea : S.rank = D.R.r + j * D.R.t) (eb : T.rank = D.R.r + n * D.R.t)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hsS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hsT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} {NS NT : ℕ}
    (hβS : IsSDFrame S βS ΛS NS) (hβT : IsSDFrame T βT ΛT NT)
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T (Lift.chrStep (L.mu t) L.eta n).1 (Lift.chrStep (L.mu t) L.eta n).2 om)
    {f₀ f : WO S T → ℂ}
    (hf : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT
      (datY S.rank D.R.r D.R.t j ha L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B) (L.chi n) (L.Q t) (L.xiR t) f₀ f)
    (g0 : G0 L.Pg D.R.r) (κ : GA D S) (κ' : GA D T)
    (hκ : IsLevelLift S βS (datY S.rank D.R.r D.R.t j ha L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B) g0 κ)
    (hκ' : IsLevelLift T βT (datY T.rank D.R.r D.R.t n hb L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B) g0 κ') :
    (levChi S βS (flagL (datY S.rank D.R.r D.R.t j ha L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B)) κ)⁻¹ • om (κ, κ') f =
      (levChi T βT (flagL (datY T.rank D.R.r D.R.t n hb L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B)) κ')⁻¹ • f := by
  classical
  subst hn
  obtain ⟨hv, e, he', ⟨Tm, hTm⟩, hall⟩ := hf
  obtain ⟨P, he, hP⟩ : ∃ P, IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t :=
    ⟨_, he', fun PP => Finset.mem_union⟩
  have dS := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D S βS ΛS NS hβS
  have dT := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D T βT ΛT NT hβT
  obtain ⟨cS, fS, -⟩ := hβS
  obtain ⟨cT, fT, -⟩ := hβT
  obtain ⟨hd, htame⟩ := GlobalTheory.T.stepSplittingCharacters_tame_levelResidue D T0 L μ0 hL t ⟨j, hj⟩
  obtain ⟨t1, t2⟩ := htame e P hP he
  have tS : TameOn (Lift.chrStep (L.mu t) L.eta (j + 1)).1 e P (resChr L t (j + 1)) := by
    unfold Lift.chrStep; split_ifs
    · exact t2
    · exact t1
  have tT : TameOn (Lift.chrStep (L.mu t) L.eta (j + 1)).2 e P (resChr L t (j + 1)) := by
    unfold Lift.chrStep; split_ifs
    · exact t1
    · exact t2
  have hη : ResEta D L.eta 1 := resEta_one_of_step hW.resS hW.resT (by
    obtain ⟨c, hc⟩ := D.R.t_odd
    rw [ea, eb, add_mul, one_mul]
    generalize j * D.R.t = w
    omega)
  have kS := parLev_St hκ.2.1
  have kT := parLev_St hκ'.2.1
  have hvac := GlobalTheory.T.weilAction_vacuum_eq_residueDetChar_of_frameStabilizer D ψ S T _ _ om θ sS sT ΛS ΛT βS βT e _ _ _ f₀ hW hθ hS hT hsS hsT dS dT fS fT he tS tT
    (GlobalTheory.T.vacuum_fixed_nonsplit_place_of_characterFrame D L.C L.eta hL.eta hη ψ S T _ _ om ΛS ΛT hW dS dT) hv κ hκ.1 κ' hκ'.1 kS kT
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO dS.1 dT.1 βS βT
  have hSB := GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
      (GlobalTheory.PlaceDatum.exists_den_frMapO dS.1.fg dT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ P
      (fun y => omegaG (datY S.rank D.R.r D.R.t j ha L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B) (L.chi (j + 1)) y *
        omegaQ (L.Q t) D.R.r (L.xiR t) 1 y) fun y y' h => by
        rw [GlobalTheory.PlaceDatum.omegaG_congr _ _ y y' fun PP hPP => h PP ((hP PP).2 (Or.inl hPP)),
          GlobalTheory.PlaceDatum.omegaQ_congr _ _ _ 1 y y' fun PP hPP => h PP ((hP PP).2 (Or.inr hPP))]
  have hsch := GlobalTheory.T.weilRep_schrodingerModel_half_substitution D ψ S T _ _ om ΛS ΛT e f₀ Tm hW dS dT (GlobalTheory.PlaceDatum.idemSum_mul_self he) hinf hv.2.theta hTm
    κ κ' _ (GlobalTheory.T.mem_completedHomLattice_iff_frameStabiliser_action D S T ΛS ΛT βS βT dS.1 dT.1 fS fT κ κ' kS kT _) hvac _ hSB
  have hfe := hall Tm hTm
  have hne := levChi_ne_zero (β := βS)
    (flagL (datY S.rank D.R.r D.R.t j ha L.Pg (L.Q t) L.triv L.chi (L.xiR t) Frm.B)) κ
  rw [hfe]
  refine (congrArg _ hsch).trans ?_
  rw [smul_smul, ← map_smul, ← map_smul]
  congr 1
  funext x
  obtain ⟨i1, i2⟩ := GlobalTheory.T.frameMatrix_movedHom_integral_reduction D S T βS βT κ κ' kS kT x
  have i3 : IsHalf e (actO S T κ⁻¹ κ'⁻¹ x) ↔ IsHalf e x := by
    refine ⟨fun h => ?_, fun h => GlobalTheory.SplitHecke.isHalf_actO _ _ h⟩
    have := GlobalTheory.SplitHecke.isHalf_actO κ κ' h
    rwa [GlobalTheory.AdelicLatMove.actO_actO_inv] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hx : IsHalf e x ∧ IsIntM (frMapO S T βS βT x)
  · rw [if_pos hx, if_pos ⟨i3.2 hx.1, i1.2 hx.2⟩]
    have a1 := GlobalTheory.T.typePlaces_localDatum_blockTriangular_law D _ _ D.R.r D.R.t j ha hb ea eb L.Pg (L.Q t) L.chi (L.xiR t)
      (fun PP => redFn βS PP (finE S κ)) (fun PP => redFn βT PP (finE T κ')) _ _
      (fun PP hP => parLev_g hκ.2.1 hP) (fun PP hP => parLev_g hκ'.2.1 hP)
      (fun PP hP => (congrFun hκ.2.2 ⟨PP, hP⟩).trans (congrFun hκ'.2.2 ⟨PP, hP⟩).symm) (fun PP _ => i2 hx.2 PP)
    have a2 := GlobalTheory.T.twistPlaces_localDatum_blockTriangular_law D _ _ D.R.r ha hb (L.Q t) (L.xiR t) 1
      (fun PP => redFn βS PP (finE S κ)) (fun PP => redFn βT PP (finE T κ')) _ _
      (fun PP hP => parLev_q hκ.2.1 hP) (fun PP hP => parLev_q hκ'.2.1 hP) (fun PP _ => i2 hx.2 PP)
    rw [zpow_one, zpow_one, Finset.prod_mul_distrib (s := L.Q t)
      (f := fun PP => ((L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn βS PP (finE S κ))) : ℂˣ) : ℂ)⁻¹)] at a2
    rw [vacScal_resChr L t (j + 1) hd βS βT P hP, mul_assoc, mul_mul_mul_comm,
      inv_mul_eq_iff_eq_mul₀ hne]
    refine (congrArg₂ _ a1 a2).trans ?_
    rw [levChi_flag_datY, levChi_flag_datY, Finset.prod_inv_distrib (s := L.Q t)
      (f := fun PP => ((L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn βT PP (finE T κ'))) : ℂˣ) : ℂ))]
    exact regroup _ _ _ _ _ _
  · rw [if_neg hx, if_neg fun h => hx ⟨i3.1 h.1, i1.1 h.2⟩, mul_zero, mul_zero]

theorem last_step_law : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.chain_ωX → R.chain_vX → ∀ t (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) g0 κ → IsLevelLift D.sp.X' R.βX (R.datXt t) g0 κ' → (levChi _ (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ)⁻¹ • R.ωX t (κ, κ') (R.vX t) = (levChi _ R.βX (flagL (R.datXt t)) κ')⁻¹ • R.vX t := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hθ hω hv t g0 κ κ' hκ hκ'
  have hm := D.R.two_le_m
  exact step_law R.toLevCh hL t (D.R.m - 1) D.R.m (by omega) (by omega) hθ (D.sp.Y_sig _) D.sp.X'_sig (r_le_Y _) r_le_X
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left (Nat.sub_le _ _)]; rfl) D.sp.X'_rank
    (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (hL.βY _ (by omega)) hL.βX (hω t) (hv t)
    g0 κ κ' hκ hκ'

end GlobalTheory.StepLaw

end
