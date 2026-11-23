import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameAtOfUnrAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMoveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedEtaTildeOfOddExponentSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTwoDiagBlocksPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharactersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

theorem char_identity {ι : Type} (Pg Q : Finset ι) (a a' d xa xb xd : ι → ℂˣ) (h : ∀ i ∈ Pg, a' i = a i) :
    ((∏ i ∈ Pg, (a i * d i)⁻¹) * ∏ i ∈ Q, xa i * xd i)⁻¹ * ((∏ i ∈ Pg, (a' i)⁻¹) * ∏ i ∈ Q, xb i) =
      (∏ i ∈ Q, (xa i)⁻¹ * xb i) * (1 * (∏ i ∈ Pg, (d i)⁻¹) * ∏ i ∈ Q, xd i)⁻¹ := by
  rw [Finset.prod_congr rfl fun i hi => congrArg (·⁻¹) (h i hi)]
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  generalize (∏ i ∈ Pg, a i) = A, (∏ i ∈ Pg, d i) = B, (∏ i ∈ Q, xa i) = C, (∏ i ∈ Q, xb i) = E, (∏ i ∈ Q, xd i) = F
  apply Units.ext
  push_cast
  field_simp

theorem smul_cancel {X : Type} {u v : X → ℂ} {ι : Type} {Q : Finset ι} {x : ι → ℂˣ} {m m' l : ℂˣ} {c : ℂ}
    (h : (∏ i ∈ Q, ((x i : ℂˣ) : ℂ)) • u = c • v) (hc : c = (m : ℂ)⁻¹ * m') (e : m⁻¹ * m' = (∏ i ∈ Q, x i) * l⁻¹) :
    u = (l : ℂ)⁻¹ • v := by
  rw [hc, ← Units.val_inv_eq_inv_val, ← Units.val_mul, e, ← Units.coe_prod, Units.val_mul, mul_smul] at h
  rw [← Units.val_inv_eq_inv_val]
  exact smul_right_injective _ (Units.ne_zero _) h

variable {D : D7}

theorem om_vec {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} {Pg Q : Finset (Pl D.host.E)}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    (hη : ∃ η, IsEtaTilde D η) (sdS : IsSelfDualC S ΛS) (sdT : IsSelfDualC T ΛT) (frS : IsFrame βS ΛS)
    (frT : IsFrame βT ΛT) (hv : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) :
    ∃ (P : Finset (Pl D.host.E)) (e : AE D) (he : e * e = e), (∀ PP, PP ∈ P ↔ PP ∈ Pg ∨ PP ∈ Q) ∧ IsIdemSum e P ∧
      (UnrOff (e + cA D e) χS → UnrOff (e + cA D e) χT → ∀ (r : ℕ) (hS : r ≤ S.rank) (hT : r ≤ T.rank), T.rank = r →
        ∀ g h, Stab S βS g → Stab T βT h →
        (∀ PP, PP ∈ Pg ∨ PP ∈ Q → redFn βS PP (finE S g) ∈ blockTri (blk2 r)) →
        (∀ PP ∈ Pg, upperLeftBlock hS (redFn βS PP (finE S g)) = upperLeftBlock hT (redFn βT PP (finE T h))) →
        (∏ PP ∈ Q, (((ξ PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hS (redFn βS PP (finE S g)))))⁻¹ *
            ξ PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)) • om (g, h) f =
          ((splitFacO χS χT (detAt e he S g) (detAt e he T h) : Circle) : ℂ) • f) := by
  obtain ⟨hvac, e, he, hth⟩ := hv
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart he
  refine ⟨_, e, hee, fun PP => @Finset.mem_union _ (_) _ _ PP, he, fun u1 u2 r hS hT hr g h sS sT tri same => ?_⟩
  have h0 := GlobalTheory.T.weil_latticeVacuum_stabilizer_splitting_characters D ψ S T ΛS ΛT χS χT om hW sdS sdT hη βS βT frS frT _ e hee he u1 u2 g h sS sT f₀ hvac.2.theta
    hvac.2.lat
  exact GlobalTheory.T.weilAction_schrodingerModel_finiteIdempotent D ψ S T ΛS ΛT χS χT om hW sdS sdT (cA D e) (by rw [← RingHom.map_mul, hee])
    (GlobalTheory.PlaceVec.infPart_cA hinf) g h (mem_latO_iff frS frT sS.2 sT.2) f₀
    (adjDatum S T βS βT Pg Q ξ (cA D e)) f _ _ hvac.2.theta hth (Circle.coe_ne_zero _) h0
    (GlobalTheory.T.adjointHalfDatum_stabilizerPair_move D S T βS βT Pg Q ξ _ r hS hT hr g h sS.2 sT.2 tri same)

variable {T0 : Type} {L : LevCh D T0} {μ0 : T0}

theorem levChi_flag_V (i : Fin D.R.m) (t : T0) {κ : GA D (Vc D i)}
    (tg : ∀ PP ∈ L.Pg, redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blkOf D.R.r D.R.t)) :
    levChi _ (L.βV i) (flagL (L.datVt i t)) κ =
      ((1 * (∏ PP ∈ L.Pg, (L.chi ((i : ℕ) + 1) PP (dBlk (blk2 D.R.r) 1 (redFn (L.βV i) PP (finE (Vc D i) κ))))⁻¹) *
        ∏ PP ∈ L.Q t, L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn (L.βV i) PP (finE (Vc D i) κ))) : ℂˣ) : ℂ) := by
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  refine congrArg Units.val (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) rfl)
  · exact extendOne_of_mem _ (Subgroup.mem_top _)
  · refine Finset.prod_congr rfl fun PP h => ?_
    rw [← (GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ D.R.t (r_le_V i) _).2.1 rV (tg PP h)]
    exact Finset.prod_range_one _

theorem om_lifts (hL : L.Is μ0) (i : Fin D.R.m) (t : T0) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {sS : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ} {f₀ f : WO (Vc D i) (Wc D i) → ℂ}
    {om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)}
    (hW : IsWeilDatumO ψ (Vc D i) (Wc D i) (L.mu t ((i : ℕ) + 1)) (L.mu t ((i : ℕ) + 1) * L.eta⁻¹) om)
    (hv : IsThPVecOf ψ θ (Vc D i) (Wc D i) sS sT (L.ΛV i) (L.ΛW i) (L.βV i) (L.βW i) L.Pg (L.Q t) (L.xiR t) f₀ f)
    {g0 : G0 L.Pg D.R.r} {κ : GA D (Vc D i)} {κ' : GA D (Wc D i)}
    (hκ : IsLevelLift (Vc D i) (L.βV i) (L.datVt i t) g0 κ) (hκ' : IsLevelLift (Wc D i) (L.βW i) (L.datWp i L.triv) g0 κ') :
    om (κ, κ') f = (levChi _ (L.βV i) (flagL (L.datVt i t)) κ)⁻¹ • f := by
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hη : IsEtaTilde D L.eta := GlobalTheory.T.isUnramifiedEtaTilde_of_odd_exponentSum D _ _ hL.eta L.C.isEta _ _ _ hW.resS hW.resT (by
    rw [rV, rW]
    obtain ⟨c, hc⟩ := D.R.t_odd
    exact ⟨D.R.r + c, by omega⟩)
  obtain ⟨P, e, hee, hP, he, hom⟩ := om_vec hW ⟨_, hη⟩ (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i))
    (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) (hL.βV i).choose_spec.1 (hL.βW i).choose_spec.1 hv
  obtain ⟨u1, u2⟩ := unrOff_mu hL t i hP he
  have sV : finE (Vc D i) κ ∈ St (L.βV i) := parLev_St hκ.2.1
  have sW : finE (Wc D i) κ' ∈ St (L.βW i) := parLev_St hκ'.2.1
  have tg : ∀ PP ∈ L.Pg, redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blkOf D.R.r D.R.t) := fun PP h =>
    parLev_g hκ.2.1 h
  have tri : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → redFn (L.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blk2 D.R.r) := fun PP h =>
    h.elim (fun h => blockTri_blkOf_le _ _ (tg PP h)) fun h => parLev_q hκ.2.1 h
  have same : ∀ PP ∈ L.Pg, upperLeftBlock (r_le_V i) (redFn (L.βV i) PP (finE (Vc D i) κ)) =
      upperLeftBlock (r_le_rank_Wc i) (redFn (L.βW i) PP (finE (Wc D i) κ')) := fun PP h =>
    (congrFun hκ.2.2 ⟨PP, h⟩).trans (congrFun hκ'.2.2 ⟨PP, h⟩).symm
  have h1 := hom u1 (u1.mul u2.inv) _ (r_le_V i) (r_le_rank_Wc i) rW κ κ' ⟨hκ.1, sV⟩ ⟨hκ'.1, sW⟩ tri same
  obtain ⟨aV, haV, hrV⟩ := exists_det_int sV
  obtain ⟨aW, haW, hrW⟩ := exists_det_int sW
  obtain ⟨mV, nV⟩ := mu_val hL t i hP he (detAt e hee _ κ) _ aV _ (isDetAt_detAt e hee _ κ) haV fun PP _ => hrV PP
  obtain ⟨mW, -⟩ := mu_val hL t i hP he (detAt e hee _ κ') _ aW _ (isDetAt_detAt e hee _ κ') haW fun PP _ => hrW PP
  rw [levChi_flag_V i t tg]
  refine smul_cancel h1 (by
    rw [splitFacO, MonoidHom.mul_apply, MonoidHom.inv_apply, nV, inv_one, mul_one, Circle.coe_mul, Circle.coe_inv,
      mV, mW]) ?_
  refine Eq.trans ?_ (char_identity L.Pg (L.Q t)
    (fun PP => L.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det (upperLeftBlock (r_le_V i)
      (redFn (L.βV i) PP (finE (Vc D i) κ)))))
    (fun PP => L.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det (redFn (L.βW i) PP (finE (Wc D i) κ')))) _ _ _ _
    fun PP h => by rw [same PP h, (GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ 0 (r_le_rank_Wc i) _).2.2 rW])
  refine congrArg₂ (· * ·) (congrArg (·⁻¹) (congrArg₂ (· * ·) ?_ ?_)) rfl
  · exact Finset.prod_congr rfl fun PP h => by
      rw [(GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ 0 (r_le_V i) _).1 (tri PP (Or.inl h)), map_mul]
  · exact Finset.prod_congr rfl fun PP h => by
      rw [(GlobalTheory.T.det_twoDiagBlocks_properties _ _ _ 0 (r_le_V i) _).1 (tri PP (Or.inr h)), map_mul]

theorem omega_lifts_vP : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.thP_ωP → R.thP_vP → ∀ i t (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → R.ωP i t (κ, κ') (R.vP i t) = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.vP i t :=
  fun _ hL _ hω hv i t _ _ _ hκ hκ' => om_lifts hL i t (hω i t) (hv i t) hκ hκ'

end GlobalTheory.VecInv
