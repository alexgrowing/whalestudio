import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCompatibilityOfClassMapsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsRc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocComp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalLanglandsSplitQp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockEig
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreLastStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ClassMapD
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.L2.Host
namespace GlobalTheory.LocCompTy
open GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
set_option maxHeartbeats 2000000 in
theorem localGlobal_compatible_at_place_alt (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (hCen : GlobalTheory.HeightCounting.Up.CenLoc D P.M) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (w : PlE D.host)
    (hw : w = D.naut.plGw k v) (e : ℚ_[D.host.g k] ≃+* w.adicCompletion D.host.E) (he : Continuous e)
    (rcw : ∀ n, QRep (D.host.g k) n → D.naut.LP w)
    (hrc : ∀ n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E))) (π : QRep (D.host.g k) n),
      Nonempty (π ≅ Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) →
      P.T.e w (rcw n π) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)) :
    ∃ (μ : ℚ_[D.host.g k]ˣ →* ℂˣ) (χ : (ZMod (D.host.g k))ˣ →* ℂˣ), TamePart μ χ ∧
      D.naut.locG (D.naut.muC i) w = rcw 1 (Rep.of (Model.detRep 1 μ)) ∧
      ∀ Q : D.naut.AV i, ∃ π : QRep (D.host.g k) D.R.nV, IrrSm π ∧ D.naut.locV i Q w = rcw D.R.nV π ∧
        ActsThrough π D.R.r D.R.t χ (D.naut.typeV i Q)
          fun a => D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) := by
  classical
  have hjr := D.nd.j_range i
  let j0 : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj0 : j0.1 + 1 = D.nd.j i := by simp only [j0]; omega
  have hsp : IsSplitPl D.host w := hw ▸ GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v
  obtain ⟨s, hs⟩ := GlobalTheory.TypeBlockPf.splitAt D _ hsp
  subst hs
  have htame : GlobalTheory.SplitWeil.IsTame ((P.tp.tup (D.nd.mu i) j0).loc s.w) :=
    GlobalTheory.MuTameQS.isTame_loc (GlobalTheory.MuTameQS.tameAt_mul ((P.cf.isMu0 j0).tame _) (P.tp.xi_tame _ _))
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_tameInflationCharacter_of_padic_iso _ _ e he _ htame
  refine ⟨_, χ, hχ, _root_.GlobalTheory.T.local_langlands_split_qp_alt_alt hPr hL D P i j0 hj0 k s.w e rcw hrc, fun Q => ?_⟩
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV (P.H.av.rep i Q) s
  have hσ' : IsLocS (n := D.R.nV) (P.H.av.S i Q) s σ := hσ
  refine ⟨Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)), GlobalTheory.T.isIrreducibleSmooth_pullback_padic_ringIso _ _ e he _ σ, ?_, ?_⟩
  · apply (P.T.e s.w).injective
    rw [hrc _ σ _ ⟨CategoryTheory.Iso.refl _⟩, D.nbc.embAV_loc, P.H.emb]
    exact P.au _ _ _ _ s _ hσ'
  obtain ⟨c, T, hc, hci, -, -, -⟩ := hσ
  set ξ := (P.tp.tup (D.nd.mu i) j0).loc s.w with hξ
  have hT : ∀ F, F ∈ D.naut.typeV i Q ↔
      (P.M.loc i).real F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := fun F => by
    rw [P.H.av.typeV]; exact Submodule.mem_comap
  let J := {φ : (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) →ₗ[ℂ] σ.V // ∀ x, TrivOutside {s.v} x →
    ∀ f' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q),
      φ (NG.rt D.host.E D.R.nV x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) (φ f')}
  let ι : D.naut.typeV i Q →ₗ[ℂ] (J → σ.V) :=
    LinearMap.pi fun φ => φ.1.comp ((P.M.loc i).real.comp (D.naut.typeV i Q).subtype)
  have hpar : ∀ (φ : J) (F : D.naut.typeV i Q),
      IsParVec (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) D.R.r D.R.t χ (φ.1 ((P.M.loc i).real F)) := by
    intro φ F
    refine GlobalTheory.T.isParahoricTypeVector_of_blockTypeVector_padic_iso _ _ e he ξ χ hχ D.R.r D.R.t σ.V σ.ρ _ ?_
    refine GlobalTheory.BlockType.isBlockVec_of (r := D.R.r) (t := D.R.t) ξ σ.ρ _ fun h hh => ?_
    obtain ⟨x, hx, hxe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
    have hmap : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) = h := by
      rw [hxe]; exact Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)
    have hF := (hT F).1 F.2
    have hh2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈
        GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := by rw [hmap]; exact hh
    have h3 := φ.2 x hx _ hF
    rw [_root_.GlobalTheory.LocCompTy.blockEig_alt hL D P i Q k v j0 hj0 s hw c hc hci F x hx hh2, map_smul] at h3
    rw [← hmap]; exact h3.symm
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro F hF
    by_contra hne
    have h1 : (P.M.loc i).real F ≠ 0 := fun h0 =>
      hne (Subtype.ext ((P.M.loc i).real_inj (h0.trans (map_zero _).symm)))
    obtain ⟨φ, hφ, hφe⟩ := GlobalTheory.T.isotypic_local_component_fixed D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s σ hσ' c hc hci _
      ((hT F).1 F.2) h1
    exact hφ (congrFun (LinearMap.mem_ker.1 hF) ⟨φ, hφe⟩)
  refine ⟨J, ι, hinj, fun F φ => hpar φ F, fun a ha F => ?_⟩
  have hzc : ∀ b, a * b = b * a := fun b => (Subalgebra.mem_center_iff.1 ha b).symm
  have hcz := GlobalTheory.SeriesSupportTest.atPlace_central D k v a hzc
  obtain ⟨L, hLift, hCL⟩ := hCen i
  have e0 : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F) =
      actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) ((P.M.loc i).real F) := by
    rw [NTypes.onMt, dif_pos hcz]; exact hCL ⟨_, hcz⟩ F
  let g : GL (Fin D.R.r) (ZMod (D.host.g k)) → G0g D.nd := fun h =>
    Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ h
  have hsum : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) ((P.M.loc i).real F) =
      ∑ h, a.coeff h • NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) := by
    unfold actSum Formalism.MainNotions.ArithmeticCylinders.atPlace
    rw [MonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapDomain_index
      (h := fun g c => c • NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F))
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  have hg : ∀ h, ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧
      IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧
      NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := fun h =>
    _root_.GlobalTheory.T.lift_through_completion_iso_alt hL D P i Q k v s hw c hc hci L hLift F F.2 h (g h) (by simp [g])
      (fun kv hkv => by simp [g, Pi.mulSingle_eq_of_ne hkv])
  choose xs hxs using hg
  have hF := (hT F).1 F.2
  have e1 : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F) =
      ∑ h, a.coeff h • NG.rt D.host.E D.R.nV (xs h) ((P.M.loc i).real F) := by
    rw [e0, hsum]; exact Finset.sum_congr rfl fun h _ => by rw [(hxs h).2.2]
  have hmem : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F ∈ D.naut.typeV i Q := by
    rw [hT, e1]
    exact Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (rt_mem_isoTyp _ _ _ hF)
  refine ⟨hmem, fun φ => ?_⟩
  have hu := (hpar φ F).1
  change φ.1 ((P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F)) =
    actTop (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) D.R.r D.R.t a (φ.1 ((P.M.loc i).real F))
  rw [e1, map_sum, actTop, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, φ.2 _ (hxs h).1 _ hF, LinearMap.smul_apply, MonoidHom.comp_apply]
  congr 1
  exact GlobalTheory.T.blockLift_action_on_principalCongruenceFixedVectors _ _ e he D.R.r D.R.t σ.V σ.ρ _ hu h _ (hxs h).2.1
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL P.T I rc → (∀ k v, _root_.GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v)) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → _root_.GlobalTheory.SerSys.LocalCompatibility D rc := by
  intro hPr hL D P I rc hRc hCM hCen
  exact ⟨hCM, fun i k v => _root_.GlobalTheory.LocCompTy.localGlobal_compatible_at_place_alt hPr hL D P hCen i k v _ rfl (I.i k v) (I.cont k v) (rc k v)
    fun n σ π h => hRc k v n σ π h⟩
end GlobalTheory.LocCompTy
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locComp_of_isRc_of_classMap_of_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL P.T I rc → (∀ k v, _root_.GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v)) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → _root_.GlobalTheory.SerSys.LocalCompatibility D rc := by
  first | exact @_root_.GlobalTheory.LocCompTy.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LocCompTy.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LocCompTy.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
