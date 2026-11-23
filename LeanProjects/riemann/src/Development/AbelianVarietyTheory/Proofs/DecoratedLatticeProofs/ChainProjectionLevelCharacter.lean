import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastStepVectorLiftPairFlagLevelCharacters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepLevelP.IoLevPf

theorem multT_val {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) (u : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : SmT M) :
    (∀ γ ∈ GQ V, ∀ g, u v (γ * g) = u v g) ∧ ∀ k ∈ J, ∀ g, u v (g * k) = χ k * u v g := by
  have h1 := (mem_multT θ M J χ u).1 hu
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h2 := GlobalTheory.mult_value_left_cont_level θ M J χ _ h1 f
    have h3 : ∀ g, u (PiTensorProduct.tprod ℂ f) g = (PiTensorProduct.lift.symm u) f g := fun g => by simp
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_⟩
    · rw [map_smul, Pi.smul_apply, Pi.smul_apply, h3, h3, h2.1 γ hγ g]
    · rw [map_smul, Pi.smul_apply, Pi.smul_apply, h3, h3, h2.2.2 k hk g, smul_eq_mul, smul_eq_mul]
      ring
  | add x y hx hy =>
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_⟩
    · rw [map_add, Pi.add_apply, Pi.add_apply, hx.1 γ hγ g, hy.1 γ hγ g]
    · rw [map_add, Pi.add_apply, Pi.add_apply, hx.2 k hk g, hy.2 k hk g]
      ring

end GlobalTheory.StepLevelP.IoLevPf

namespace GlobalTheory.StepLevelP

set_option maxHeartbeats 800000 in

theorem io_levChi : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ t j, j + 1 < D.R.m → ∀ F : (pk W).CC t (j + 1), F.1 ∈ CP (pk W) (lvP W) t (j + 1) → ∀ κ ∈ levS (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)), ∀ φ x g, ((pk W).ioY t j F).1 ((pk W).ItY j φ x) (g * κ) = levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) κ * ((pk W).ioY t j F).1 ((pk W).ItY j φ x) g := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj F hF κ hκ φ x g
  have hC := hW.bot.hyp.2.2.2.1
  have hL : (pk W).Is W.P.A3.A.μ0 := hC.lev
  have hθ : IsInfFam (pk W).θ := hC.models.inf
  have hio := hC.chain.ioY t j (by omega)
  have hκG : κ ∈ GfC (Yc D j) := hκ.1
  have hκP : Lev.finE (Yc D j) κ ∈ parLev D.sp.cm (Yc D j).gram ((pk W).βY j) ((pk W).datYt t j (pk W).triv) := hκ.2.1
  have hκH : rTup ((pk W).βY j) ((pk W).datYt t j (pk W).triv) (Lev.finE (Yc D j) κ) ∈ (lvP W).H := hκ.2.2
  have hκl : IsLevelLift (Yc D j) ((pk W).βY j) ((pk W).datYt t j (pk W).triv)
      (rTup ((pk W).βY j) ((pk W).datYt t j (pk W).triv) (Lev.finE (Yc D j) κ)) κ := ⟨hκG, hκP, rfl⟩
  obtain ⟨κ', hκ'⟩ := GlobalTheory.ChainLiftEquiv.liftsExist_chain (pk W) hL t (j + 1) hj
    (rTup ((pk W).βY j) ((pk W).datYt t j (pk W).triv) (Lev.finE (Yc D j) κ))
  have hj' : j < D.R.m := by omega
  have hlaw := GlobalTheory.StepLaw.step_law (pk W).toLevCh hL t j (j + 1) rfl hj' hθ (D.sp.Y_sig _) (D.sp.Y_sig _) (r_le_Y _) (r_le_Y _)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj'.le]; rfl)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj.le]; rfl)
    (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (hL.βY j hj') (hL.βY (j + 1) hj)
    (hC.chain.ωY t j hj) (hC.chain.vY t j hj) _ κ κ' hκl hκ'
  have hsS : levChi (Yc D j) ((pk W).βY j) (flagL ((pk W).datYt t j (pk W).triv)) κ ≠ 0 := levChi_ne_zero _ _
  have hsT : levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) (flagL ((pk W).datYt t (j + 1) (pk W).triv)) κ' ≠ 0 :=
    levChi_ne_zero _ _
  have hlaw' : (levChi (Yc D j) ((pk W).βY j) (flagL ((pk W).datYt t j (pk W).triv)) κ)⁻¹ •
      (pk W).ωY t j (κ, κ') ((pk W).vY t j) =
      (levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) (flagL ((pk W).datYt t (j + 1) (pk W).triv)) κ')⁻¹ • (pk W).vY t j := hlaw
  have hv : (pk W).ωY t j (κ, κ') ((pk W).vY t j) =
      (levChi (Yc D j) ((pk W).βY j) (flagL ((pk W).datYt t j (pk W).triv)) κ *
        (levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) (flagL ((pk W).datYt t (j + 1) (pk W).triv)) κ')⁻¹) •
        (pk W).vY t j := by
    rw [mul_smul, ← hlaw', smul_smul, mul_inv_cancel₀ hsS, one_smul]
  have hpt := GlobalTheory.FiniteFock.om_pureTensorO_of_finite (pk W).ψ (pk W).θ _ _ _ _ ((pk W).ωY t j) hθ (hC.chain.ωY t j hj)
    _ _ _ _ ((pk W).vY t j) (hC.chain.ptY t j hj) κ hκG κ' hκ'.1 _ hv φ
  have hker := GlobalTheory.thetaKO_rat_left_and_eigen_right (pk W).ψ _ _ _ _ ((pk W).ωY t j) (hC.chain.ωY t j hj)
    ((pk W).ptY t j φ) (hC.chain.ptY t j hj φ)
  have hκ'H : rTup ((pk W).βY (j + 1)) ((pk W).datYt t (j + 1) (pk W).triv) (Lev.finE (Yc D (j + 1)) κ') ∈ (lvP W).H := by
    rw [hκ'.2.2]; exact hκH
  have hκ'P : κ' ∈ levS (Yc D (j + 1)) ((pk W).βY (j + 1)) ((pk W).datYt t (j + 1) (lvP W)) := ⟨hκ'.1, hκ'.2.1, hκ'H⟩
  have e1 : levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) κ =
      (((lvP W).chi ⟨_, hκH⟩ : ℂˣ) : ℂ) * levChi (Yc D j) ((pk W).βY j) (flagL ((pk W).datYt t j (pk W).triv)) κ := by
    unfold levChi
    erw [levFn_withP (L := (pk W).datYt t j (pk W).triv) (lvP W), extendOne_of_mem _ hκH, Units.val_mul]
    rfl
  have hsub : (⟨_, hκ'H⟩ : (lvP W).H) = ⟨_, hκH⟩ := Subtype.ext hκ'.2.2
  have e2 : levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) ((pk W).datYt t (j + 1) (lvP W)) κ' =
      (((lvP W).chi ⟨_, hκH⟩ : ℂˣ) : ℂ) *
        levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) (flagL ((pk W).datYt t (j + 1) (pk W).triv)) κ' := by
    unfold levChi
    erw [levFn_withP (L := (pk W).datYt t (j + 1) (pk W).triv) (lvP W), extendOne_of_mem _ hκ'H, Units.val_mul, hsub]
    rfl
  have hfd : ((pk W).νY t (j + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (j + 1))) ((pk W).fdY t (j + 1)) ((pk W).νY t (j + 1)) := by
    rcases Nat.lt_or_ge (j + 1 + 1) D.R.m with h | h
    · have := hC.models.νY t (j + 1) h
      exact ⟨this.1.1, this.2⟩
    · have e : j + 1 = D.R.m - 1 := by omega
      rw [e]
      have := hC.models.νY' t
      exact ⟨this.1.1, this.2⟩
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable (Yc D (j + 1))
  have htg : IsTopologicalGroup (GA D (Yc D (j + 1))) := by
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
    exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Yc D (j + 1)).gram))
  haveI := hfd.1
  haveI hR : ((pk W).νY t (j + 1)).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hfd.1
  have hmap : Measure.map (fun h => h * κ') ((pk W).νY t (j + 1)) = (pk W).νY t (j + 1) := map_mul_right_eq_self _ κ'
  have hFv := fun v => GlobalTheory.StepLevelP.IoLevPf.multT_val (pk W).θ ((pk W).MY (j + 1)) _ _ F.1 hF v
  have hpt' : (pk W).ωY t j (κ, κ') ((pk W).ptY t j φ) = (levChi (Yc D j) ((pk W).βY j) (flagL ((pk W).datYt t j (pk W).triv)) κ * (levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) (flagL ((pk W).datYt t (j + 1) (pk W).triv)) κ')⁻¹) • (pk W).ptY t j φ := hpt
  have hth := hker.2 κ κ' _ hpt'
  have hint := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ (Yc D (j + 1))) ((pk W).νY t (j + 1))
    ((pk W).fdY t (j + 1)) hfd.2 κ' hmap
    (fun h => thetaKO ((pk W).ωY t j) (g * κ) h ((pk W).ptY t j φ) * F.1 x h)
    (fun γ hγ h => by
      have h1 := hker.1 1 (GQ (Yc D j)).one_mem γ hγ (g * κ) h
      rw [one_mul] at h1
      simp only [h1, (hFv x).1 γ hγ h])
    (hio.integ F φ x (g * κ))
  have hpw : ∀ h, thetaKO ((pk W).ωY t j) (g * κ) (h * κ') ((pk W).ptY t j φ) * F.1 x (h * κ') =
      (levChi (Yc D j) ((pk W).βY j) (flagL ((pk W).datYt t j (pk W).triv)) κ * (levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) (flagL ((pk W).datYt t (j + 1) (pk W).triv)) κ')⁻¹ * levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) ((pk W).datYt t (j + 1) (lvP W)) κ') * (thetaKO ((pk W).ωY t j) g h ((pk W).ptY t j φ) * F.1 x h) := fun h => by
    rw [hth, (hFv x).2 κ' hκ'P]; ring
  rw [← hio.eq F φ x (g * κ), ← hio.eq F φ x g]
  unfold Lift.liftInt
  rw [← hint.2]
  simp only [hpw]
  rw [integral_const_mul, e1, e2]
  field_simp

end GlobalTheory.StepLevelP

end
