import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainProjectionLevelCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StepLevelP.IoLevPf
end GlobalTheory.StepLevelP.IoLevPf
namespace GlobalTheory.StepLevelP
set_option maxHeartbeats 800000 in
theorem io_levChi_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t j, j + 1 < D.R.m → ∀ F : (_root_.GlobalTheory.Fam.pk_z W).CC t (j + 1), F.1 ∈ CP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1) → ∀ κ ∈ levS (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)), ∀ φ x g, ((_root_.GlobalTheory.Fam.pk_z W).ioY t j F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j φ x) (g * κ) = levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ * ((_root_.GlobalTheory.Fam.pk_z W).ioY t j F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j φ x) g := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj F hF κ hκ φ x g
  have hC := hW.bot.hyp.2.2.2.1
  have hL : (_root_.GlobalTheory.Fam.pk_z W).Is W.P.A3.A.μ0 := hC.lev
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hC.models.inf
  have hio := hC.chain.ioY t j (by omega)
  have hκG : κ ∈ GfC (Yc D j) := hκ.1
  have hκP : Lev.finE (Yc D j) κ ∈ parLev D.sp.cm (Yc D j).gram ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) := hκ.2.1
  have hκH : rTup ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) (Lev.finE (Yc D j) κ) ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := hκ.2.2
  have hκl : IsLevelLift (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)
      (rTup ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) (Lev.finE (Yc D j) κ)) κ := ⟨hκG, hκP, rfl⟩
  obtain ⟨κ', hκ'⟩ := GlobalTheory.ChainLiftEquiv.liftsExist_chain (_root_.GlobalTheory.Fam.pk_z W) hL t (j + 1) hj
    (rTup ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) (Lev.finE (Yc D j) κ))
  have hj' : j < D.R.m := by omega
  have hlaw := GlobalTheory.StepLaw.step_law (_root_.GlobalTheory.Fam.pk_z W).toLevCh hL t j (j + 1) rfl hj' hθ (D.sp.Y_sig _) (D.sp.Y_sig _) (r_le_Y _) (r_le_Y _)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj'.le]; rfl)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj.le]; rfl)
    (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (hL.βY j hj') (hL.βY (j + 1) hj)
    (hC.chain.ωY t j hj) (hC.chain.vY t j hj) _ κ κ' hκl hκ'
  have hsS : levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ ≠ 0 := levChi_ne_zero _ _
  have hsT : levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ' ≠ 0 :=
    levChi_ne_zero _ _
  have hlaw' : (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ)⁻¹ •
      (_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ, κ') ((_root_.GlobalTheory.Fam.pk_z W).vY t j) =
      (levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ')⁻¹ • (_root_.GlobalTheory.Fam.pk_z W).vY t j := hlaw
  have hv : (_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ, κ') ((_root_.GlobalTheory.Fam.pk_z W).vY t j) =
      (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ *
        (levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ')⁻¹) •
        (_root_.GlobalTheory.Fam.pk_z W).vY t j := by
    rw [mul_smul, ← hlaw', smul_smul, mul_inv_cancel₀ hsS, one_smul]
  have hpt := GlobalTheory.FiniteFock.om_pureTensorO_of_finite (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) hθ (hC.chain.ωY t j hj)
    _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).vY t j) (hC.chain.ptY t j hj) κ hκG κ' hκ'.1 _ hv φ
  have hker := GlobalTheory.thetaKO_rat_left_and_eigen_right (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (hC.chain.ωY t j hj)
    ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) (hC.chain.ptY t j hj φ)
  have hκ'H : rTup ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv) (Lev.finE (Yc D (j + 1)) κ') ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := by
    rw [hκ'.2.2]; exact hκH
  have hκ'P : κ' ∈ levS (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) := ⟨hκ'.1, hκ'.2.1, hκ'H⟩
  have e1 : levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ =
      (((_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨_, hκH⟩ : ℂˣ) : ℂ) * levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ := by
    unfold levChi
    erw [levFn_withP (L := (_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv) (_root_.GlobalTheory.Fam.complexLevelStructure W), extendOne_of_mem _ hκH, Units.val_mul]
    rfl
  have hsub : (⟨_, hκ'H⟩ : (_root_.GlobalTheory.Fam.complexLevelStructure W).H) = ⟨_, hκH⟩ := Subtype.ext hκ'.2.2
  have e2 : levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ' =
      (((_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨_, hκH⟩ : ℂˣ) : ℂ) *
        levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ' := by
    unfold levChi
    erw [levFn_withP (L := (_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv) (_root_.GlobalTheory.Fam.complexLevelStructure W), extendOne_of_mem _ hκ'H, Units.val_mul, hsub]
    rfl
  have hfd : ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) := by
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
  haveI hR : ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hfd.1
  have hmap : Measure.map (fun h => h * κ') ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) = (_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1) := map_mul_right_eq_self _ κ'
  have hFv := fun v => GlobalTheory.StepLevelP.IoLevPf.multT_val (_root_.GlobalTheory.Fam.pk_z W).θ ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) _ _ F.1 hF v
  have hpt' : (_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ, κ') ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) = (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ * (levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ')⁻¹) • (_root_.GlobalTheory.Fam.pk_z W).ptY t j φ := hpt
  have hth := hker.2 κ κ' _ hpt'
  have hint := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ (Yc D (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1))
    ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) hfd.2 κ' hmap
    (fun h => thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (g * κ) h ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) * F.1 x h)
    (fun γ hγ h => by
      have h1 := hker.1 1 (GQ (Yc D j)).one_mem γ hγ (g * κ) h
      rw [one_mul] at h1
      simp only [h1, (hFv x).1 γ hγ h])
    (hio.integ F φ x (g * κ))
  have hpw : ∀ h, thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (g * κ) (h * κ') ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) * F.1 x (h * κ') =
      (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.pk_z W).triv)) κ * (levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (flagL ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.pk_z W).triv)) κ')⁻¹ * levChi (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ') * (thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) g h ((_root_.GlobalTheory.Fam.pk_z W).ptY t j φ) * F.1 x h) := fun h => by
    rw [hth, (hFv x).2 κ' hκ'P]; ring
  rw [← hio.eq F φ x (g * κ), ← hio.eq F φ x g]
  unfold Lift.liftInt
  rw [← hint.2]
  simp only [hpw]
  rw [integral_const_mul, e1, e2]
  field_simp
end GlobalTheory.StepLevelP
end
end
