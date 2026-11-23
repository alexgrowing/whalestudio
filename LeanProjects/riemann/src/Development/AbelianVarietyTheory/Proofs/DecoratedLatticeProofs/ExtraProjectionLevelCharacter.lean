import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainProjectionLevelCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotLevGEmpty
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepLevelP

theorem eq_mul_of_inv_mul {a b c d : ℂ} (ha : a ≠ 0) (h : a⁻¹ * b = c * d) : b = a * c * d := by
  rw [mul_assoc, ← h, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

theorem mul_eq_of {a c d u v p q : ℂ} (h1 : u = a * p) (h2 : v = c * d * q) : u * v = a * (c * d) * (p * q) := by
  rw [h1, h2]; ring

theorem const_eq {a b c I : ℂ} (hb : b ≠ 0) : a * b⁻¹ * (b * c) * I = c * a * I := by
  field_simp

set_option maxHeartbeats 800000 in

theorem ioX_levChi_gen {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ)
    (hL : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T)
    (F : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (hF : F.1 ∈ CXP R P t) (κ : GA D (Yc D (D.R.m - 1)))
    (hκ : κ ∈ levS (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P)) (φ x g) :
    (R.ioX t F).1 (R.ItX φ x) (g * κ) =
      levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P) κ * (R.ioX t F).1 (R.ItX φ x) g := by
  have hθ : IsInfFam R.θ := hm.inf
  have hio := hc.ioX t
  have hκG : κ ∈ GfC (Yc D (D.R.m - 1)) := hκ.1
  have hκP : Lev.finE (Yc D (D.R.m - 1)) κ ∈ parLev D.sp.cm (Yc D (D.R.m - 1)).gram (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) := hκ.2.1
  have hκH : rTup (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) (Lev.finE (Yc D (D.R.m - 1)) κ) ∈ P.H := hκ.2.2
  have hκl : IsLevelLift (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv)
      (rTup (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) (Lev.finE (Yc D (D.R.m - 1)) κ)) κ := ⟨hκG, hκP, rfl⟩
  refine (GlobalTheory.Fam.FamInhab.lifts_top (R := R) hL t
    (rTup (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) (Lev.finE (Yc D (D.R.m - 1)) κ))).elim fun κ' hκ' => ?_
  have hlaw := GlobalTheory.StepLaw.last_step_law R hL hθ hc.ωX hc.vX t _ κ κ' hκl hκ'
  have hsS : levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ ≠ 0 := levChi_ne_zero _ _
  have hsT : levChi D.sp.X' R.βX (flagL (R.datXt t)) κ' ≠ 0 := levChi_ne_zero _ _
  have hlaw' : (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ)⁻¹ •
      R.ωX t (κ, κ') (R.vX t) =
      (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹ • R.vX t := hlaw
  have hv : R.ωX t (κ, κ') (R.vX t) =
      (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ *
        (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹) • R.vX t := by
    rw [mul_smul, ← hlaw', smul_smul, mul_inv_cancel₀ hsS, one_smul]
  have hpt := GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ _ _ _ _ (R.ωX t) hθ (hc.ωX t)
    _ _ _ _ (R.vX t) (hc.ptX t) κ hκG κ' hκ'.1 _ hv φ
  have hker := GlobalTheory.thetaKO_rat_left_and_eigen_right R.ψ _ _ _ _ (R.ωX t) (hc.ωX t)
    (R.ptX t φ) (hc.ptX t φ)
  have e1 : levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P) κ =
      ((P.chi ⟨_, hκH⟩ : ℂˣ) : ℂ) * levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ := by
    unfold levChi
    erw [levFn_withP (L := R.datYt t (D.R.m - 1) R.triv) P, extendOne_of_mem _ hκH, Units.val_mul]
    rfl
  have hfd : (R.νX t).IsHaarMeasure ∧ IsFundamentalDomain (GQ D.sp.X') (R.fdX t) (R.νX t) :=
    ⟨(hm.νX t).1.1, (hm.νX t).2⟩
  have hi := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable D.sp.X'
  haveI i1 := hi.1
  haveI i2 := hi.2.1
  haveI i3 := hi.2.2.1
  haveI i4 := hi.2.2.2
  have htg : IsTopologicalGroup (GA D D.sp.X') := by
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
    exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig D.sp.X'.gram))
  haveI := hfd.1
  haveI hR : (R.νX t).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hfd.1
  have hmap : Measure.map (fun h => h * κ') (R.νX t) = R.νX t := map_mul_right_eq_self _ κ'
  have hFv := (GlobalTheory.StepLevelP.IoLevPf.multT_val R.θ R.MX _ _ F.1 hF x).1
  have hF1 := ((GlobalTheory.Fam.FamInhab.cxp_iff P t F.1).1 hF).2 ⟨_, hκH⟩ κ' hκ' x
  have hF2 : ∀ h, F.1 x (h * κ') =
      levChi D.sp.X' R.βX (flagL (R.datXt t)) κ' * ((P.chi ⟨_, hκH⟩ : ℂˣ) : ℂ) * F.1 x h := fun h =>
    eq_mul_of_inv_mul hsT (hF1 h)
  have hpt' : R.ωX t (κ, κ') (R.ptX t φ) = (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ * (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹) • R.ptX t φ := hpt
  have hth := hker.2 κ κ' _ hpt'
  have hint := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ D.sp.X') (R.νX t)
    (R.fdX t) hfd.2 κ' hmap
    (fun h => thetaKO (R.ωX t) (g * κ) h (R.ptX t φ) * F.1 x h)
    (fun γ hγ h => by
      have h1 := hker.1 1 (GQ (Yc D (D.R.m - 1))).one_mem γ hγ (g * κ) h
      rw [one_mul] at h1
      simp only [h1, hFv γ hγ h])
    (hio.integ F φ x (g * κ))
  have hpw : ∀ h, thetaKO (R.ωX t) (g * κ) (h * κ') (R.ptX t φ) * F.1 x (h * κ') =
      (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ * (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹ * (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ' * ((P.chi ⟨_, hκH⟩ : ℂˣ) : ℂ))) * (thetaKO (R.ωX t) g h (R.ptX t φ) * F.1 x h) := fun h => by
    exact mul_eq_of (hth g h) (hF2 h)
  refine (hio.eq F φ x (g * κ)).symm.trans (hint.2.symm.trans ?_)
  refine (congrArg (fun f => ∫ h in R.fdX t, f h ∂(R.νX t)) (funext hpw)).trans ((integral_const_mul _ _).trans ?_)
  refine (const_eq hsT).trans ?_
  exact congrArg₂ (· * ·) e1.symm (hio.eq F φ x g)

theorem ioX_levChi : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ t (F : LinearMap.range ((pk W).cX.toMap (pk W).prX ∘ₗ ((pk W).HX t).e)), F.1 ∈ CXP (pk W) (lvP W) t → ∀ κ ∈ levS (Yc D (D.R.m - 1)) ((pk W).βY (D.R.m - 1)) ((pk W).datYt t (D.R.m - 1) (lvP W)), ∀ φ x g, ((pk W).ioX t F).1 ((pk W).ItX φ x) (g * κ) = levChi (Yc D (D.R.m - 1)) ((pk W).βY (D.R.m - 1)) ((pk W).datYt t (D.R.m - 1) (lvP W)) κ * ((pk W).ioX t F).1 ((pk W).ItX φ x) g :=
  fun W hW t F hF κ hκ φ x g => ioX_levChi_gen (pk W) (lvP W) hW.bot.hyp.2.2.2.1.lev hW.bot.hyp.2.2.2.1.models
    hW.bot.hyp.2.2.2.1.chain t F hF κ hκ φ x g

end GlobalTheory.StepLevelP

end
