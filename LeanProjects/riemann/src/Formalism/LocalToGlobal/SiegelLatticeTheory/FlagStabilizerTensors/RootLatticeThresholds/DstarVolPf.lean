import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ZsCovMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiniteLevelVolumeOfMeasure

noncomputable section

namespace Formalism.L2.SG.Pf.DstarVolPf

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.Theta
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def frOf : Formalism.IndefR.Eqv.UI.Frames D (VS D) where
  ε := fun _ => Formalism.L2.SG.InstExistsPf.epsV D
  P := fun v => (Formalism.L2.SG.InstExistsPf.exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose
  unit := fun v => (Formalism.L2.SG.InstExistsPf.exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose_spec.1
  spec := fun v => (Formalism.L2.SG.InstExistsPf.exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose_spec.2
  Λ := Formalism.L2.SG.InstExistsPf.Lv D
  Λ_fg := Formalism.L2.SG.InstExistsPf.L_fg D
  Λ_span := Formalism.L2.SG.InstExistsPf.L_span D
  Λ_dual := Formalism.L2.SG.InstExistsPf.L_dual D

theorem instOf_eq : Formalism.L2.SG.InstExistsPf.instOf D = Formalism.IndefR.Eqv.UI.instV (frOf D) := rfl

theorem lv_eq : (frOf D).Λ = Formalism.IndefR.Eqv.UI.Lv D (VS D) := rfl

abbrev IV : Formalism.MainNotions.S.AutInst := Formalism.IndefR.Eqv.UI.instV (frOf D)

def cdProdI : ENNReal := ∏ v : InfinitePlace D.host.F, (D.s.cdScale (VS D).rank ((frOf D).ε v) : ENNReal)

def muVI (μf : Measure (Formalism.IndefR.Eqv.UI.instV (frOf D)).Gf) [SigmaFinite μf] : Measure (GA D (VS D)) :=
  cdProdI D • ((Formalism.IndefR.Eqv.UI.instV (frOf D)).muA μf).map (Formalism.IndefR.Eqv.UI.brg (frOf D))

def VolMeasOf : Prop :=
  ∀ (μf : Measure (Formalism.IndefR.Eqv.UI.instV (frOf D)).Gf) [μf.IsHaarMeasure] [SigmaFinite μf],
    μf (Formalism.IndefR.Eqv.UI.instV (frOf D)).Kset = 1 →
    IsVolMeas D (VS D) (D.R.k + D.R.rS) (D.R.rS + 1) (muVI D μf)

theorem volMeasOf_of (hcd : cdScaleTie D) : VolMeasOf D := by
  intro μf _ _ hK
  have h1 : ∀ (v : InfinitePlace D.host.F) (i : Fin (D.R.k + D.R.rS)),
      (frOf D).ε v ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inl i)) = true := fun v i => by
    have := Formalism.L2.SG.InstExistsPf.eSgn_isLeft D ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inl i))
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have h2 : ∀ (v : InfinitePlace D.host.F) (j : Fin (D.R.rS + 1)),
      (frOf D).ε v ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inr j)) = false := fun v j => by
    have := Formalism.L2.SG.InstExistsPf.eSgn_isLeft D ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inr j))
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  exact Formalism.L2.S.S7.ZsCovMeas.isVolMeas_muV (frOf D) hcd (lv_eq D) (fun _ => (Formalism.L2.SG.InstExistsPf.eSgn D).symm)
    h1 h2 (fun v => (D.s.cdScale_pos _ _).ne') μf hK

theorem cdScale_cast {n m : ℕ} (h : n = m) (ε : Fin n → Bool) :
    D.s.cdScale n ε = D.s.cdScale m (fun i => ε (Fin.cast h.symm i)) := by
  subst h; rfl

theorem cdScale_epsV :
    D.s.cdScale (VS D).rank (Formalism.L2.SG.InstExistsPf.epsV D) = D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) := by
  rw [cdScale_cast D ((Formalism.L2.SG.InstExistsPf.rank_eq D).trans (dimS_eq D.R).symm)]
  rfl

section Gen

variable {I : Formalism.MainNotions.S.AutInst} (hb : AdBridgeIso I)

theorem mem_rr_iff' (x : I.GA) :
    x ∈ Formalism.MainNotions.LeviCoordinates.rr_GF I ↔ toHA I hb x ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := by
  have hGF := Formalism.L2.SG.Closed.AdBridgeGF_holds I (toHA I hb) (toHA_isBridge I hb)
  have hrat : ∀ h : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J,
      h ∈ ratHA I ↔ h ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := fun h => Iff.rfl
  rw [← hrat, ← hGF, Formalism.MainNotions.LeviCoordinates.rr_mem_GF]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← (toHA I hb).injective hyx]

theorem isFD_image (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA)
    (hf : I.IsFundDom (I.muA μf) fund) (ν : Measure (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J))
    (hν : ν ≪ (I.muA μf).map (toHA I hb)) :
    IsFundamentalDomain (HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J) (toHA I hb '' fund) ν := by
  haveI hBor : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J) := ⟨rfl⟩
  haveI : (I.muA μf).IsHaarMeasure := Formalism.L2.SG.PoincareInHH.Cut.muA_isHaar' I μf
  haveI : (I.muA μf).IsMulLeftInvariant := inferInstance
  have hfd0 : IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF I) fund (I.muA μf) :=
    Formalism.MainNotions.LeviCoordinates.rr_isFD ⟨hf.1, hf.2.1, hf.2.2⟩
  let Γ : Subgroup (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J) := HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J
  let e := (toHA I hb).toHomeomorph.toMeasurableEquiv
  let eΓ : Γ ≃ Formalism.MainNotions.LeviCoordinates.rr_GF I :=
    { toFun := fun g => ⟨(toHA I hb).symm (g : HA _ _ _), (mem_rr_iff' hb _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact g.2)⟩
      invFun := fun x => ⟨toHA I hb x, (mem_rr_iff' hb _).1 x.2⟩
      left_inv := fun g => Subtype.ext (ContinuousMulEquiv.apply_symm_apply _ _)
      right_inv := fun x => Subtype.ext (ContinuousMulEquiv.symm_apply_apply _ _) }
  have hqmp : Measure.QuasiMeasurePreserving e.toEquiv.symm ((I.muA μf).map e) (I.muA μf) := by
    refine (MeasurePreserving.quasiMeasurePreserving ⟨e.symm.measurable, ?_⟩)
    exact e.map_symm_map
  have hfd : IsFundamentalDomain Γ (e '' fund) ((I.muA μf).map e) := by
    refine hfd0.image_of_equiv e.toEquiv hqmp eΓ fun g x => ?_
    show e ((eΓ g : I.GA) * x) = (g : HA _ _ _) * e x
    show toHA I hb ((toHA I hb).symm g * x) = (g : HA _ _ _) * toHA I hb x
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  exact hfd.mono hν

end Gen

theorem covol_gen (hVM : VolMeasOf D) (hVol : VolTie D) (I : Formalism.MainNotions.S.AutInst)
    (hI : I = Formalism.IndefR.Eqv.UI.instV (frOf D)) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (hf : I.IsFundDom (I.muA μf) fund) :
    I.vol μf fund / (μf I.Kset).toReal *
      ∏ _v : InfinitePlace I.F, (D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) : ℝ) = volY0 D := by
  subst hI
  have hKc : IsCompact (IV D).Kset := Formalism.L2.SG.Closed.AutKCompact_holds (IV D)
  have hKo : IsOpen (IV D).Kset := by
    have h := (IV D).topf_open 1 le_rfl
    convert h using 1
    ext x
    constructor
    · intro hx
      exact ⟨hx, fun y hy => ⟨_, Formalism.L2.SG.Pf.unitaryCongruence.K_sub_mv _ hx hy, by simp⟩⟩
    · intro hx
      exact hx.1
  have hpos : 0 < μf (IV D).Kset := hKo.measure_pos μf ⟨1, Formalism.L2.SG.Pf.unitaryCongruence.K_one _⟩
  have hfin : μf (IV D).Kset < ⊤ := hKc.measure_lt_top
  set c := μf (IV D).Kset with hc
  let μ' : Measure (IV D).Gf := c⁻¹ • μf
  haveI : μ'.IsHaarMeasure := Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hpos.ne')
  have hfs : ∀ n, μ' (spanningSets μf n) < ⊤ := fun n => by
    show (c⁻¹ • μf) _ < ⊤
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 hpos) (measure_spanningSets_lt_top μf n)
  haveI : SigmaFinite μ' :=
    ⟨⟨{ set := spanningSets μf, set_mem := fun _ => Set.mem_univ _, finite := hfs, spanning := iUnion_spanningSets μf }⟩⟩
  have hK1 : μ' (IV D).Kset = 1 := by
    show (c⁻¹ • μf) (IV D).Kset = 1
    rw [Measure.smul_apply, smul_eq_mul, ← hc, ENNReal.inv_mul_cancel hpos.ne' hfin.ne]
  have hV := hVM μ' hK1
  have hsig : (VS D).SigOK := D.sp.Y_sig 0
  have hsv : ∀ τ, (VS D).sig τ = (D.R.k + D.R.rS, D.R.rS + 1) := fun τ => D.sp.baseSpace_signature_eq τ
  obtain ⟨-, hall⟩ := hVol (VS D) _ _ hsig hsv
  obtain ⟨-, hfd⟩ := hall _ hV
  let hb : AdBridgeIso (IV D) := (Formalism.L2.SG.Closed.adelic_isomorphism_statement (IV D)).1
  have hbrg : Formalism.IndefR.Eqv.UI.brg (frOf D) = toHA (IV D) hb := rfl
  have hμA : (IV D).muA μ' = c⁻¹ • (IV D).muA μf := by
    show (Measure.pi fun v => Formalism.REAL.muG ((IV D).ε v)).prod (c⁻¹ • μf) = c⁻¹ • (Measure.pi fun v => Formalism.REAL.muG ((IV D).ε v)).prod μf
    exact Measure.prod_smul_right _
  have hν : muVI D μ' ≪ ((IV D).muA μf).map (toHA (IV D) hb) := by
    unfold muVI
    rw [hbrg, hμA, Measure.map_smul]
    exact (Measure.smul_absolutelyContinuous).trans Measure.smul_absolutelyContinuous
  have hFD := isFD_image hb μf fund hf (muVI D μ') hν
  have key : muVI D μ' (toHA (IV D) hb '' fund) = ENNReal.ofReal (D.vol (VS D)) := hfd _ hFD
  haveI : BorelSpace (HAd (IV D)) := ⟨rfl⟩
  let e := (toHA (IV D) hb).toHomeomorph.toMeasurableEquiv
  have hmeas : Measurable (toHA (IV D) hb) := (toHA (IV D) hb).continuous.measurable
  have hS : MeasurableSet (toHA (IV D) hb '' fund) := (e.measurableSet_image).2 hf.1
  have hmap : muVI D μ' (toHA (IV D) hb '' fund) = cdProdI D * (c⁻¹ * (IV D).muA μf fund) := by
    unfold muVI
    rw [Measure.smul_apply, smul_eq_mul, hbrg, hμA]
    congr 1
    erw [Measure.map_apply hmeas hS]
    rw [Set.preimage_image_eq _ (toHA (IV D) hb).injective, Measure.smul_apply, smul_eq_mul]
  have hA0 : (IV D).muA μf fund ≠ 0 := by
    haveI : ((IV D).muA μf).IsHaarMeasure := Formalism.L2.SG.PoincareInHH.Cut.muA_isHaar' (IV D) μf
    have hfd0 : IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF (IV D)) fund ((IV D).muA μf) :=
      Formalism.MainNotions.LeviCoordinates.rr_isFD ⟨hf.1, hf.2.1, hf.2.2⟩
    exact hfd0.measure_ne_zero (NeZero.ne _)
  have hcd0 : cdProdI D ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => by simpa using (D.s.cdScale_pos _ _).ne'
  have hci0 : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hfin.ne
  replace key := hmap.symm.trans key
  have hAT : (IV D).muA μf fund ≠ ⊤ := by
    intro hT
    rw [hT, ENNReal.mul_top hci0, ENNReal.mul_top hcd0] at key
    exact ENNReal.ofReal_ne_top key.symm
  have hL0 : cdProdI D * (c⁻¹ * (IV D).muA μf fund) ≠ 0 := mul_ne_zero hcd0 (mul_ne_zero hci0 hA0)
  have hvpos : 0 < D.vol (VS D) := by
    by_contra hle
    push_neg at hle
    rw [ENNReal.ofReal_of_nonpos hle] at key
    exact hL0 key
  have hR := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_ofReal hvpos.le, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv] at hR
  have hcdR : (cdProdI D).toReal = ∏ _v : InfinitePlace D.host.F, (D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) : ℝ) := by
    unfold cdProdI
    rw [ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    show ((D.s.cdScale (VS D).rank (Formalism.L2.SG.InstExistsPf.epsV D) : ENNReal)).toReal = _
    rw [cdScale_epsV]
    rfl
  rw [hcdR] at hR
  show ((IV D).muA μf fund).toReal / c.toReal *
      ∏ _v : InfinitePlace D.host.F, (D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) : ℝ) = D.vol (VS D)
  rw [← hR]
  ring

section Record

variable {D}

theorem dstarVolV_of (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hVol : VolTie D)
    (hcd : cdScaleTie D) : Formalism.L2.SG.Pf.RowDictPf.DstarVolV X :=
  covol_gen D (volMeasOf_of D hcd) hVol X.B.I (h.trans (instOf_eq D)) X.B.μf X.B.fund X.B.fund_spec

theorem dstarVol_holds (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hVol : VolTie D)
    (hcd : cdScaleTie D) (hT : dsigTie D) : Formalism.L2.SG.Pf.RowDictPf.DstarVol X :=
  Formalism.L2.SG.Pf.RowDictPf.dstarVol_of X hT (dstarVolV_of X h hVol hcd)

end Record

end Formalism.L2.SG.Pf.DstarVolPf
