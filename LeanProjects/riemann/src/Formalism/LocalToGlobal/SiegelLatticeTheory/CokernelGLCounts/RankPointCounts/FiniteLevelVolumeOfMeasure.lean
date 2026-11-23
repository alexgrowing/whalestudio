import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Chi2ApplyOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHCut
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement

noncomputable section

namespace Formalism.L2.SG.IntegralApproximation

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped Classical TensorProduct

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem finiteLevelVolume_of_measure (hM : X.MeasTie hb) : FiniteLevelVolumeEquality X hb := by
  unfold FiniteLevelVolumeEquality
  rw [hM.2.2.1]
  haveI : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  let e := (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).toHomeomorph.toMeasurableEquiv
  have he : (X.toFin hb : X.B.I.Gf → _) = e := rfl
  have hK : levelUnitary X hb = e '' X.K2 := rfl
  rw [hK, he, MeasurableEquiv.map_apply, Set.preimage_image_eq _ e.injective]

theorem mem_rr_iff (x : X.B.I.GA) :
    x ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ↔
      toHA X.B.I hb x ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J := by
  have hGF := Formalism.L2.SG.Closed.AdBridgeGF_holds X.B.I (toHA X.B.I hb) (toHA_isBridge X.B.I hb)
  have hrat : ∀ h : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J,
      h ∈ ratHA X.B.I ↔ h ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J := fun h => Iff.rfl
  rw [← hrat, ← hGF, Formalism.MainNotions.LeviCoordinates.rr_mem_GF]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← (toHA X.B.I hb).injective hyx]

theorem covolTie_of (hM : X.MeasTie hb) : CovolTie X := by
  haveI hBor : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : (X.B.I.muA X.B.μf).IsHaarMeasure := Formalism.L2.SG.PoincareInHH.Cut.muA_isHaar' X.B.I X.B.μf
  haveI : (X.B.I.muA X.B.μf).IsMulLeftInvariant := inferInstance
  have hfd0 : IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) X.B.fund (X.B.I.muA X.B.μf) :=
    Formalism.MainNotions.LeviCoordinates.rr_isFD ⟨X.B.fund_spec.1, X.B.fund_spec.2.1, X.B.fund_spec.2.2⟩
  let Γ : Subgroup (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J
  let e := (toHA X.B.I hb).toHomeomorph.toMeasurableEquiv
  let eΓ : Γ ≃ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I :=
    { toFun := fun g => ⟨(toHA X.B.I hb).symm (g : HA _ _ _), (mem_rr_iff X hb _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact g.2)⟩
      invFun := fun x => ⟨toHA X.B.I hb x, (mem_rr_iff X hb _).1 x.2⟩
      left_inv := fun g => Subtype.ext (ContinuousMulEquiv.apply_symm_apply _ _)
      right_inv := fun x => Subtype.ext (ContinuousMulEquiv.symm_apply_apply _ _) }
  haveI : Countable Γ := Function.Injective.countable eΓ.injective
  have hqmp : Measure.QuasiMeasurePreserving e.toEquiv.symm ((X.B.I.muA X.B.μf).map e) (X.B.I.muA X.B.μf) := by
    refine (MeasurePreserving.quasiMeasurePreserving ⟨e.symm.measurable, ?_⟩)
    exact e.map_symm_map
  have hfd : IsFundamentalDomain Γ (e '' X.B.fund) X.measG.μG := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ]
    refine hfd0.image_of_equiv e.toEquiv hqmp eΓ fun g x => ?_
    show e ((eΓ g : X.B.I.GA) * x) = (g : HA _ _ _) * e x
    show toHA X.B.I hb ((toHA X.B.I hb).symm g * x) = (g : HA _ _ _) * toHA X.B.I hb x
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have hmap : X.measG.μG (e '' X.B.fund) = X.B.I.muA X.B.μf X.B.fund := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ, MeasurableEquiv.map_apply, Set.preimage_image_eq _ e.injective]
  haveI : (X.measG.μG).IsHaarMeasure := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ]
    exact (toHA X.B.I hb).isHaarMeasure_map (X.B.I.muA X.B.μf)
  haveI : (X.measG.μG).IsMulLeftInvariant := inferInstance
  haveI : MeasurableConstSMul Γ (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    ⟨fun c => (continuous_mul_left (c : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).measurable⟩
  unfold CovolTie covolBy
  split_ifs with h
  · have h1 : IsFundamentalDomain Γ h.choose X.measG.μG := h.choose_spec
    rw [h1.measure_eq hfd, hmap]
    rfl
  · exact absurd ⟨_, hfd⟩ h

section MassData

open Formalism.L2.SG.MassDataConc Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

variable (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem MassDataDstarX_holds (L : LocIn (TypX X)) (A : AnIn) (hH : HypX X hb FdN FdN' u u')
    (hKpp : KppVolAt X hb hK FdN FdN' u u' X0 L A) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Dstar = Formalism.L2.SG.RowsConc.DstC X :=
  MassDataDstarX X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq L A hH hKpp (finiteLevelVolume_of_measure X hb hH.1)
    (covolTie_of X hb hH.1)

end MassData

end Formalism.L2.SG.IntegralApproximation
