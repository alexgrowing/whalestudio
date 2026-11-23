import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc

noncomputable section

namespace Formalism.L2.SG.IntegralApproximation

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped Classical TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Vol

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def FiniteLevelVolumeEquality : Prop := (X.measG.μGf (levelUnitary X hb)).toReal = (X.B.μf X.K2).toReal

def CovolTie : Prop :=
  covolBy (G := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) X.measG.μG =
    X.B.I.vol X.B.μf X.B.fund

theorem chi2_apply_one (hK : X.LevelSubgroupCharacter) : X.chi2 1 = 1 := by
  obtain ⟨h1, -, -, hmul, hnorm⟩ := hK
  have hm := hmul 1 h1 1 h1
  simp only [mul_one] at hm
  have hne : X.chi2 1 ≠ 0 := by
    intro h0
    have hn := hnorm 1 h1
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  exact mul_left_cancel₀ hne (hm.symm.trans (mul_one _).symm)

theorem e_one_re (hK : X.LevelSubgroupCharacter) : (X.B.e 1).re = ((X.B.μf X.K2).toReal)⁻¹ := by
  have h := X.e_eq 1
  have h1 : (1 : X.B.I.Gf) ∈ X.K2 := hK.1
  change X.B.e 1 = if (1 : X.B.I.Gf) ∈ X.K2 then star (X.chi2 1) / ((X.B.μf X.K2).toReal : ℂ) else 0 at h
  rw [if_pos h1, chi2_apply_one X hK, star_one] at h
  rw [h, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]

end Vol

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem MassDataDstarX (L : LocIn (TypX X)) (A : AnIn) (hH : HypX X hb FdN FdN' u u')
    (hKpp : KppVolAt X hb hK FdN FdN' u u' X0 L A) (h2 : FiniteLevelVolumeEquality X hb) (h3 : CovolTie X) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Dstar = Formalism.L2.SG.RowsConc.DstC X := by
  unfold Formalism.FourierDecayAlt.S3.MassData.Dstar Formalism.L2.SG.RowsConc.DstC Formalism.MainNotions.S.AutInst.Dstar
  rw [e_one_re X hK]
  have hdeg : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).deg =
      Formalism.MainNotions.PlaceDegreeData.fdegAll X.B.I X.B.σ X.B.w := rfl
  have hvol : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG =
      covolBy (G := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) X.measG.μG := rfl
  have hkpp : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKpp =
      (bOf X hb hK FdN FdN' u u' X0 L A).μKpp := rfl
  rw [hdeg, hvol, h3, hkpp, hKpp hH, h2]
  ring

theorem massDataDstarC_of (L : LocIn (TypX X)) (A : AnIn) (hH : HypX X hb FdN FdN' u u')
    (hKpp : KppVolAt X hb hK FdN FdN' u u' X0 L A) (h2 : FiniteLevelVolumeEquality X hb) (h3 : CovolTie X)
    (hT : D.what₂.Dstar = Formalism.L2.SG.RowsConc.DstC X) :
    MassDataDstarC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  unfold MassDataDstarC
  rw [hT]
  exact MassDataDstarX (hH := hH) (hKpp := hKpp) (h2 := h2) (h3 := h3) (ψ := ψ) (T := T) (sd := sd) (C := C)
    (Th := Th) (vR := vR) (Q := Q) (M := M) (δ := δ) (i0 := i0) (i0' := i0') (νq := νq)

end Formalism.L2.SG.IntegralApproximation
