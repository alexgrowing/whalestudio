import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.SupportG
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal

noncomputable section

namespace Formalism.L2.SG.MassDataConc

open Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures MeasureTheory
open scoped Classical

section Terms

variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁)

def SigOf : ℝ :=
  ∑' p : τ × τ, (T.sc T.genSet).indicator (fun p => (inner ℂ (T.vec p.1) (T.vec p.2)).re) p

def gsPairs : Set (τ × τ) := {p | p.1 ∈ T.genSet ∧ p.2 ∈ T.genSet ∧ T.s0 p.1 p.2 = 1 ∧ T.scal p.1 p.2}

def CokernelCountConstant : ℝ := ∑' p : τ × τ, (gsPairs T).indicator (fun p => (inner ℂ (T.op p.1) (T.op p.2)).re) p

theorem pairSum_eq {g : ℝ} (hG : T.Gam1 = g) : T.pairSum (T.sc T.genSet) = g * SigOf T := by
  subst hG
  rfl

end Terms

structure AnRest where
  KV : ℝ
  KtopV : ℝ

def anOf {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (coo deg intN intC intOO sd C Th : ℝ)
    (r f : ℕ) (R : AnRest) : AnIn where
  Coo := coo
  deg := deg
  IntN := intN
  IntC := intC
  IntOO := intOO
  Sig := SigOf T
  KV := R.KV
  KtopV := R.KtopV
  Kgs2 := CokernelCountConstant T
  supdens := sd
  e1 := max sd 1
  δ := C * ((r : ℝ) + 1) * (C / Th) ^ f

section Kappa

open Formalism.BasicNotions

def kapN (D : D7) : ℝ :=
  D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) * D.R.f) *
    ((Formalism.MainNotions.S.Lat.gS D : ℝ) ^ (2 * D.R.f * D.R.rS * (D.R.rS + 1)))⁻¹

end Kappa

section OfSetting

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

variable (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X))
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ) (R : AnRest)

def normalizedFourierDecayDatum : Formalism.FourierDecayAlt.S3.MassData (TypX X) :=
  bOf X hb hK FdN FdN' u u' X0 L
    (anOf T (kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1) (Formalism.L2.SG.RealObj.degX X)
      (L.volZZ / ((L.localVolumeArchimedean * ∏ p, L.localVolumeAtPlace p) * L.volPP) * (L.volPP * (Formalism.L2.SG.RealObj.IntC X u u' 1 / kapN D)))
      (Formalism.L2.SG.RealObj.IntC X u u' 1 / kapN D) (Formalism.L2.SG.RealObj.IntOO X u u' 1) sd C Th D.R.rS
      (Fintype.card (NumberField.InfinitePlace X.B.I.F)) R)

def bC : Formalism.FourierDecayAlt.S3.MassData (TypX X) :=
  let B1 : Formalism.FourierDecayAlt.S3.MassData (TypX X) :=
    { normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R with
      Mo := (normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R).localVolumeArchimedean * (normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R).μKo ^ 2 /
        ((normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R).μSo * (normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R).μSo') }
  { B1 with n0c := B1.AA / B1.ρ0, KV := B1.Sig / B1.ρ0 }

theorem inOrdinary_bC (h : L.localVolumeArchimedean ≠ 0) : (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).InOrdinary := by
  have h' : (normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R).localVolumeArchimedean ≠ 0 := h
  unfold Formalism.FourierDecayAlt.S3.MassData.InOrdinary
  change (normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R).localVolumeArchimedean * (normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R).μKo ^ 2 /
      ((normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R).μSo * (normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R).μSo') / (normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R).localVolumeArchimedean =
    (normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R).μKo ^ 2 / ((normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R).μSo * (normalizedFourierDecayDatum X hb hK FdN FdN' u u' X0 L T sd C Th R).μSo')
  rw [mul_div_assoc, mul_div_cancel_left₀ _ h']

theorem inForm_bC (h : (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).ρ0 ≠ 0) :
    (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).InForm := by
  unfold Formalism.FourierDecayAlt.S3.MassData.InForm
  change (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).Sig = (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).ρ0 * ((bC X hb hK FdN FdN' u u' X0 L T sd C Th R).Sig / (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).ρ0)
  rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self h, mul_one]

theorem inMass_bC (h : (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).ρ0 ≠ 0) :
    (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).InMass := by
  unfold Formalism.FourierDecayAlt.S3.MassData.InMass
  change (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).AA / (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).ρ0 * (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).ρ0 = (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).AA
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self h, mul_one]

theorem link_sig (h : T.Gam1 = (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).Gam1) :
    T.pairSum (T.sc T.genSet) =
      (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).Gam1 * (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).Sig := pairSum_eq T h

theorem energy_defs :
    (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).e1 = max sd 1 ∧
      (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).δ =
        C * ((D.R.rS : ℝ) + 1) * (C / Th) ^ (Fintype.card (NumberField.InfinitePlace X.B.I.F)) := ⟨rfl, rfl⟩

theorem inJacMod_bC : (bC X hb hK FdN FdN' u u' X0 L T sd C Th R).InJacMod := rfl

theorem scaled_volume_level_subgroup (hV : 0 < X.volK2) (A : AnIn) :
    (Real.sqrt (c0X X u FdN * c0X X u' FdN'))⁻¹ * X.volK2 =
      (Real.sqrt ((bOf X hb hK FdN FdN' u u' X0 L A).c0 * (bOf X hb hK FdN FdN' u u' X0 L A).c0'))⁻¹ := by
  have h1 : c0X X u FdN = X.volK2 * (bOf X hb hK FdN FdN' u u' X0 L A).c0 := by
    change X.volK2 * (X.muN u FdN).toReal * (X.muH u Set.univ).toReal / (Module.finrank ℂ (X.Vpi u) : ℝ) =
      X.volK2 * ((X.muN u FdN).toReal * (X.muH u Set.univ).toReal / (Module.finrank ℂ (X.Vpi u) : ℝ))
    ring
  have h2 : c0X X u' FdN' = X.volK2 * (bOf X hb hK FdN FdN' u u' X0 L A).c0' := by
    change X.volK2 * (X.muN u' FdN').toReal * (X.muH u' Set.univ).toReal / (Module.finrank ℂ (X.Vpi u') : ℝ) =
      X.volK2 * ((X.muN u' FdN').toReal * (X.muH u' Set.univ).toReal / (Module.finrank ℂ (X.Vpi u') : ℝ))
    ring
  rw [h1, h2]
  generalize (bOf X hb hK FdN FdN' u u' X0 L A).c0 = a
  generalize (bOf X hb hK FdN FdN' u u' X0 L A).c0' = b
  rw [show X.volK2 * a * (X.volK2 * b) = X.volK2 ^ 2 * (a * b) by ring, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq hV.le, mul_inv, mul_right_comm, inv_mul_cancel₀ hV.ne', one_mul]

def LevelOneLatticeAgreementAt (TR : TypedRed X) (A : AnIn) : Prop :=
  (Gam1 TR : ℝ) = (bOf X hb hK FdN FdN' u u' X0 L A).Gam1

end OfSetting

section Compat

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Volumes Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

variable {D : D7} (X : HidaSetting D)

def MeasCompatψ (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Prop :=
  (∀ u, (∃ (hT1 : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u)) j i) =
          gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u)) i j) (νH : Measure _),
        IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hT1 νH ∧
        IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (tupH (frameOf X u)) X.measG.μG (X.measW u).μH νH) ∧
      covol (X.measW u).μN = 1) ∧
    ∀ X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E, (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0 →
      ∃ (hTB : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J X0 j i) = gramE X.B.I.cm.sig X.B.I.J X0 i j)
        (νB : Measure _),
        IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hTB νB ∧
        IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J X0 X.measG.μG (X.measG.μB X0) νB

def MeasCompat : Prop :=
  ∃ ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ, IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧ MeasCompatψ X ψ

theorem inVolumes_of_compat (hb : AdBridge.AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn)
    (hV : InVolumesAt X hb hK FdN FdN' u u' X0 L A) (hH : HypX X hb FdN FdN' u u') (hC : MeasCompat X)
    (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0) :
    (bOf X hb hK FdN FdN' u u' X0 L A).InVolumes := by
  unfold MeasCompat at hC
  obtain ⟨ψ, hψ, -, hM⟩ := hC
  unfold MeasCompatψ at hM
  obtain ⟨hu, hB⟩ := hM
  obtain ⟨⟨hT1, νH, hO, hCm⟩, hN⟩ := hu u
  obtain ⟨⟨hT1', νH', hO', hCm'⟩, hN'⟩ := hu u'
  obtain ⟨hTB, νB, hOB, hCB⟩ := hB X0 hdet
  exact hV hH ψ hψ hT1 νH hO hCm hT1' νH' hO' hCm' hTB νB hdet hOB hCB hN hN'

end Compat

section Loc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ) (R : AnRest)

def bCL : Formalism.FourierDecayAlt.S3.MassData (TypX X) :=
  bC X hb hK FdN FdN' u u' X0 (Formalism.L2.SG.LocVol.locOf X u u' ψ) T sd C Th R

end Loc

section Nc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ngFac (D : D7) : ℝ :=
  (Real.sqrt (abs ((Algebra.norm ℚ (((Formalism.MainNotions.S.Lat.gS D : ℕ) : D.host.E) ^ D.R.m) : ℚ) : ℝ))) ^ (D.R.k - 1)

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn)

end Nc

section Kernel

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)

def VConstants (sc : ℝ) (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (w : Point D.host.E (D.R.rS + 1)) :
    Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) :=
  Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.VPt X u u' sc i0 i0' FdN FdN' νq w)

def KVOf {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (V : Point D.host.E (D.R.rS + 1) → Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u)) : ℝ :=
  ∑' q : Point D.host.E (D.R.rS + 1) × Point D.host.E (D.R.rS + 1),
    (Formalism.L2.SG.PairVal.KgsOf vR Q q.1 q.2 * inner ℂ (V q.2) (V q.1)).re

def KtopVOf (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (V : Point D.host.E (D.R.rS + 1) → Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u)) : ℝ :=
  ∑' q : Point D.host.E (D.R.rS + 1) × Point D.host.E (D.R.rS + 1),
    ((((Formalism.L2.SG.SupportG.normG ((D.mem u).A.T) ((D.mem u').A.T) q.1 *
        Formalism.L2.SG.SupportG.normG ((D.mem u).A.T) ((D.mem u').A.T) q.2 : ℚ) : ℝ) ^ (((D.R.k : ℝ) - 1) / 4) : ℝ) *
      Formalism.MainNotions.S.LocalSplitGroups.KtopG M δ ((D.mem u).A.T) ((D.mem u').A.T) q.1 q.2 * inner ℂ (V q.2) (V q.1)).re

end Kernel

section Full

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

def bCF : Formalism.FourierDecayAlt.S3.MassData (TypX X) :=
  bCL X hb hK FdN FdN' u u' X0 ψ T sd C Th
    ⟨KVOf X u u' vR Q (VConstants X u u' 1 i0 i0' FdN FdN' νq), KtopVOf X u u' M δ (VConstants X u u' 1 i0 i0' FdN FdN' νq)⟩

end Full

section Closed

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

def InFormC : Prop :=
  (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InForm

theorem inFormC_bCF (h : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).ρ0 ≠ 0) :
    InFormC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := inForm_bC X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) T sd C Th
    ⟨KVOf X u u' vR Q (VConstants X u u' 1 i0 i0' FdN FdN' νq), KtopVOf X u u' M δ (VConstants X u u' 1 i0 i0' FdN FdN' νq)⟩ h

def InTypedC : Prop :=
  HypX X hb FdN FdN' u u' → ProdConv X u u' ψ → LocTieX X ψ u → LocTieX X ψ u' → TypFacts X u u' →
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped

theorem inOrdinary_bCF (hP : ProdConv X u u' ψ) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary := by
  unfold ProdConv at hP
  exact inOrdinary_bC X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) T sd C Th
    ⟨KVOf X u u' vR Q (VConstants X u u' 1 i0 i0' FdN FdN' νq), KtopVOf X u u' M δ (VConstants X u u' 1 i0 i0' FdN FdN' νq)⟩ hP.2.2.2.2.1.ne'

theorem inTypedC_of
    (h : InTypedAt X hb hK FdN FdN' u u' X0
      (anOf T (kapN D * Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1) (Formalism.L2.SG.RealObj.degX X)
        ((locOf X u u' ψ).volZZ / (((locOf X u u' ψ).localVolumeArchimedean * ∏ p, (locOf X u u' ψ).localVolumeAtPlace p) * (locOf X u u' ψ).volPP) *
          ((locOf X u u' ψ).volPP * (Formalism.L2.SG.RealObj.IntC X u u' 1 / kapN D)))
        (Formalism.L2.SG.RealObj.IntC X u u' 1 / kapN D) (Formalism.L2.SG.RealObj.IntOO X u u' 1) sd C Th D.R.rS
        (Fintype.card (NumberField.InfinitePlace X.B.I.F))
        ⟨KVOf X u u' vR Q (VConstants X u u' 1 i0 i0' FdN FdN' νq), KtopVOf X u u' M δ (VConstants X u u' 1 i0 i0' FdN FdN' νq)⟩) ψ) :
    InTypedC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := h

theorem inJacMod_bCF : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InJacMod := rfl

def LevelOneLatticeAgreement : Prop := T.Gam1 = (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Gam1

def ttC : Prop :=
  (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).tt =
    ∏ p : TypX X, (1 + 3 / ((Ideal.absNorm p.1.asIdeal : ℕ) : ℝ))

theorem ttC_of_split (h : GSplitX X) : ttC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  unfold ttC Formalism.FourierDecayAlt.S3.MassData.tt
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [(h p).1]
  rfl

def MassDataDstarC : Prop :=
  (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Dstar = D.what₂.Dstar

def EnergyLinkC (jn : ℝ) : Prop := (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).IntN = jn

theorem energyLink_bCF (jn : ℝ) (h : EnergyLinkC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq jn) :
    Formalism.FourierDecayAlt.PB.EnergyLink (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq) jn sd C Th D.R.rS
      (Fintype.card (NumberField.InfinitePlace X.B.I.F)) := by
  unfold Formalism.FourierDecayAlt.PB.EnergyLink
  exact ⟨h, energy_defs X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) T sd C Th
    ⟨KVOf X u u' vR Q (VConstants X u u' 1 i0 i0' FdN FdN' νq), KtopVOf X u u' M δ (VConstants X u u' 1 i0 i0' FdN FdN' νq)⟩⟩

def NcTieC (c : ℝ) : Prop :=
  c = (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).n0c * ngFac D /
    ((bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al * kapN D)

def RhoTieC : Prop :=
  (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).ρ0 = Formalism.MainNotions.S.Cnt.massRows D F0 what₂

end Closed

end Formalism.L2.SG.MassDataConc
