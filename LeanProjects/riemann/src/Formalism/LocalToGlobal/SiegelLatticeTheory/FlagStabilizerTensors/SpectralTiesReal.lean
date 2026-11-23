import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremS
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataForm
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DegreeRatioFormulaStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups ValuativeRel

namespace Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section KV

variable {E : Type} [Field E] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def KVIdentity {P : Type} [Fintype P] (B : S3.MassData P) (c : ℕ → TB.Pt E → ℂ) (Vt : TB.Pt E → H) : Prop :=
  Summable (fun ρ : ℕ => ‖∑' p, c ρ p • Vt p‖ ^ 2) ∧
    B.c0 * B.c0' * B.KV = B.n0c * ∑' ρ : ℕ, ‖∑' p, c ρ p • Vt p‖ ^ 2

theorem kv_identity_bound {P : Type} [Fintype P] {B : S3.MassData P} {c : ℕ → TB.Pt E → ℂ} {Vt : TB.Pt E → H}
    (hI : KVIdentity B c Vt) (hn : 0 ≤ B.n0c) :
    ∀ Mb : ℝ, (∀ R : Finset ℕ, ∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2 ≤ Mb) → B.c0 * B.c0' * B.KV ≤ B.n0c * Mb := by
  intro Mb hMb
  rw [hI.2]
  refine mul_le_mul_of_nonneg_left ?_ hn
  first
  | exact hI.1.tsum_le_of_sum_le hMb
  | exact tsum_le_of_sum_le hI.1 hMb
  | exact tsum_le_of_sum_le' (le_trans (by positivity) (hMb ∅)) hMb

end KV

section Carrier

open Formalism.L2.SG.AdBridge

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

abbrev massDataY : S3.MassData (Formalism.L2.SG.TypedSets.TypX X) :=
  Formalism.L2.SG.MassDataConc.bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq

def CarrierFull (C₄ CA : ℝ) (G0 : Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ) (l : ℕ) : Prop :=
  ∃ (Wp Wq : InfinitePlace D.host.E → Type) (_ : ∀ x, NormedAddCommGroup (Wp x)) (_ : ∀ x, InnerProductSpace ℂ (Wp x))
    (_ : ∀ x, NormedAddCommGroup (Wq x)) (_ : ∀ x, InnerProductSpace ℂ (Wq x)) (_ : ∀ x, FiniteDimensional ℂ (Wq x))
    (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (Qm : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ)
    (Qim : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v),
    S.CA = CA ∧ S.G = G0 ∧ S.de = de ∧ S.de' = de' ∧ S.l = l ∧
    Formalism.L2.SG.DataInst.Compat S u u' ∧ Formalism.L2.SG.RealObj.BaseFromX X S u u' i0 i0' τ Qm Qim ν' m₀ ∧
    Formalism.L2.SG.RealObj.TopTie X S u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq τ ∧
    Formalism.L2.SG.RealObj.VJoint X S u u' 1 i0 i0' νq T f ν' m₀ τ eP eQ ∧
    Formalism.FourierDecayAlt.PB.RealInputs (Formalism.L2.SG.DataInst.dOf S Y.δ Y.M u u') C₄ (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN
      (Formalism.L2.SG.RealObj.VtPt X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq)

end Carrier

theorem glob_f_eq {D : D7} {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) {u u' : D.what₂.Word} (hC : Formalism.L2.SG.DataInst.Compat S u u') :
    S.G.f = D.R.f := by
  first | unfold Formalism.L2.SG.DataInst.Compat at hC | skip
  have hf := hC.2.2.2.2.2.2
  show Fintype.card (InfinitePlace D.host.E) = D.R.f
  rw [← hf]
  first
  | exact (Fintype.card_congr S.pl).symm.trans (Fintype.card_fin S.f)
  | (rw [← Fintype.card_fin S.f]; exact (Fintype.card_congr S.pl).symm)
  | (convert (Fintype.card_congr S.pl).symm using 1; simp)

theorem pos_facts {P : Type} [Fintype P] {B : S3.MassData P} (hP : B.Pos) : 0 < B.n0c ∧ 0 < B.c0 * B.c0' := by
  have hQ := hP
  unfold S3.MassData.Pos at hQ
  casesm* _ ∧ _
  refine ⟨?_, ?_⟩
  · first | positivity | (unfold S3.MassData.n0c; positivity)
  · first | positivity | (unfold S3.MassData.c0 S3.MassData.c0'; positivity) | (unfold S3.MassData.c0; positivity)

theorem kv_nonneg {E : Type} [Field E] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {P : Type} [Fintype P] {B : S3.MassData P} {c : ℕ → TB.Pt E → ℂ} {Vt : TB.Pt E → H}
    (hI : KVIdentity B c Vt) (hP : B.Pos) : 0 ≤ B.KV := by
  obtain ⟨hn, hc⟩ := pos_facts hP
  have h1 : 0 ≤ B.c0 * B.c0' * B.KV := by
    rw [hI.2]
    exact mul_nonneg hn.le (tsum_nonneg fun _ => by positivity)
  by_contra hneg
  push_neg at hneg
  have h2 := mul_neg_of_pos_of_neg hc hneg
  linarith

theorem pos_deg {P : Type} [Fintype P] {B : S3.MassData P} (hP : B.Pos) : 0 < B.deg := by
  have hQ := hP
  unfold S3.MassData.Pos at hQ
  casesm* _ ∧ _
  first | positivity | assumption | (unfold S3.MassData.deg; positivity)

theorem pos_rho {P : Type} [Fintype P] {B : S3.MassData P} (hP : B.Pos) : 0 < B.ρ0 := by
  have hQ := hP
  unfold S3.MassData.Pos at hQ
  casesm* _ ∧ _
  first | positivity | assumption | (unfold S3.MassData.ρ0; positivity)

open Formalism.L2.SG.DataInst in

def RowsInputP (D : D7) : Prop :=
  ∀ (Wp Wq : InfinitePlace D.host.E → Type) [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) →
    ∀ (L : Formalism.L2.SG.CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] → Compat S u u' →
    Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') →
    ∀ (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ nc : ℝ, Formalism.L2.SG.CntLocal.Formula δ L u u' F0 what₂ nc → ∀ α : ℝ, 0 < α →
    BddAbove (densSet L δ ϖ u u' F0 what₂) →
      (∃ κ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ) ∧
      ∀ κ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℕ, RowLabel κ →
        RowsPSD S δ M L u u' F0 what₂ ϖ (Formalism.L2.SG.PairVal.vRdef D u u' F0 what₂ δ M) κ nc α

theorem rowsInputP_of {D : D7} (h : Formalism.L2.SG.DataInst.RowsInputAt D) : RowsInputP D := by
  intro Wp Wq _ _ _ _ S δ M hA L u u' hT hC _ F0 what₂ hR ϖ hϖ nc hF α hα hB
  exact h Wp Wq S δ M hA L u u' hT hC F0 what₂ hR ϖ hϖ nc hF α hα hB

open Formalism.L2.SG.AdBridge Formalism.L2.SG.CntLocal Formalism.L2.SG.DataInst in

theorem theoremS_rec
    (hLMA : ∀ D : D7, LocalModelAt D) (hDIA : ∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → DensInputAt D) (hRIA : ∀ D : D7, RowsInputP D)
    (C₄ Cthr : ℝ) (h4 : 1 ≤ C₄) :
    ∃ CA C : ℝ, Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ (D : D7) (L : SizeData₂ D) (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X)
      (hF : FinX Y) (u u' : D.what₂.Word)
      (G0 : Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ) (l : ℕ)
      (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
      (Lsp : LocSp D Y.M) (ϖ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, 𝒪[(D.s.atP p).Fp])
      (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
      (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u)) (nc Th Cp Cf c5 Cn : ℝ),
      u ≠ u' → Nonempty (SIso D.s (sOf hF)) → 0 ≤ L.sc.b →

      CarrierFull X hb Y u u' X0 ψ (supDens Lsp Y.δ ϖ u u' (X.Fu u) (Y.what₂ u) / ∏' p, alpD u u' p) C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) Q i0 i0' νq C₄ CA G0 de de' l →
      Fintype.card (InfinitePlace X.B.I.F) = D.R.f →

      k0 ≤ G0.k →
      J.SzHyp G0 CA C0 CG CDel cT Cb L.sc.b Cp Th de de' (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') l →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log L.sc.b ≤ G0.f * Real.log G0.k →
      2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k →

      (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
      Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') → Formalism.L2.SG.Pf.LocCP.LocTied D →
      (∀ p, Irreducible (ϖ p)) → Formula Y.δ Lsp u u' (X.Fu u) (Y.what₂ u) nc → RowLabel κ →
      RowsSum (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) κ (nc * ∏' p, alpD u u' p)
        (Formalism.L2.SG.RealObj.VtPt X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq) →

      Formalism.L2.SG.MassDataForm.RowFormC X hb Y u u' X0 ψ (supDens Lsp Y.δ ϖ u u' (X.Fu u) (Y.what₂ u) / ∏' p, alpD u u' p) C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) Q Y.M Y.δ i0 i0' νq κ nc →
      PB.MassDataHyp (massDataY X hb Y u u' X0 ψ (supDens Lsp Y.δ ϖ u u' (X.Fu u) (Y.what₂ u) / ∏' p, alpD u u' p) C Th
          (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) Q i0 i0' νq) →
      PB.Link (Y.tO u u') (massDataY X hb Y u u' X0 ψ (supDens Lsp Y.δ ϖ u u' (X.Fu u) (Y.what₂ u) / ∏' p, alpD u u' p) C Th
          (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) Q i0 i0' νq)
        G0 de (D.mem u).A.T (D.duS u) (D.duS u') →
      PB.SplitInputs (Y.tO u u') (massDataY X hb Y u u' X0 ψ (supDens Lsp Y.δ ϖ u u' (X.Fu u) (Y.what₂ u) / ∏' p, alpD u u' p) C Th
          (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) Q i0 i0' νq).tt →

      PB.SizeNumbers G0.k G0.r G0.f L.sc.b G0.g1 G0.g2 c5 Cn →
      (Y.tO u u').RowBig (Real.exp (-(c5 * G0.k * G0.f * Real.log G0.k)))
        ((D.duS u : ℝ) * (D.duS u') / (G0.size de (D.mem u).A.T (D.duS u)).Dstar) →
      (Y.tO u u').RowNotScalar (Real.exp (-(c5 * G0.k * G0.f * Real.log G0.k)))
        ((D.duS u : ℝ) * (D.duS u') / (G0.size de (D.mem u).A.T (D.duS u)).Dstar) →
      (Y.tO u u').RowNG (((2 : ℝ) ^ (G0.k - 2 * G0.r - 5))⁻¹ *
          Real.exp (Cn * ((2 * G0.r + 2 : ℕ) : ℝ) ^ 5 * G0.f * Real.log L.sc.b))
        ((D.duS u : ℝ) * (D.duS u') / (G0.size de (D.mem u).A.T (D.duS u)).Dstar) →
      (G0.size de (D.mem u).A.T (D.duS u)).Dstar = D.what₂.Dstar →

      Formalism.L2.SG.TermOp.KExpansion (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK (Y.Dt u) (Y.Dt u') →
      Formalism.L2.SG.TermOp.AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') →
      (Y.tO u u').IdDegenerate → (Y.tO u u').part (Y.tO u u').degSet = 0 →
      ‖(Y.tO u u').K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * ((D.duS u : ℝ) * (D.duS u') / D.what₂.Dstar) ∧
      L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar := by
  obtain ⟨CA, C, h1, h2, h3, h5, hrest⟩ := Formalism.L2.SG.TheoremS.pbApplied C₄ Cthr h4
  refine ⟨CA, C, h1, h2, h3, h5, fun C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6 => ?_⟩
  obtain ⟨k0, hk⟩ := hrest C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  refine ⟨k0, ?_⟩
  intro D L X hb Y hF u u' G0 de de' l i0 i0' νq X0 ψ Lsp ϖ κ Q nc Th Cp Cf c5 Cn hne hI hb0
    hCar hcard hk0 hSz h16 hCf hsize hTT hPH hLTr hϖ hFo hκ hSum hKVI hBI hLink hSplit hSN hRB hRNS hRNG hDst hE hA hId hK2
  obtain ⟨Wp, Wq, i1, i2, i3, i4, i5, S, _, _, _, _, _, _, _, _, _, hCA, hG, hde, hde', hl, hC,
    _, _, _, hRI⟩ := hCar
  subst hG hde hde' hl
  have hInst : J.Inst (dOf S Y.δ Y.M u u') S.pl S.G CA S.de S.de'
      ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) S.l := by
    have h := inst_dOf S Y.δ Y.M u u'
    rw [hCA, hC.2.2.2.2.1, hC.2.2.2.2.2.1] at h
    exact h
  have hLM := hLMA D Wp Wq S Y.δ Y.M Y.agree u u' hC
  obtain ⟨-, hBdd, -, hαpos, hDens⟩ := hDIA D hLTr hsize Y.δ Y.M Y.agree Lsp u u' hTT (X.Fu u) (Y.what₂ u) (Y.rowsOK u) ϖ hϖ
  have hDI : PB.DensInput S.G.k S.G.r S.G.f (supDens Lsp Y.δ ϖ u u' (X.Fu u) (Y.what₂ u) / ∏' p, alpD u u' p) := by
    rw [hC.2.1, hC.1, glob_f_eq S hC]
    exact hDens
  have hPSD := (hRIA D Wp Wq S Y.δ Y.M Y.agree Lsp u u' hTT hC hPH (X.Fu u) (Y.what₂ u) (Y.rowsOK u) ϖ hϖ nc hFo _ hαpos hBdd).2 κ hκ
  have hKV' : KVIdentity (massDataY X hb Y u u' X0 ψ (supDens Lsp Y.δ ϖ u u' (X.Fu u) (Y.what₂ u) / ∏' p, alpD u u' p) C Th
      (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) Q i0 i0' νq)
      (rowVec (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) κ (nc * ∏' p, alpD u u' p))
      (Formalism.L2.SG.RealObj.VtPt X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq) := hKVI
  have hRows := rowsInput_of hC hPSD hSum _ rfl (kv_nonneg hKV' hBI.1) (kv_identity_bound hKV' (pos_facts hBI.1).1.le)
  have : CompleteSpace (Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u)) := FiniteDimensional.complete ℂ _
  have : CompleteSpace (Formalism.L2.SG.TermOp.H1 X u u' (Y.what₂ u) (Y.what₂ u')) := FiniteDimensional.complete ℂ _
  have hEL := Formalism.L2.SG.MassDataConc.energyLink_bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u')
    (supDens Lsp Y.δ ϖ u u' (X.Fu u) (Y.what₂ u) / ∏' p, alpD u u' p) C Th (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) Q Y.M Y.δ
    i0 i0' νq _ rfl
  rw [hcard, ← hC.1, ← hC.2.2.2.2.2.2] at hEL
  have hPB := hk D.host.E S.W (dOf S Y.δ Y.M u u') S.pl S.G L.sc.b Cp Cf Th S.de S.de'
    (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') S.l hk0 hSz h16 hCf (unram_host D) hInst hLM
    _ _ _ _ _ hRI hDI _ _ hRows hBI hEL _ _ _ _ _ (Y.tO u u') c5 Cn hLink hSplit hSN hRB hRNS hRNG
  refine ⟨by rw [hDst] at hPB; exact hPB, ?_⟩
  exact packageTieConc D L hb0 Formalism.L2.SG.Pf.isoNorm X Y hF hI u u' hne (Formalism.L2.SG.Pf.dimTie X u)
    (Formalism.L2.SG.Pf.dimTie X u') hE hA hId hK2 (Formalism.L2.SG.Pf.normTie hF u u')
    ⟨_, _, S.G, S.de, (D.mem u).A.T, (D.duS u : ℝ), (D.duS u' : ℝ), ⟨rfl, rfl, rfl, hDst⟩, hPB⟩

section STies

open Formalism.L2.SG.AdBridge Formalism.L2.SG.PoincareInHH.PoincareSetting

structure STies (D : D7) where
  X : HidaSetting D
  hb : AdBridgeIso X.B.I
  Y : Formalism.L2.SG.Full.Full X
  hI : ∀ hF : FinX Y, SIso D.s (sOf hF)
  ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ
  autTie : Formalism.MainNotions.S.AutTie D X.B X.pl
  measTie : X.MeasTie hb
  ψ_char : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ
  ψ_std : Formalism.L2.SG.LocVol.IsStdChar ψ
  measCompat : Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ
  locCompat : ∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w

def SConc2 (D : D7) : Prop := Nonempty (STies D)

variable {D : D7}

theorem STies.duC_eq (T : STies D) (hF : FinX T.Y) (u : D.what₂.Word) : Formalism.L2.SG.RowsConc.duC T.X T.Y u = (D.duS u : ℝ) := by
  have h := finrank_cols hF (T.hI hF) u
  unfold Formalism.L2.SG.RowsConc.duC
  exact_mod_cast h

theorem STies.dstC_eq (T : STies D) : Formalism.L2.SG.RowsConc.DstC T.X = D.what₂.Dstar := by
  first
  | exact T.autTie.Dstar_eq.symm
  | exact (Formalism.MainNotions.S.AutTie.Dstar_eq T.autTie).symm
  | (rw [T.autTie.Dstar_eq]; rfl)

theorem STies.concTie (T : STies D) (hF : FinX T.Y) (hK : T.X.LevelSubgroupNormalized)
    (hN : ∀ u, Formalism.L2.SG.PoincareInHH.Cut.NeatKu T.X u T.Y.hK) (hW : Formalism.L2.SG.WuDecay.WuDecay T.X)
    (hph : Integrable T.X.ph (Formalism.L2.SG.ProjRows.muInf T.X.B.I)) (hLT : Formalism.L2.SG.Pf.LocCP.LocTied D)
    (hTF : Formalism.L2.SG.RowsConc.TFrameAt D) : Formalism.L2.SG.RowsConc.ConcTie T.X T.Y := by
  unfold Formalism.L2.SG.RowsConc.ConcTie
  exact ⟨hK, hN, fun u => T.duC_eq hF u, T.dstC_eq, hW, hph,
    ⟨T.hb, T.ψ, T.measTie, T.ψ_char, T.ψ_std, T.measCompat, T.locCompat, hLT⟩, hTF⟩

theorem STies.sConc (T : STies D) (hF : FinX T.Y) (hK : T.X.LevelSubgroupNormalized) (hCL : ∀ u, ColsLink T.X u T.Y.hK) (hW : Formalism.L2.SG.WuDecay.WuDecay T.X)
    (hph : Integrable T.X.ph (Formalism.L2.SG.ProjRows.muInf T.X.B.I)) : SConc D := by
  unfold SConc
  exact ⟨T.X, T.hb, T.Y, hF, T.autTie, hK, hCL, T.measTie, ⟨T.ψ, T.ψ_char, T.ψ_std, T.measCompat⟩, hW, hph, ⟨T.hI hF⟩⟩

end STies

section GlobOf

variable (D : D7)

open Classical in

def gOf (e : InfinitePlace D.host.E ≃ D.what₂.Tau) : Sz.Glob (InfinitePlace D.host.E) where
  k := D.R.k
  r := D.R.rS
  Del := D.s.Del
  vlast w := vOne D (e w) (D.R.k - 1)
  b w j := bOne D (e w) j
  a w := uOne D D.u₀ (e w) 1
  top w := decide (IsTop D (e w))
  bp w := bTop D (e w)
  v := D.host.v
  dF := (2 * D.host.v) ^ D.R.f
  Lv M := Formalism.HermitianLatticesTheory.lValEta D.host.E M
  vol := Formalism.MainNotions.BridgeLemma.szaMass D
  g1 := D.host.g 0
  g2 := D.host.g 1
  dsig w := D.dsig (e w)

def deOf (τ : D.what₂.Tau) (u : D.what₂.Word) (l : ℕ) : ℝ :=
  if 1 ≤ l ∧ l + 2 ≤ D.R.k then (vOne D τ l - 1 / 2 - uOne D u τ (l + 1)) / D.s.Del else 0

open Classical in

def lOf (de de' : ℕ → ℝ) : ℕ :=
  if h : ∃ l, 1 ≤ l ∧ l + 2 ≤ D.R.k ∧ de l ≠ de' l then Nat.find h else 0

end GlobOf

open Formalism.L2.SG.AdBridge Formalism.L2.SG.CntLocal Formalism.L2.SG.DataInst Formalism.L2.SG.RowsConc in

theorem theoremS_recursion_fixed
    (hLMA : ∀ D : D7, LocalModelAt D) (hDIA : ∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → DensInputAt D) (hRIA : ∀ D : D7, RowsInputP D)
    (hNG : RowNGC)
    (C₄ Cthr : ℝ) (h4 : 1 ≤ C₄) :
    ∃ CA C : ℝ, Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (hF : FinX T.Y) (u u' : D.what₂.Word)
      (G0 : Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ) (l : ℕ)
      (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
      (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E)
      (Lsp : LocSp D T.Y.M) (ϖ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, 𝒪[(D.s.atP p).Fp])
      (κ : Formalism.L2.SG.TermDef.Term D u u' (T.X.Fu u) (T.Y.what₂ u) → ℕ)
      (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u)) (nc Th Cp Cf : ℝ),
      u ≠ u' → 0 ≤ L.sc.b →

      CarrierFull T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq C₄ CA G0 de de' l →
      Fintype.card (InfinitePlace T.X.B.I.F) = D.R.f →

      k0 ≤ G0.k →
      J.SzHyp G0 CA C0 CG CDel cT Cb L.sc.b Cp Th de de' (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') l →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log L.sc.b ≤ G0.f * Real.log G0.k →
      2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k →
      PB.SizeNumbers G0.k G0.r G0.f L.sc.b G0.g1 G0.g2 (1 / 3) Cn →
      (G0.size de (D.mem u).A.T (D.duS u)).Dstar = D.what₂.Dstar →

      (T.Y.tO u u').RowBig (epsL D) (ddC T.X T.Y u u') → (T.Y.tO u u').RowNotScalar (epsL D) (ddC T.X T.Y u u') →
      Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f →
      Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (T.Y.tO u u').AbsConv →

      (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
      (∀ p, Irreducible (ϖ p)) → Formula T.Y.δ Lsp u u' (T.X.Fu u) (T.Y.what₂ u) nc → RowLabel κ →
      RowsSum (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) κ (nc * ∏' p, alpD u u' p)
        (Formalism.L2.SG.RealObj.VtPt T.X u u' 1 i0 i0' (T.Y.FN u) (T.Y.FN u') νq) →

      Formalism.L2.SG.MassDataForm.RowFormC T.X T.hb T.Y u u' X0 T.ψ
        (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq κ nc →
      PB.MassDataHyp (massDataY T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
          (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq) →
      PB.Link (T.Y.tO u u') (massDataY T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
          (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq)
        G0 de (D.mem u).A.T (D.duS u) (D.duS u') →
      PB.SplitInputs (T.Y.tO u u') (massDataY T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p)
          C Th (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq).tt →

      Formalism.L2.SG.TermOp.KExpansion (T.X.Fu u) (T.X.Fu u') (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u') T.Y.hK
        (T.Y.Dt u) (T.Y.Dt u') →
      Formalism.L2.SG.TermOp.AbsConvT (T.X.Fu u) (T.X.Fu u') T.Y.TR (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u') →
      (T.Y.tO u u').IdDegenerate → (T.Y.tO u u').part (T.Y.tO u u').degSet = 0 →
      ‖(T.Y.tO u u').K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * ((D.duS u : ℝ) * (D.duS u') / D.what₂.Dstar) ∧
      L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar := by
  obtain ⟨CA, C, h1, h2, h3, h5, hrest⟩ := theoremS_rec hLMA hDIA hRIA C₄ Cthr h4
  refine ⟨CA, C, h1, h2, h3, h5, ?_⟩
  intro C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb
  obtain ⟨k0, hk0⟩ := hrest C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb
  refine ⟨k0, ?_⟩
  intro Cg cb Cw cTf CT C0f
  obtain ⟨Cn, hCn, C'₀, Cl₀, hNG'⟩ := hNG Cg cb Cw cTf CT C0f
  refine ⟨Cn, C'₀, Cl₀, hCn, ?_⟩
  intro C' Cl hC' hCl D L T hF u u' G0 de de' l i0 i0' νq X0 Lsp ϖ κ Q nc Th Cp Cf huu hb hCar hcard hk hSz h16 hCf hk2
    hSN hDst hRB hRNS hH0 hSt hCT hAC hmod hϖ hFo hRL hRS hRF hBI hLk hSI hKE hAT hID hpart
  have hNGr := hNG' C' Cl hC' hCl D L T.X T.Y u u' hH0 hSt hCT hAC
  have hCar' := hCar
  obtain ⟨Wp, Wq, i1, i2, i3, i4, i5, S, Tw, fw, ν', m₀, τ, Qm, Qim, eP, eQ, _, hSG, _, _, _, hComp, _⟩ := hCar'
  have hComp' := hComp
  unfold Formalism.L2.SG.DataInst.Compat at hComp'
  have hGr : G0.r = D.R.rS := by rw [← hSG]; exact hComp'.1
  have hGk : G0.k = D.R.k := by rw [← hSG]; exact hComp'.2.1
  have hGf : G0.f = D.R.f := by rw [← hSG]; exact glob_f_eq S hComp
  have hCT' := hCT
  unfold Formalism.L2.SG.RowsConc.ConcTie at hCT'
  obtain ⟨_, _, hdu, hDs, _, _, ⟨_, _, _, _, _, _, _, hLT⟩, _⟩ := hCT'
  have hPH : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') := by
    first
    | exact Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt
    | exact Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' (by unfold Formalism.MainNotions.VanishingOnXAndXPlus.Stand; unfold Formalism.MainNotions.S.Cnt.Stand at hSt; exact hSt)
  have hrat : (D.duS u : ℝ) * (D.duS u') / (G0.size de (D.mem u).A.T (D.duS u)).Dstar =
      Formalism.L2.SG.RowsConc.ddC T.X T.Y u u' := by
    rw [hDst]
    unfold Formalism.L2.SG.RowsConc.ddC
    rw [hdu u, hdu u', hDs]
  have heL : Real.exp (-((1 / 3 : ℝ) * G0.k * G0.f * Real.log G0.k)) = Formalism.L2.SG.RowsConc.epsL D := by
    unfold Formalism.L2.SG.RowsConc.epsL
    rw [hGk, hGf]
  have heN : ((2 : ℝ) ^ (G0.k - 2 * G0.r - 5))⁻¹ * Real.exp (Cn * ((2 * G0.r + 2 : ℕ) : ℝ) ^ 5 * G0.f * Real.log L.sc.b) =
      Formalism.L2.SG.RowsConc.epsNG D L Cn := by
    unfold Formalism.L2.SG.RowsConc.epsNG Formalism.L2.SG.RowsConc.mR
    rw [hGk, hGr, hGf]
  exact hk0 D L T.X T.hb T.Y hF u u' G0 de de' l i0 i0' νq X0 T.ψ Lsp ϖ κ Q nc Th Cp Cf (1 / 3) Cn huu ⟨T.hI hF⟩ hb hCar
    hcard hk hSz h16 hCf hk2 hmod hPH hLT hϖ hFo hRL hRS hRF hBI hLk hSI hSN
    (by first | (rw [heL, hrat]; exact hRB) | (convert hRB using 1 <;> first | exact heL | exact hrat))
    (by first | (rw [heL, hrat]; exact hRNS) | (convert hRNS using 1 <;> first | exact heL | exact hrat))
    (by first | (rw [heN, hrat]; exact hNGr) | (convert hNGr using 1 <;> first | exact heN | exact hrat))
    hDst hKE hAT hID hpart

section MassDataHypotheses

open Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol Formalism.L2.SG.RealObj

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

abbrev anY : AnIn :=
  anOf (Y.tO u u') (Formalism.L2.SG.MassDataConc.kapN D * DisintegrationConstant X u u' 1) (degX X)
    ((locOf X u u' ψ).volZZ / (((locOf X u u' ψ).localVolumeArchimedean * ∏ p, (locOf X u u' ψ).localVolumeAtPlace p) * (locOf X u u' ψ).volPP) *
      ((locOf X u u' ψ).volPP * (IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D)))
    (IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D) (IntOO X u u' 1) sd C Th D.R.rS (Fintype.card (InfinitePlace X.B.I.F))
    ⟨KVOf X u u' vR Q (VConstants X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq),
      KtopVOf X u u' Y.M Y.δ (VConstants X u u' 1 i0 i0' (Y.FN u) (Y.FN u') νq)⟩

def MassDataPosY : Prop := (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).Pos

theorem massDataInputs_Y (hPos : MassDataPosY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq)
    (hForm : InFormC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq)
    (hNu : InNuX X u u' 1) (hInf : InInfinityX X u u' 1) (hk : Formalism.L2.SG.MassDataConc.kapN D ≠ 0)
    (hH : HypX X hb (Y.FN u) (Y.FN u') u u')
    (hVol : InVolumesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hstd : IsStdChar ψ) (hMC : MeasCompatψ X ψ)
    (hdet : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0)
    (hLS : InLevelSAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hMs : InMassesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hCo : InColumnsAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hIx : InIndicesAt X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq))
    (hP : ProdConv X u u' ψ)
    (hTy : InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq)
    (hLT : LocTieX X ψ u) (hLT' : LocTieX X ψ u') (hTF : TypFacts X u u') :
    PB.MassDataHyp (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) := by
  refine ⟨hPos, hForm, ?_, rfl, ?_, ?_, ?_, hLS hH, hMs hH, hCo hH, inOrdinary_bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ
    (Y.tO u u') sd C Th vR Q Y.M Y.δ i0 i0' νq hP, hTy hH hP hLT hLT' hTF, hIx hH⟩
  ·
    have hρ : (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).ρ0 ≠ 0 := ne_of_gt (pos_rho hPos)
    exact inMass_bC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (Y.tO u u') sd C Th _ hρ
  ·
    show IntOO X u u' 1 = Formalism.L2.SG.MassDataConc.kapN D * DisintegrationConstant X u u' 1 * (IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D)
    rw [mul_assoc, mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ hk]
    unfold IntOO IntC
    rw [hNu, ENNReal.toReal_mul, ENNReal.toReal_ofReal (cooOf_nonneg X u u' 1)]
  ·
    show IntOO X u u' 1 ≤ 1 / degX X
    exact ENNReal.toReal_le_of_le_ofReal (one_div_nonneg.mpr (pos_deg hPos).le) hInf.2.2
  · exact inVolumes_of_compat X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (locOf X u u' ψ) (anY X Y u u' ψ sd C Th vR Q i0 i0' νq)
      hVol hH ⟨ψ, hψ, hstd, hMC⟩ hdet

end MassDataHypotheses

open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.RealObj in

def CarrierC : Prop :=
  ∃ C₄ CA₀ : ℝ, 1 ≤ C₄ ∧ ∀ CA : ℝ, CA₀ ≤ CA → 1 ≤ CA →
    ∀ C0 CG CDel cT Cb : ℝ, 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
      (τ : D.what₂.Tau) (Cp Th' : ℝ)
      (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
      (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd C Th : ℝ)
      {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
      (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂),
      u ≠ u' → k0 ≤ (gOf D e).k → Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f →
      (∀ x : InfinitePlace D.host.E,
        InfinitePlace.mk ((T.X.B.I.φ (T.X.pl.symm (e x))).comp T.X.ιE.symm.toRingHom) = x) →
      J.SzHyp (gOf D e) CA C0 CG CDel cT Cb L.sc.b Cp Th' (deOf D τ u) (deOf D τ u')
        (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
      (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
      CarrierFull T.X T.hb T.Y u u' X0 T.ψ sd C Th vR Q i0 i0' νq C₄ CA (gOf D e) (deOf D τ u) (deOf D τ u')
        (lOf D (deOf D τ u) (deOf D τ u'))

open Formalism.L2.SG.AdBridge Formalism.L2.SG.CntLocal Formalism.L2.SG.DataInst Formalism.L2.SG.RowsConc in

theorem theoremS_recursion_constants
    (hLMA : ∀ D : D7, LocalModelAt D) (hDIA : ∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → DensInputAt D) (hRIA : ∀ D : D7, RowsInputP D)
    (hNG : RowNGC) (hCar : CarrierC) (Cthr : ℝ) :
    ∃ C₄ CA C : ℝ, 1 ≤ C₄ ∧ Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (hF : FinX T.Y) (u u' : D.what₂.Word)
      (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (τ : D.what₂.Tau)
      (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
      (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E)
      (Lsp : LocSp D T.Y.M) (ϖ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, 𝒪[(D.s.atP p).Fp])
      (κ : Formalism.L2.SG.TermDef.Term D u u' (T.X.Fu u) (T.Y.what₂ u) → ℕ)
      (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u)) (nc Th Cp Cf : ℝ),
      u ≠ u' → 0 ≤ L.sc.b →

      (∀ v, i0 v = i0' v) → Formalism.L2.SG.RealObj.PtRepExists T.X u u' 1 i0 i0' → Formalism.L2.SG.RealObj.NuQPin T.X u u' νq →
      (∀ x : InfinitePlace D.host.E,
        InfinitePlace.mk ((T.X.B.I.φ (T.X.pl.symm (e x))).comp T.X.ιE.symm.toRingHom) = x) →
      Fintype.card (InfinitePlace T.X.B.I.F) = D.R.f →

      k0 ≤ (gOf D e).k →
      J.SzHyp (gOf D e) CA C0 CG CDel cT Cb L.sc.b Cp Th (deOf D τ u) (deOf D τ u') (D.mem u).A.T (D.mem u').A.T
        (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log L.sc.b ≤ (gOf D e).f * Real.log (gOf D e).k →
      2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k →
      PB.SizeNumbers (gOf D e).k (gOf D e).r (gOf D e).f L.sc.b (gOf D e).g1
        (gOf D e).g2 (1 / 3) Cn →
      ((gOf D e).size (deOf D τ u) (D.mem u).A.T (D.duS u)).Dstar = D.what₂.Dstar →

      (T.Y.tO u u').RowBig (epsL D) (ddC T.X T.Y u u') → (T.Y.tO u u').RowNotScalar (epsL D) (ddC T.X T.Y u u') →
      Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f →
      Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (T.Y.tO u u').AbsConv →

      (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
      (∀ p, Irreducible (ϖ p)) → Formula T.Y.δ Lsp u u' (T.X.Fu u) (T.Y.what₂ u) nc → RowLabel κ →
      RowsSum (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) κ (nc * ∏' p, alpD u u' p)
        (Formalism.L2.SG.RealObj.VtPt T.X u u' 1 i0 i0' (T.Y.FN u) (T.Y.FN u') νq) →

      Formalism.L2.SG.MassDataForm.RowFormC T.X T.hb T.Y u u' X0 T.ψ
        (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
        (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq κ nc →
      PB.MassDataHyp (massDataY T.X T.hb T.Y u u' X0 T.ψ (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p)
          C Th (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq) →
      PB.Link (T.Y.tO u u') (massDataY T.X T.hb T.Y u u' X0 T.ψ
          (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
          (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq)
        (gOf D e) (deOf D τ u) (D.mem u).A.T (D.duS u) (D.duS u') →
      PB.SplitInputs (T.Y.tO u u') (massDataY T.X T.hb T.Y u u' X0 T.ψ
          (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
          (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q i0 i0' νq).tt →

      Formalism.L2.SG.TermOp.KExpansion (T.X.Fu u) (T.X.Fu u') (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u') T.Y.hK
        (T.Y.Dt u) (T.Y.Dt u') →
      Formalism.L2.SG.TermOp.AbsConvT (T.X.Fu u) (T.X.Fu u') T.Y.TR (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u') →
      (T.Y.tO u u').IdDegenerate → (T.Y.tO u u').part (T.Y.tO u u').degSet = 0 →
      ‖(T.Y.tO u u').K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * ((D.duS u : ℝ) * (D.duS u') / D.what₂.Dstar) ∧
      L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar := by
  obtain ⟨C₄, CA₀, h4, hC⟩ := hCar
  obtain ⟨CA, C, h1, h2, h3, h5, hrest⟩ := theoremS_recursion_fixed hLMA hDIA hRIA hNG C₄ (max Cthr CA₀) h4
  refine ⟨C₄, CA, C, h4, le_trans (le_max_left _ _) h1, h2, h3, h5, fun C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6 => ?_⟩
  obtain ⟨k0, hk⟩ := hrest C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  obtain ⟨k0c, hCk⟩ := hC CA (le_trans (le_max_right _ _) h1) h2 C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  refine ⟨max k0 k0c, fun Cg cb Cw cTf CT C0f => ?_⟩
  obtain ⟨Cn, C'₀, Cl₀, hCn, hrow⟩ := hk Cg cb Cw cTf CT C0f
  obtain ⟨C'₁, Cl₁, hCc⟩ := hCk Cg cb Cw cTf CT C0f
  refine ⟨Cn, max C'₀ C'₁, max Cl₀ Cl₁, hCn, fun C' Cl hC' hCl => ?_⟩
  intro D L T hF u u' e τ i0 i0' νq X0 Lsp ϖ κ Q nc Th Cp Cf hne hb0 hii hPt hNu hPT hcard hk0 hSz h16 hCf hsize hSN
    hDst hRB hRNS hHyp0 hStand hCT hAC hTT hϖ hFo hκ hSum hKVI hBI hLink hSplit hE hA hId hK2
  have hCF := hCc C' Cl (le_trans (le_max_right _ _) hC') (le_trans (le_max_right _ _) hCl) D L T u u' e τ Cp Th i0 i0' νq X0
    (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
    (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q hne (le_trans (le_max_right _ _) hk0) hHyp0 hPT
    hSz hii hPt hNu
  exact hrow C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_left _ _) hCl) D L T hF u u' (gOf D e) (deOf D τ u)
    (deOf D τ u') (lOf D (deOf D τ u) (deOf D τ u')) i0 i0' νq X0 Lsp ϖ κ Q nc Th Cp Cf hne hb0 hCF hcard
    (le_trans (le_max_left _ _) hk0) hSz h16 hCf hsize hSN hDst hRB hRNS hHyp0 hStand hCT hAC hTT hϖ hFo hκ hSum hKVI hBI
    hLink hSplit hE hA hId hK2

end Formalism.L2.SG.SpectralTiesReal
