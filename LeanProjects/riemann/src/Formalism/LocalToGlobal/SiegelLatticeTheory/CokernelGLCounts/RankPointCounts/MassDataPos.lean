import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarDisintegrationRealHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.MassDataPos

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem glkC_pos (k g : ℕ) (hg : g.Prime) : 0 < glkC k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold glkC
  exact Nat.card_pos

theorem ukC_pos (k g : ℕ) (hg : g.Prime) : 0 < ukC k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold ukC
  exact Nat.card_pos

theorem ggC_pos (r k g : ℕ) (hg : g.Prime) : 0 < ggC r k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold ggC
  exact Nat.card_pos

theorem nnC_pos (r k g : ℕ) (hg : g.Prime) : 0 < nnC r k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold nnC
  rw [Nat.card_pos_iff]
  refine ⟨⟨⟨1, ?_⟩⟩, inferInstance⟩
  unfold Formalism.FourierDecayAlt.S3.IsN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp only [Formalism.DoubleCosetMeasures.IsUpUni, Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32]
       exact ⟨fun i j hij => by simp [Matrix.one_apply, (show j < i from hij).ne'], fun a => by simp [Matrix.one_apply]⟩)
    | (simp [Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32, Matrix.one_apply]; done)
    | (ext i j; simp [Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32, Matrix.one_apply]; done)

section Main

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

abbrev bk : Formalism.FourierDecayAlt.S3.MassData (TypX X) := bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq

def MassDataPosC : Prop := (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos

def LocHaarPosC : Prop :=
  (∀ p, 0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnatp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKppp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSp' p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSppp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSppp' p) ∧
  0 < (X.measG.μGf (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))).toReal ∧
  0 < ((X.measW u).μSf (Subtype.val ⁻¹' (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal ∧
  0 < ((X.measW u').μSf (Subtype.val ⁻¹' (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μHpp ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μHpp' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μN ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μN'

def CovolPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volNa ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volNa' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volB

def QuotVolPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN'

def RecPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).deg ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).dimπ ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).dimπ' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).ρ0 ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).ρ0' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d'

theorem gOf_prime (p : TypX X) : (gOf p).Prime := by
  unfold gOf
  split_ifs
  · exact D.host.g_prime 0
  · exact D.host.g_prime 1

theorem massDataPosC_of (hL : LocHaarPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hCv : CovolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hQv : QuotVolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hR : RecPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hP : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hCoo : 0 < Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1)
    (hκ : 0 < Formalism.L2.SG.MassDataConc.kapN D) (hsd : 0 ≤ sd) (hC : 0 ≤ C) (hTh : 0 < Th) :
    MassDataPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  obtain ⟨hv, -, -, -, hUo, -, hZZ, hPP, -, hal, -⟩ := hP
  obtain ⟨hloc, hGf, hSf, hSf', hH, hH', hHpp, hHpp', hN, hN'⟩ := hL
  obtain ⟨hG, hHa, hHa', hNa, hNa', hB⟩ := hCv
  obtain ⟨hvH, hvH', hvN, hvN'⟩ := hQv
  obtain ⟨hdeg, hdp, hdp', hr0, hr0', hd, hd'⟩ := hR
  set B := bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq with hBdef
  have hMp : ∀ p, 0 < B.Mp p := fun p => (hv p.1).1 p.2
  have hU00p : ∀ p, 0 < B.localVolumeAtPlace p := fun p => (hv p.1).2.1
  have hKo : 0 < B.μKo := div_pos hGf (Finset.prod_pos fun p _ => (hloc p).1)
  have hSo : 0 < B.μSo := div_pos hSf (Finset.prod_pos fun p _ => (hloc p).2.2.2.1)
  have hSo' : 0 < B.μSo' := div_pos hSf' (Finset.prod_pos fun p _ => (hloc p).2.2.2.2.1)
  have hU00o : 0 < B.localVolumeArchimedean := hUo
  have hMo : 0 < B.Mo := div_pos (mul_pos hU00o (pow_pos hKo 2)) (mul_pos hSo hSo')
  have hZ : 0 < B.volZZ := hZZ
  have hPPp : 0 < B.volPP := by
    show 0 < ∏ l : Fin (D.R.rS + 1), ∏' v : Formalism.L2.SG.LocVol.PlX X, Formalism.L2.SG.LocVol.PPX X u u' ψ l v
    exact Finset.prod_pos fun l _ => (hPP l).2
  have hAl : 0 < B.al := mul_pos (Finset.prod_pos fun p _ => (hv p.1).2.2.2.2) hal
  have hCo : 0 < B.Coo := mul_pos hκ hCoo
  have hMM : 0 < B.MM := mul_pos hMo (Finset.prod_pos fun p _ => hMp p)
  have hμK : 0 < B.μK := mul_pos hKo (Finset.prod_pos fun p _ => (hloc p).1)
  have hAA : 0 < B.AA := div_pos (mul_pos (mul_pos hB hCo) (div_pos hMM hZ)) hμK
  have hn0c : 0 < B.n0c := div_pos hAA hr0
  have hgp : ∀ p, 0 < B.g p := fun p => by
    show (0 : ℝ) < ((gOf p : ℕ) : ℝ)
    exact_mod_cast (gOf_prime X p).pos
  have hglk : ∀ p, 0 < B.glk p := fun p => by
    show (0 : ℝ) < ((glkC D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast glkC_pos _ _ (gOf_prime X p)
  have huk : ∀ p, 0 < B.uk p := fun p => by
    show (0 : ℝ) < ((ukC D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast ukC_pos _ _ (gOf_prime X p)
  have hnn : ∀ p, 0 < B.nn p := fun p => by
    show (0 : ℝ) < ((nnC D.R.rS D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast nnC_pos _ _ _ (gOf_prime X p)
  have hgg : ∀ p, 0 < B.gg p := fun p => by
    show (0 : ℝ) < ((ggC D.R.rS D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast ggC_pos _ _ _ (gOf_prime X p)
  have hδ : 0 ≤ B.δ := by
    show 0 ≤ C * ((D.R.rS : ℝ) + 1) * (C / Th) ^ (Fintype.card (NumberField.InfinitePlace X.B.I.F))
    exact mul_nonneg (mul_nonneg hC (by positivity)) (pow_nonneg (div_nonneg hC hTh.le) _)
  unfold MassDataPosC Formalism.FourierDecayAlt.S3.MassData.Pos
  exact ⟨fun p => ⟨hgp p, hglk p, huk p, hnn p, hgg p, (hloc p).1, (hloc p).2.1, (hloc p).2.2.1, (hloc p).2.2.2.1,
      (hloc p).2.2.2.2.1, (hloc p).2.2.2.2.2.1, (hloc p).2.2.2.2.2.2, hMp p, hU00p p⟩,
    hKo, hSo, hSo', hMo, hU00o, hH, hH', hHpp, hHpp', hN, hN', hZ, hPPp, hAl, hG, hHa, hHa', hNa, hNa', hB, hvH, hvH',
    hvN, hvN', hCo, hdeg, hdp, hdp', hr0, hr0', hd, hd', hn0c, hsd, hδ⟩

end Main

theorem cooOf_pos {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) : 0 < Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 := by
  have h := Formalism.L2.SG.RealObj.InfCut.ProductExactness.haar_disintegration_real_holds D X u u' 1 one_pos
  have h' : ∃ C, 0 < C ∧ Formalism.L2.SG.RealObj.Disint X u u' 1 C := h
  unfold Formalism.L2.SG.RealObj.DisintegrationConstant
  rw [dif_pos h']
  exact h'.choose_spec.1

theorem quotVolPosC_of {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hK2 : X.LevelSubgroupNormalized) (hV : 0 < X.volK2) :
    QuotVolPosC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  obtain ⟨hN, hH⟩ := Formalism.L2.SG.Closed.VolPosC_holds D X Y u hK2
  obtain ⟨hN', hH'⟩ := Formalism.L2.SG.Closed.VolPosC_holds D X Y u' hK2
  refine ⟨hH, hH', ?_, ?_⟩
  · show 0 < ((X.muN u) (Y.FN u)).toReal
    exact pos_of_mul_pos_right hN hV.le
  · show 0 < ((X.muN u') (Y.FN u')).toReal
    exact pos_of_mul_pos_right hN' hV.le

end Formalism.L2.SG.Pf.MassDataPos
