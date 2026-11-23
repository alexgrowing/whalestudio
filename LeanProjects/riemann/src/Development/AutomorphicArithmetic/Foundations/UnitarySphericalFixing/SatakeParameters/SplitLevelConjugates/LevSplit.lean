import Mathlib
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.IsPrincipalCongruenceAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitReductionStandardFrameConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.G0LiftUnitaryCentralFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceUnitaryLocEqTransposeInv

noncomputable section
set_option maxHeartbeats 1000000

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.CenFrame
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace UpperTheory.One.M.B

private theorem map_eq_one {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) {κ : GAf L n}
    (hK : IsPrincipalCongruenceAt s κ) {y : GL (Fin n) (Os s)} (hy : IsCompOf s κ y) {k : Type} [CommRing k] (φ : Os s →+* k)
    (hφ : IsResidue s φ) : Matrix.GeneralLinearGroup.map φ y = 1 := by
  refine Units.ext (Matrix.ext fun a c => ?_)
  have h0 : φ (y.val a c - (1 : Matrix (Fin n) (Fin n) (Os s)) a c) = 0 := by
    rw [hφ.ker]
    have e : ((y.val a c - (1 : Matrix (Fin n) (Fin n) (Os s)) a c : Os s) : s.v.adicCompletion (maximalRealSubfield L)) =
        ((s.loc n κ).val - 1) a c := by
      rw [Matrix.sub_apply, ← hy a c]
      by_cases h : a = c <;> simp [Matrix.one_apply, h]
    rw [e]
    exact hK a c
  rw [map_sub, sub_eq_zero] at h0
  refine h0.trans ?_
  rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

private theorem map_eq_one_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) {κ : GAf L n}
    (hU : κ ∈ Umax L n) (hK : IsPrincipalCongruenceAt s κ) {y' : GL (Fin n) (Os (GlobalTheory.TypeTame.conjSP s))}
    (hy' : IsCompOf (GlobalTheory.TypeTame.conjSP s) κ y') {k : Type} [CommRing k] (φ : Os (GlobalTheory.TypeTame.conjSP s) →+* k)
    (hφ : IsResidue (GlobalTheory.TypeTame.conjSP s) φ) : Matrix.GeneralLinearGroup.map φ y' = 1 := by
  obtain ⟨y, hy⟩ := GlobalTheory.BlockLiftFrame.exists_isCompOf s hU
  have h1 : Matrix.GeneralLinearGroup.map (φ : Os s →+* k) y = 1 := map_eq_one s hK hy φ ⟨hφ.surj, hφ.ker⟩
  have h2 : Matrix.GeneralLinearGroup.map (φ : Os s →+* k) y⁻¹ = 1 := by rw [map_inv, h1, inv_one]
  have h3 : Matrix.GeneralLinearGroup.map (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype y = s.loc n κ :=
    Units.ext (Matrix.ext fun a c => hy a c)
  refine Units.ext (Matrix.ext fun a c => ?_)
  have e : y'.val a c = (y⁻¹).val c a := by
    apply Subtype.ext
    have h4 : (s.loc n κ)⁻¹ =
        Matrix.GeneralLinearGroup.map (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype y⁻¹ :=
      (congrArg _ h3.symm).trans (MonoidHom.map_inv _ y).symm
    rw [hy' a c, GlobalTheory.ConjLoc.loc_conjSP, h4]
    rfl
  have e2 : (Matrix.GeneralLinearGroup.map (φ : Os s →+* k) y⁻¹).val c a = (1 : GL (Fin n) k).val c a := by rw [h2]
  refine ((congrArg φ e).trans e2).trans ?_
  rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

variable {D : D7}

private theorem red_of_comp {V : TH.HSp D} {n : ℕ} (hn : V.rank = n) {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : Formalism.IndefR.principalLevelFrame.RowPsi V n} (hP : StdFrame hF P) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1)
    (s : SplitPlace D.host.E) {κ : GAf D.host.E n} (hU : κ ∈ Umax D.host.E n)
    (h : ∀ y, IsCompOf s κ y → ∀ φ : Os s →+* Formalism.L2.DIV.kP s.w, IsResidue s φ → Matrix.GeneralLinearGroup.map φ y = 1) :
    Formalism.L2.DIV.redFn β s.w (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
  obtain ⟨φ, b, hφ, hfr⟩ := GlobalTheory.FrameRedSplit.frameRed_exists D V n hn hF P β Λ hP hB s
  obtain ⟨y, hy⟩ := GlobalTheory.BlockLiftFrame.exists_isCompOf s hU
  refine Units.ext (Matrix.ext fun i j => ?_)
  have e := hfr κ hU y hy (Fin.cast hn i) (Fin.cast hn j)
  rw [h y hy φ hφ, mul_one, mul_inv_cancel] at e
  refine e.trans ?_
  rw [Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  exact if_congr (Fin.cast_injective hn).eq_iff rfl rfl

private theorem red_one {V : TH.HSp D} {n : ℕ} (hn : V.rank = n) {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : Formalism.IndefR.principalLevelFrame.RowPsi V n} (hP : StdFrame hF P) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1)
    (s : SplitPlace D.host.E) {κ : GAf D.host.E n} (hU : κ ∈ Umax D.host.E n) (hT : TrivOutside {s.v} κ)
    (PP : PlE D.host) (hK : NG.OverPl PP s.v → IsPrincipalCongruenceAt s κ) :
    Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
  by_cases ho : NG.OverPl PP s.v
  · have hk := hK ho
    rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE s.w PP (Eq.trans ho s.w_under.symm) with e | e
    · rw [e]
      exact red_of_comp hn hP hB s hU fun y hy φ hφ => map_eq_one s hk hy φ hφ
    · have e' : PP = (GlobalTheory.TypeTame.conjSP s).w := by
        rw [e]
        refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
        exact (GlobalTheory.SplitConjPlace.mem_conj_w s x).symm
      rw [e']
      exact red_of_comp hn hP hB _ hU fun y hy φ hφ => map_eq_one_conj s hU hk hy φ hφ
  · have hS := (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hU)
    refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {PP.under (𝓞 D.host.F)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
    rw [Finset.mem_singleton.1 hu]
    exact GlobalTheory.NonSplitLevel.projV_eq_one hP κ PP (hT _ fun e => ho (congrArg HeightOneSpectrum.asIdeal e))

end UpperTheory.One.M.B

theorem UpperTheory.One.M.B.levSplit :
    UpperTheory.One.M.B.LevSplit := by
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y _ _ _ _ _ i P hP s κ hU hT hK => ?_
  have hlev := z.pins.char.base.lev
  obtain ⟨c, hc⟩ := hlev.βV i
  rw [one_pow] at hc
  have hS := (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hc (P.into κ)).2 ((hP.2 κ).1 hU)
  have hred : ∀ PP, PP ∈ (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0)
        (z.R.toRealDat.levR z.F.lv2 false)).Pg ∨
      PP ∈ (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false)).Q →
      Formalism.L2.DIV.redFn (z.R.toRealDat.βV i) PP (Formalism.IndefR.Lev.finE _ (P.ψ κ)) = 1 := by
    intro PP hPP
    rcases hPP with h | h
    · obtain ⟨k, hk⟩ := (hlev.Pg PP).1 h
      exact UpperTheory.One.M.B.red_one (GlobalTheory.FrameBlockDiagonal.rankV _ i) hP hc s hU hT PP fun ho =>
        hK ⟨PP, ho, k, GlobalTheory.Mem.TypePl.div_over _ hk⟩
    · refine absurd ?_ ((hlev.Q_ram _ PP).2 (Or.inl h))
      have e := (congrArg z.R.toRealDat.toLevCh.xiH ((congrArg Y.tupT Y.tup0).symm.trans (Y.tupT_tup _))).trans hlev.xi_base
      exact e ▸ fun _ _ => rfl
  refine ⟨⟨P.into κ, GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA _ _) hS hred⟩, ?_⟩
  unfold Formalism.IndefR.Lev.levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one _ _ _ hred, Units.val_one]

end
