import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastBiExpand
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsModelChg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthAtEmb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsLocalModelFlatMapFourierJacobiStepStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsLocalModelExtendByZeroTopStepStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsTopVertexFrameAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.LastPlace

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

open ValuativeRel in

theorem combAt_renumber {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T' : HSp D} {Y Y' Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] [Fintype Z] [DecidableEq Z] (FS : Frame k S.rank Y') (F : Frame k T'.rank Y) (FX : Frame k T'.rank Z)
    (e : Z ≃ Y) (he : ∀ r z, FX.β r z = F.β r (e z)) (c : WO S T' →₀ ℂ) (Ξ : Matrix Y Y' k → ℂ) :
    p.IsCombAt ψ FS F c Ξ → p.IsCombAt ψ FS FX c (fun x => Ξ (x.submatrix e.symm id)) := by
  rintro ⟨hsupp, hc⟩
  refine ⟨hsupp, fun Tm hTm Φ₀ Φ hΦ₀ hΦ => ?_⟩
  haveI : T2Space (Matrix Y Y' k) := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  have hc1 : Continuous fun y : Matrix Y Y' k => y.submatrix e id :=
    continuous_pi fun a => continuous_pi fun b => (continuous_apply b).comp (continuous_apply (e a))
  have hc2 : Continuous fun x : Matrix Z Y' k => x.submatrix e.symm id :=
    continuous_pi fun a => continuous_pi fun b => (continuous_apply b).comp (continuous_apply (e.symm a))
  let re : SB (Matrix Z Y' k) → SB (Matrix Y Y' k) := fun Ψ =>
    ⟨fun y => Ψ.1 (y.submatrix e id), GlobalTheory.FinPl.Comm.comp_mem_SB Ψ.2 hc1 hc2 (fun y => by ext a b; simp)⟩
  obtain ⟨Tm', hTm', hchg⟩ := GlobalTheory.LocMod.Place.exists_isModel_chg D k p Z Y' S T' FS FX Y Y' FS F ψ Tm hTm
  have hP : F.γ * FX.β = (F.γ * F.β).submatrix id e := by
    ext y z
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, he]
  have hre : ∀ (Ψ : SB (Matrix Z Y' k)), Tm' (re Ψ) = Tm Ψ := fun Ψ => hchg Ψ (re Ψ) fun x => by
    change Ψ.1 x = Ψ.1 ((F.γ * FX.β * x * (FS.γ * FS.β)).submatrix e id)
    have hx : (F.γ * FX.β * x * (FS.γ * FS.β)).submatrix e id = x := by
      rw [hP, F.γβ, FS.γβ, Matrix.mul_one]
      funext a b
      simp [Matrix.mul_apply, Matrix.one_apply]
    rw [hx]
  have h1 : IsOne (re Φ₀) := by
    unfold IsOne
    funext y
    change Φ₀.1 (y.submatrix e id) = _
    rw [hΦ₀]
    by_cases hy : ∀ r q, y r q ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (show y ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from hy), Set.indicator_of_mem (show y.submatrix e id ∈ {x : Matrix Z Y' k | ∀ r q, x r q ∈ 𝒪[k]} from
        fun r q => hy (e r) q)]
    · rw [Set.indicator_of_notMem (show y ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from hy), Set.indicator_of_notMem (show y.submatrix e id ∉ {x : Matrix Z Y' k | ∀ r q, x r q ∈ 𝒪[k]} from
        fun h => hy fun r q => by simpa using h (e.symm r) q)]
  have h2 : (re Φ).1 = Ξ := by
    funext y
    change Φ.1 (y.submatrix e id) = Ξ y
    rw [hΦ]
    simp
  rw [← hre Φ, ← hre Φ₀]
  exact hc Tm' hTm' (re Φ₀) (re Φ) h1 h2

end GlobalTheory.LastPlace

open GlobalTheory.LastPlace in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.FlatPlace.lastStep_eventually : Big fun ch => ChrP ch → ArrP ch → LocP ch → BesP ch → JacP ch → LastP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  classical
  intro hChr hArr hLoc hBes hJac t w hw p hp β r r₀ h hpts M hM φ v f hvf j hj
  have hj0 : j + 2 * 0 + 2 = D.R.m := by omega
  have hm : (locGrid ch.G t w).m = D.R.m := rfl
  have hA1 := topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1)
  have hA0 := topRank_add (G := locGrid ch.G t w) one_le_sLen j
  have hA2 := topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1 + 1)
  have hAm := topRank_add (G := locGrid ch.G t w) one_le_sLen D.R.m
  rw [hm] at hA1 hA0 hA2 hAm
  have h₁ : topRank (locGrid ch.G t w) (j + 1) + 0 = (locGrid ch.G t w).rank (D.R.m, j + 1) := by omega
  have h₂ : topRank (locGrid ch.G t w) j + (0 + 1) = (locGrid ch.G t w).rank (D.R.m, j) := by omega
  have h₃ : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, D.R.m) := by
    rw [show j + 1 + 1 = D.R.m by omega]
  have h₄ : (locGrid ch.G t w).rank (D.R.m, j + 1) = topRank (locGrid ch.G t w) (j + 1) := by omega
  obtain ⟨hchar, hcond, -⟩ := hChr t w hw p hp
  obtain ⟨F₀, T₁, hcore, hT₁, hT₁O, Φ₁, hΦ₁, hT₁Φ⟩ := GlobalTheory.T.lastTwoSteps_localModel_flatMap_fourierJacobiStep ch hChr hArr hLoc hBes hJac t w hw p hp β r r₀ h hpts M hM φ v f
    hvf j hj0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some h₁ h₂
  obtain ⟨T₂, hT₂, hT₂O, Φ₂, hΦ₂, hT₂Φ⟩ := GlobalTheory.T.lastTwoSteps_localModel_extendByZero_topStep ch hChr hArr hJac t w hw p hp β M hM φ v f hvf j hj0 h₃ h₄
  obtain ⟨e, he1, he2, FX, hFX, hFXe⟩ := GlobalTheory.T.lastTwoSteps_topVertex_frame_at_place ch t w hw p hp j hj
  intro I S x Ξ₁ Ξ₂ c₁ c₂ hc
  haveI : T2Space (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) :=
    GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  let Ξ₂' : I → SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m)) ⊕ Unit) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) :=
    fun i => ⟨fun y => (Ξ₂ i).1 (y.submatrix e.symm id),
      GlobalTheory.FinPl.Comm.comp_mem_SB (Ξ₂ i).2 (p := fun y => y.submatrix e.symm id) (s := fun y => y.submatrix e id)
        (continuous_pi fun a => continuous_pi fun b => (continuous_apply b).comp (continuous_apply (e.symm a)))
        (continuous_pi fun a => continuous_pi fun b => (continuous_apply b).comp (continuous_apply (e a)))
        (fun y => by ext a b; simp)⟩
  have hΞ₂' : ∀ i y, (Ξ₂' i).1 y = (Ξ₂ i).1 (y.submatrix e.symm id) := fun _ _ => rfl
  let O₁ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)) :=
    ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  let O₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) :=
    ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  have hO₁ : IsOne O₁ := rfl
  have hO₂ : IsOne O₂ := rfl
  have hL : (pLine D).rank = 1 := rfl
  have ha : ((p.xi ^ 0)⁻¹ : Kw w) ≠ 0 := by simp
  have hz : (lastTau (D := D)).map p.pr *ᵥ (fun _ => (1 : Kw w)) =
      (-(p.xi * (p.xi ^ 0)⁻¹)) • fun i => p.pr ((besAt ch.G hM j 0 hj0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some).ζ i) := by
    funext i
    simp [lastTau, mulVec, dotProduct, besAt, Place.xi, Place.pr, hL]
    exact (mul_one _).symm
  have key := fun (S' : Finset I) (Ψ₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w))) =>
    GlobalTheory.LastSeeSawGen.lastBi_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ ch.W.ψ_std (psiAt ch.W w) hchar hcond 0
      (besAt ch.G hM j 0 hj0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (ch.G.V (.top (j + 1))) (ch.G.V (.top (j + 1 + 1)))
      (ch.G.V (.grid D.R.m D.R.m)) (pLine D) (topOrthAt ch.G (show D.R.m = j + 1 + 1 by omega)) lastTau hL
      GlobalTheory.RowChain.LastSeeSawStep.lastTau_gram ((p.xi ^ 0)⁻¹) (fun _ => 1) ha hz _ _ _ (frTop ch.S.toGridChoice t w j (by omega)) F₀
      (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w D.R.m le_rfl) FX hcore hFX T₁ T₂ hT₁ hT₂ Φ₁ Ψ₂ O₁ O₂
      hO₁ hO₂ I S' x Ξ₁ Ξ₂' c₁ c₂
  have hc' : ∀ i ∈ S, p.IsCombAt ch.W.ψ (frTop ch.S.toGridChoice t w j (by omega)) (frTop ch.S.toGridChoice t w (j + 1) (by omega))
      (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) FX (c₂ i) (Ξ₂' i).1 :=
    fun i hi => ⟨(hc i hi).1, combAt_renumber p ch.W.ψ _ _ FX e hFXe _ _ (hc i hi).2⟩
  have hsymm : ∀ a : Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)),
      e.symm (Fin.castLE (by omega) a) = Sum.inl (Fin.cast h₃ a) := fun a => by
    rw [Equiv.symm_apply_eq]; ext; rw [he1]; rfl
  have hsymm' : e.symm (topLast (locGrid ch.G t w) (j + 1 + 1)) = Sum.inr () := by
    rw [Equiv.symm_apply_eq]; ext; rw [he2]; rfl
  unfold facAt locA conAt
  rw [dif_pos hj0, dif_pos hj0]
  unfold lastDat
  rw [← hT₁O O₁ hO₁, ← hT₂O O₂ hO₂]
  refine ⟨fun hrel => ?_, fun hexp => ?_⟩
  · have e1 := key S 0 hc' (fun y y' => by
      rw [Submodule.coe_zero, Pi.zero_apply, zero_mul]
      exact (hrel y (y'.submatrix e.symm id)).symm)
    have e2 := key ∅ 0 (fun i hi => absurd hi (Finset.notMem_empty i)) (fun y y' => by
      rw [Submodule.coe_zero, Pi.zero_apply, zero_mul, Finset.sum_empty])
    rw [Finset.sum_empty] at e2
    exact e1.symm.trans e2
  · rw [← hT₁Φ, ← hT₂Φ]
    refine key S Φ₂ hc' fun y y' => ?_
    rw [hΦ₂, hΦ₁]
    refine Eq.trans ?_ (hexp (y, y'.submatrix e.symm id))
    rw [dif_pos (show j + 2 * 0 + 2 = (locGrid ch.G t w).m from hj0)]
    have hy : y'.toRows₁.submatrix (Fin.cast h₃) (Fin.cast h₄) = (y'.submatrix e.symm id).submatrix
        (Fin.castLE (show (locGrid ch.G t w).rank ((locGrid ch.G t w).m, j + 1 + 1) ≤ _ by simp only [hm]; omega))
        (Fin.cast (show (locGrid ch.G t w).rank ((locGrid ch.G t w).m, j + 1) = _ by simp only [hm]; omega)) := by
      funext a b
      simp only [Matrix.submatrix_apply, Matrix.toRows₁_apply, id]
      exact congrArg (fun z => y' z (Fin.cast h₄ b)) (hsymm a).symm
    have hy' : (y'.submatrix e.symm id) (topLast (locGrid ch.G t w) (j + 1 + 1)) = y' (Sum.inr ()) := by
      funext b
      simp only [Matrix.submatrix_apply, id]
      rw [hsymm']
    simp only
    rw [hy, hy']
    rfl

end
