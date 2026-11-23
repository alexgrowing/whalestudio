import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IoUniq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
noncomputable section

namespace GlobalTheory.Mem.R3.DTheta.StepLevLift

theorem stepLev_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (b : Bool) (t : T) (k : ℕ), k + 1 < D.R.m → ∀ κ ∈ levS (Yc D k) (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)), ∃ κ' ∈ levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)), R.ωY t k (κ, κ') (R.vY t k) = (levChi (Yc D k) (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)) κ * (levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ')⁻¹) • R.vY t k := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk κ hκ
  have hL := hP.char.base.lev
  have hk' : k < D.R.m := Nat.lt_of_succ_lt hk
  obtain ⟨hκ1, hκ2⟩ := hκ
  set g0 : G0 R.Pg D.R.r := rTup (R.βY k) (R.datYt t k R.triv) (finE (Yc D k) κ) with hg0
  have hl : IsLevelLift (Yc D k) (R.βY k) (R.datYt t k R.triv) g0 κ := ⟨hκ1, hκ2.1, rfl⟩
  obtain ⟨κ', hl'⟩ := GlobalTheory.ChainLiftEquiv.liftsExist_chain R.toRealDat hL t (k + 1) hk g0
  have hlaw := GlobalTheory.StepVecLaw.stepVec_lifts R.toRealDat hL hP.char.base.models.inf hP.char.base.chain.ωY
    hP.char.base.chain.vY t k hk g0 κ κ' hl hl'
  have hmem : rTup (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) (finE (Yc D (k + 1)) κ') ∈
      (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.H := by
    rw [hl'.2.2]; exact hκ2.2
  refine ⟨κ', ⟨hl'.1, hl'.2.1, hmem⟩, ?_⟩
  have e1 := levFn_withP (V := Yc D k) (β := R.βY k) (L := R.datYt t k (R.toRealDat.levR F.lv2 b))
    (R.datYt t k (R.toRealDat.levR F.lv2 b)).P (finE (Yc D k) κ)
  have e2 := levFn_withP (V := Yc D (k + 1)) (β := R.βY (k + 1)) (L := R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))
    (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P (finE (Yc D (k + 1)) κ')
  have x1 : ext1 (R.datYt t k (R.toRealDat.levR F.lv2 b)).P.H (R.datYt t k (R.toRealDat.levR F.lv2 b)).P.chi
      (rTup (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)) (finE (Yc D k) κ)) =
      ext1 (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.H (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.chi
      (rTup (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (finE (Yc D (k + 1)) κ')) := by
    have : rTup (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (finE (Yc D (k + 1)) κ') = g0 := hl'.2.2
    rw [this]
    rfl
  unfold levChi
  change R.ωY t k (κ, κ') (R.vY t k) = (((Formalism.L2.DIV.levFn (R.βY k) (withP (R.datYt t k (R.toRealDat.levR F.lv2 b)) (R.datYt t k (R.toRealDat.levR F.lv2 b)).P) (finE (Yc D k) κ) : ℂˣ) : ℂ) * ((Formalism.L2.DIV.levFn (R.βY (k + 1)) (withP (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P) (finE (Yc D (k + 1)) κ') : ℂˣ) : ℂ)⁻¹) • R.vY t k
  rw [e1, e2, x1]
  unfold levChi at hlaw
  change ((Formalism.L2.DIV.levFn (R.βY k) (flagL (R.datYt t k (R.toRealDat.levR F.lv2 b))) (finE (Yc D k) κ) : ℂˣ) : ℂ)⁻¹ • R.ωY t k (κ, κ') (R.vY t k) = ((Formalism.L2.DIV.levFn (R.βY (k + 1)) (flagL (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) (finE (Yc D (k + 1)) κ') : ℂˣ) : ℂ)⁻¹ • R.vY t k at hlaw
  set c := ext1 (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.H (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.chi
      (rTup (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (finE (Yc D (k + 1)) κ'))
  set a := Formalism.L2.DIV.levFn (R.βY k) (flagL (R.datYt t k (R.toRealDat.levR F.lv2 b))) (finE (Yc D k) κ)
  set a' := Formalism.L2.DIV.levFn (R.βY (k + 1)) (flagL (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) (finE (Yc D (k + 1)) κ')
  have ha : ((a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hc : ((c : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h3 : R.ωY t k (κ, κ') (R.vY t k) = (((a : ℂˣ) : ℂ) * ((a' : ℂˣ) : ℂ)⁻¹) • R.vY t k := by
    rw [mul_smul, ← hlaw, smul_inv_smul₀ ha]
  rw [h3, Units.val_mul, Units.val_mul]
  congr 1
  field_simp

end GlobalTheory.Mem.R3.DTheta.StepLevLift

end
