import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
noncomputable section

namespace GlobalTheory.AscFin.IsoDiag

set_option maxHeartbeats 1000000 in

theorem last_diag_int_iso : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (z : Fin V₀.rank → D.host.E) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → (0 < ρ → ∀ a ∈ idAt D (· = v), dW.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v)) → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∀ ξ ∈ p.B₁, ∀ ξ' : Mx D ρ V₀.rank, MxAt (· = v) ξ → mt W (dW.levi t) ⬝ dW.incX V₀ ξ = dW.incX V₀ ξ' → ψ (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (dW.incX V₀ ξ')) = ψ (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (dW.incX V₀ ξ))) → ∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ hstd V V₀ W W₀ ρ dV dW p z LV LV₀ LW LW₀ v hG hS hlast t ht htG hiso i hi
  obtain ⟨eV, heV_int, heV_act, heV_cA, -⟩ := GlobalTheory.FinPl.LastDiag.exists_idemAt D v
  have heV_id : eV ∈ idAt D (· = v) := heV_int.1
  have hcA : ∀ c ∈ idAt D (· = v), cA D c ∈ idAt D (· = v) := fun c hc => by
    rw [← heV_act c hc, map_mul, heV_cA]; exact Ideal.mul_mem_left _ _ heV_id
  have hMx : ∀ c ∈ idAt D (· = v), MxAt (· = v) (dW.incAdj V₀ (c • yZero V₀ ρ z)) :=
    fun c hc k l => by
      rw [GlobalTheory.FinPl.LastDiag.incAdj_smul, Matrix.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ (hcA c hc)
  have hcong := (GlobalTheory.IwaPlace.mem_congGrp_iff W (idAt D (· = v)) _).1 htG
  have hM : MxAt (· = v) (mt W (dW.levi t) - 1) := fun k l => by rw [Matrix.sub_apply]; exact hcong k l
  have htM : t.1 - 1 = dW.pX ⬝ (mt W (dW.levi t) - 1) ⬝ dW.jX := by
    rw [Matrix.mul_sub, Matrix.sub_mul, dW.pX_levi t, Matrix.mul_one, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]
  have ha : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := GlobalTheory.FinPl.LastDiag.mxAt_mul_right (GlobalTheory.FinPl.LastDiag.mxAt_mul_left dW.pX hM) dW.jX i i
    rwa [← htM, Matrix.sub_apply, Matrix.one_apply_eq] at this
  have hρ : 0 < ρ := by omega
  rw [← hlast hρ _ ha]
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hstd V₀ W LV₀ LW hG.sdV₀ hG.sdW (· = v) _ (hMx _ ha)).2 fun u' hu' => ?_
  obtain ⟨ξ, hξdef⟩ : ∃ ξ, ξ = dW.pX ⬝ u' := ⟨_, rfl⟩
  have hξ : MxAt (· = v) ξ := hξdef ▸ GlobalTheory.FinPl.LastDiag.mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu')
  have hu : dV.ext0 W (dW.incX V₀ ξ) ∈ latO V W (LV : Set _) (LW : Set _) (· = v) :=
    hξdef ▸ GlobalTheory.FinPl.LastDiag.wittExtZero_inclusionX_mem_homLatticeCompletion dV dW hG.sdV hG.sdW hG.sdV₀ hG.monoV hG.monoW hu'
  have hB : ξ ∈ p.B₁ := (hS.b ξ hξ).2 hu
  have hact : mt W (dW.levi t) ⬝ dW.incX V₀ ξ = dW.incX V₀ (t.1 ⬝ ξ) := by
    rw [HypDec.incX_apply, HypDec.incX_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, HypDec.levi_jX]
  have hχ := hiso ξ hB (t.1 ⬝ ξ) hξ hact
  rw [GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj, ← Matrix.mul_assoc,
    GlobalTheory.FinPl.LastDiag.yZero_mul_diag _ _ t.1 ht i hi, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj] at hχ
  rw [GlobalTheory.FinPl.LastDiag.symplO_incAdj_eq, ← hξdef, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, sub_mul, one_mul,
    map_sub, neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, hχ, ← AddChar.map_add_eq_mul]
  rw [add_neg_cancel, AddChar.map_zero_eq_one]

end GlobalTheory.AscFin.IsoDiag
