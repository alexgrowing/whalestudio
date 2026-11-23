import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeightEqAbsInfType

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.BottomWeights

theorem mul_n_eq {D : D7} {N N' : ℕ} (χ : HeckeU D N) (χ' : HeckeU D N') (e e' : ℤ)
    (h : ∀ x, χ.f x ^ e = χ'.f x ^ e') (τ : D.what₂.Tau) : e * χ.n τ = e' * χ'.n τ := by
  have hc := GlobalTheory.SplitWeight.exps_eq_zero (Formalism.L2.Host.embTau D) (GlobalTheory.SplitWeight.embTau_inj D)
    (GlobalTheory.SplitWeight.embTau_ne_conj D) (fun τ => e * χ.n τ - e' * χ'.n τ) (fun a ha => by
      set u := Units.mk0 a ha
      set φ := Formalism.L2.Host.embTau D
      have hne : ∀ τ, φ τ a ≠ 0 := fun τ => by simpa using ha
      have hu : ∀ τ, φ τ a / ((‖φ τ a‖ : ℝ) : ℂ) ≠ 0 := fun τ =>
        div_ne_zero (hne τ) (by exact_mod_cast norm_ne_zero_iff.2 (hne τ))
      have hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
          ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1 := χ.aut u
      have hB : ((χ'.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
          ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ'.n τ) = 1 := χ'.aut u
      have hE := congrArg Units.val (h (Units.map (inc D).toMonoidHom u))
      simp only [Units.val_zpow_eq_zpow_val] at hE
      rw [eq_inv_of_mul_eq_one_left hA, eq_inv_of_mul_eq_one_left hB, inv_zpow, inv_zpow, inv_inj,
        ← Finset.prod_zpow, ← Finset.prod_zpow] at hE
      simp_rw [zpow_sub₀ (hu _), Finset.prod_div_distrib, mul_comm e, mul_comm e', zpow_mul]
      rw [hE]
      exact div_self (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (zpow_ne_zero _ (hu τ))))
  exact sub_eq_zero.1 (congrFun hc τ)

theorem isBottom_n_eq : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T) (i j : Fin D.R.m)
    (𝔪 : Ideal (𝓞 D.host.E)) {δ t0 : ℂ} {Q : ℕ} (P P' : Pair D ⊤ δ t0 Q), IsBottom G t i j 𝔪 P P' → P'.n = P.n := by
  intro D T Lc sc G t i j 𝔪 δ t0 Q P P' h
  funext τ
  have h1 := mul_n_eq P.W.chV' P'.W.chV' P.W.ep' P'.W.ep' (fun x => (h.chars.2 x).trans (h.chars'.2 x).symm) τ
  have h2 := P.wt τ
  have h3 := P'.wt τ
  have h4 : P'.d = P.d := h.rank.2.2.2
  omega

end GlobalTheory.BottomWeights

end
