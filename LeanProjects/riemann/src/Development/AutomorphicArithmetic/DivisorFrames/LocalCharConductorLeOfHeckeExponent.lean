import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.localChar_conductor_le_of_heckeExponent :
    ∀ (D : D7) (ν : (AE D)ˣ →* Circle) (νH : Formalism.L2.Host.HChar D.host.E), ChrEq ν νH →
        ∀ (v : Pl D.host.F) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (c : ℕ), GlobalTheory.CMVal.ExpAt νH (splitPrime τ) c →
        GlobalTheory.SplitFlip.CondLE (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) c (chrW ν τ) ∧ (¬ GlobalTheory.LFun.UnrAt ν (splitPrime τ) → 1 ≤ c) := by
  intro D ν νH h v τ c hc
  refine ⟨fun x hx => ?_, fun hn => ?_⟩
  · have h1 : Valued.v (x : Fv D.host.F v) = 1 := (GlobalTheory.FlipMatch.isEquiv_Fv v).eq_one_iff_eq_one.1 hx.1
    have h2 : Valued.v ((x : Fv D.host.F v) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
      refine ((GlobalTheory.FlipMatch.isEquiv_Fv v _ _).1 hx.2).trans_eq ?_
      rw [Units.val_pow_eq_pow_val, map_pow, GlobalTheory.ChrWUnif.valued_unifAt, ← WithZero.exp_nsmul]
      simp
    have h3 := (hc c).2 le_rfl (Units.map (complMap (splitPrime_under τ)).toMonoidHom x)
      ((SplitTie.valued_complMap τ (splitPrime_under τ) _).trans h1) (by
        refine le_of_eq_of_le ?_ h2
        rw [← SplitTie.valued_complMap τ (splitPrime_under τ), RingHom.map_sub, RingHom.map_one]
        rfl)
    rw [← locChar_eq_of_chrEq h] at h3
    exact h3
  · by_contra h0
    apply hn
    rw [unrAt_iff_of_chrEq h]
    intro x hx
    refine (hc 0).2 (by omega) x hx ?_
    rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact Valuation.map_sub_le _ (le_of_eq hx) (le_of_eq (map_one _))
