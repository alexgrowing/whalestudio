import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRegroupCommutativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeProductOfLocalTestFunctionsSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStabiliserLeCentraliserCompactPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRationalPointTestSupportDoubleCosetsFinitStatement

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.ClsOrb

theorem clsSum_eq_mass_mul_twOrb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → clsSum S K' f γ = mass (MonoidHom.id _) (ratFinU E n) (finPt γ) * twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f) := by
  intro E _ _ _ hU n hn S hS lam K' hK' f hf γ hγ
  obtain ⟨hKo, hKc, hlev⟩ := GlobalTheory.T.productOfLocalLevelsUnitary_isOpen_isCompact_isLevel E hU n hn S hS K' hK'
  have hH := GlobalTheory.T.isHecke_productOfLocalTestFunctions_section E hU n hn S hS K' hK' f hf
  have hcomm := GlobalTheory.T.centralizer_regular_rationalPoint_finiteAdelic_comm E n γ hγ
  have hcpt := GlobalTheory.T.level_stabiliser_le_centraliser_compact_part E hU n hn S hS K' hK' γ hγ
  have hsupp := GlobalTheory.T.regularRationalPoint_testSupport_doubleCosets_finite E hU n hn S hS K' hK' f hf γ hγ
  have horb := GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel (finU E n) (MonoidHom.id _) (globLev S (KL n)) hKo hKc
    (fun k hk => hk) (globLev S K') hlev (finPt γ) (globFn S f) hH hcpt hsupp
  set T := twCent (MonoidHom.id (finU E n)) (finPt γ) with hT
  have hCT : cptPart T ≤ T := (Subgroup.closure_le T).2 fun t ht => ht.1
  have hU' : ∀ x : finU E n, T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom ≤ cptPart T ∧
      (T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).relIndex (cptPart T) ≠ 0 := fun x =>
    ⟨le_trans (inf_le_inf_left _ (Subgroup.map_mono hlev.2.1)) (hcpt x).1, (hcpt x).2⟩
  have hinv : ∀ t ∈ T, ∀ k ∈ globLev S K', ∀ x : finU E n,
      globFn S f ((t * x * k)⁻¹ * finPt γ * (t * x * k)) = globFn S f (x⁻¹ * finPt γ * x) := by
    intro t ht k hk x
    have ht' : t * finPt γ = finPt γ * t := ht
    have e1 : t⁻¹ * finPt γ * t = finPt γ := by
      rw [mul_assoc, ← ht', ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : (t * x * k)⁻¹ * finPt γ * (t * x * k) = k⁻¹ * (x⁻¹ * (t⁻¹ * finPt γ * t) * x) * k := by group
    rw [e2, e1, mul_assoc, (hH.2 k⁻¹ (inv_mem hk) _).1, (hH.2 k hk _).2]
  have hreg := GlobalTheory.T.finsum_doubleCoset_regroup_commutative (finU E n) T (ratFinU E n) (cptPart T) (globLev S K')
    (fun x => globFn S f (x⁻¹ * finPt γ * x)) hcomm hCT hU' hinv
  simp only [MonoidHom.id_apply] at horb
  rw [clsSum, horb.1, horb.2, hreg, mass]
  ring

end GlobalTheory.BCT.ClsOrb
