import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss

theorem isOfFinOrder_of_hasConductor {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) (a : k) : IsOfFinOrder (ψ a) := by
  have hn : ∀ n : ℕ, valuation k (n : k) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (valuation k).map_add_le ih (by simp)

  have hc : ∀ y : k, valuation k y ≤ valuation k (c : k) → ψ y = 1 := (h c).2 le_rfl
  have hc0 : valuation k (c : k) ≠ 0 := by simp
  set γ : (ValueGroupWithZero k)ˣ := Units.mk0 _ hc0 with hγ

  obtain ⟨t, -, ht⟩ := (IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k a)).elim_nhds_subcover
    (fun x => {z | valuation k (z - x) < γ}) (fun x _ => by
      rw [IsValuativeTopology.mem_nhds_iff']
      exact ⟨γ, subset_rfl⟩)
  have hmem : ∀ n : ℕ, ∃ x : t, valuation k ((n : k) * a - x) < γ := by
    intro n
    have : (n : k) * a ∈ {x | valuation k x ≤ valuation k a} := by
      simp only [Set.mem_ofPred_eq, map_mul]
      calc valuation k (n : k) * valuation k a ≤ 1 * valuation k a := by gcongr; exact hn n
        _ = valuation k a := one_mul _
    obtain ⟨x, hx⟩ := Set.mem_iUnion₂.mp (ht this)
    exact ⟨⟨x, hx.1⟩, hx.2⟩
  choose f hf using hmem

  obtain ⟨n, m, hnm, hfnm⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hdiff : valuation k ((n : k) * a - (m : k) * a) ≤ valuation k (c : k) := by
    have h1 := hf n
    have h2 := hf m
    rw [hfnm] at h1
    have : (n : k) * a - (m : k) * a = ((n : k) * a - (f m : k)) - ((m : k) * a - (f m : k)) := by ring
    rw [this]
    refine le_of_lt ?_
    calc valuation k (((n : k) * a - (f m : k)) - ((m : k) * a - (f m : k)))
        ≤ max (valuation k ((n : k) * a - (f m : k))) (valuation k ((m : k) * a - (f m : k))) :=
          (valuation k).map_sub _ _
      _ < γ := max_lt h1 h2
  have hpow : ψ a ^ n = ψ a ^ m := by
    have := hc _ hdiff
    rw [AddChar.map_sub_eq_div, div_eq_one, ← nsmul_eq_mul, ← nsmul_eq_mul,
      AddChar.map_nsmul_eq_pow, AddChar.map_nsmul_eq_pow] at this
    exact this
  rw [isOfFinOrder_iff_pow_eq_one]
  rcases Nat.lt_or_gt_of_ne hnm with hlt | hlt
  · refine ⟨m - n, Nat.sub_pos_of_lt hlt, ?_⟩
    rw [pow_sub _ hlt.le, ← hpow, mul_inv_cancel]
  · refine ⟨n - m, Nat.sub_pos_of_lt hlt, ?_⟩
    rw [pow_sub _ hlt.le, hpow, mul_inv_cancel]

theorem lossLe_psi_neg_phase : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t), ∀ X Y (e : Vars (locGrid ch.G t P)),
    (ch.S.term t Φ β P).datum X Y ≠ 0 →
    moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) (fill one_le_sLen X Y e) ≠ 0 →
    ∀ w : PlL D, LossLe w ((psiAt ch.W P.1 (-phase X e) : Circle) : ℂ) 0 := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS hIs _ hF t Φ β hβ P X Y e hd hm w

  obtain ⟨y, hy⟩ := hF.phases t Φ β hβ P X Y e hd hm

  have hcond : HasConductor (psiAt ch.W P.1) 1 :=
    GlobalTheory.FunObj.Good.hasConductor_psiAt ch.W
      (GlobalTheory.FunObj.Good.badInt_notMem hS.core.lev (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS) (hIs.guard t) P.2)
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_hasConductor hcond (-phase X e))
  have hneg : ((psiAt ch.W P.1 (-phase X e) : Circle) : ℂ) = D.what₂.embLL y⁻¹ := by
    rw [AddChar.map_neg_eq_inv, Circle.coe_inv, map_inv₀, hy]
  refine ⟨y⁻¹, hneg.symm, Or.inr ?_⟩
  have hroot : y⁻¹ ^ n = 1 := by
    apply D.what₂.embLL.injective
    rw [map_pow, ← hneg, ← Circle.coe_pow, hpow, Circle.coe_one, map_one]
  have h0 : (n : ℤ) * Formalism.DivisionValues.vw w y⁻¹ = 0 := by
    unfold Formalism.DivisionValues.vw
    rw [← FractionalIdeal.count_pow, FractionalIdeal.spanSingleton_pow, hroot,
      FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  have hv : Formalism.DivisionValues.vw w y⁻¹ = 0 := (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast hn.ne')
  simp [hv]

end GlobalTheory.UnfoldLoss
